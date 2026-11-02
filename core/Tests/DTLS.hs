{-# LANGUAGE OverloadedStrings #-}
-- | DTLS specific tests: handshake fragment reassembly, record replay
-- window, and complete handshakes over a datagram link which reorders
-- and duplicates datagrams.
module DTLS
    ( tests_dtls
    ) where

import Test.Tasty
import Test.Tasty.QuickCheck

import Network.TLS
import Network.TLS.Extra.Cipher (ciphersuite_default_DTLS)
import Network.TLS.Internal
    ( HandshakeType(..)
    , HandshakeFragment(..)
    , newHandshakeReassembly
    , insertFragment
    , insertFragments
    , newReplayWindow
    , isReplayed
    , markReceived
    )

import Connection (arbitraryRSACredentialWithUsage)

import Control.Concurrent.Async
import Control.Concurrent.Chan
import Control.Monad
import qualified Control.Exception as E
import Data.Default.Class
import Data.List (foldl', nub, sort)
import Data.Word
import Data.X509 (ExtKeyUsageFlag(..))
import qualified Data.ByteString as B
import System.Timeout

tests_dtls :: TestTree
tests_dtls = testGroup "DTLS"
    [ testGroup "Handshake reassembly"
        [ testProperty "Fragments in any order" prop_reassembly_any_order
        , testProperty "Messages in any order" prop_reassembly_messages_in_order
        , testProperty "Reversed ClientHello fragments" prop_reassembly_reversed_client_hello
        , testProperty "Stale and inconsistent fragments" prop_reassembly_discards
        , testProperty "Stateless ClientHello" prop_reassembly_stateless_hello
        ]
    , testGroup "Replay window"
        [ testProperty "No record accepted twice" prop_replay_unique
        , testProperty "Reordered records accepted" prop_replay_reordered
        ]
    , testGroup "Handshake over datagrams"
        [ testProperty "In order" $ prop_handshake_dtls InOrder
        , testProperty "Reordered handshake datagrams" $ prop_handshake_dtls SwapHandshakePairs
        , testProperty "Duplicated datagrams" $ prop_handshake_dtls Duplicate
        ]
    ]

----------------------------------------------------------------
-- reassembly

-- | Split [0, len) into pieces, add some arbitrary (overlapping) ranges
-- and duplicates, then shuffle.
arbitraryFragments :: HandshakeType -> Word16 -> B.ByteString -> Gen [HandshakeFragment]
arbitraryFragments ty msgSeq body = do
    let len = B.length body
    cuts <- sort . nub <$> listOf (choose (1, max 1 (len - 1)))
    let bounds = nub $ [0] ++ filter (< len) cuts ++ [len]
        tiling | len == 0  = [(0, 0)]
               | otherwise = zip bounds (tail bounds)
    extra <- listOf $ do
        o <- choose (0, len)
        e <- choose (o, len)
        return (o, e)
    dups <- sublistOf tiling
    shuffle [ HandshakeFragment ty len msgSeq o (B.take (e - o) $ B.drop o body)
            | (o, e) <- tiling ++ take 10 extra ++ dups ]

arbitraryBody :: Gen B.ByteString
arbitraryBody = do
    len <- oneof [choose (0, 3), choose (0, 4000)]
    B.pack <$> vectorOf len arbitrary

prop_reassembly_any_order :: Property
prop_reassembly_any_order = property $ do
    body <- arbitraryBody
    msgSeq <- arbitrary
    frags <- arbitraryFragments HandshakeType_Certificate msgSeq body
    let (_, (msgs, _)) = insertFragments frags (newHandshakeReassembly msgSeq)
    return $ msgs === [(HandshakeType_Certificate, msgSeq, body)]

prop_reassembly_messages_in_order :: Property
prop_reassembly_messages_in_order = property $ do
    n <- choose (1, 6)
    first <- choose (0, 1000)
    bodies <- vectorOf n arbitraryBody
    let types = cycle [HandshakeType_Certificate, HandshakeType_ServerKeyXchg, HandshakeType_ServerHelloDone]
        expected = zip3 types [first ..] bodies
    frags <- concat <$> mapM (\(t, s, b) -> arbitraryFragments t s b) expected
    frags' <- shuffle frags
    let (_, (msgs, _)) = insertFragments frags' (newHandshakeReassembly first)
    return $ msgs === expected

-- | ClientHello body with the given cookie, padded to the given length.
clientHelloBody :: B.ByteString -> Int -> B.ByteString
clientHelloBody cookie len =
    let prefix = B.concat [ "\xfe\xfd", B.replicate 32 0x11, "\x00"
                          , B.singleton (fromIntegral $ B.length cookie), cookie ]
    in prefix `B.append` B.replicate (len - B.length prefix) 0x22

-- The case from the field: a 1445 bytes ClientHello in two records, the
-- second one arriving first.
prop_reassembly_reversed_client_hello :: Property
prop_reassembly_reversed_client_hello = once $
    let body = clientHelloBody (B.replicate 20 0x33) 1445
        frag o e = HandshakeFragment HandshakeType_ClientHello 1445 1 o (B.take (e - o) $ B.drop o body)
        st0 = newHandshakeReassembly 1
        (st1, msgs1, d1) = insertFragment (frag 1175 1445) st0
        (_,   msgs2, d2) = insertFragment (frag 0 1175) st1
    in (msgs1, d1, msgs2, d2) === ([], Nothing, [(HandshakeType_ClientHello, 1, body)], Nothing)

prop_reassembly_discards :: Property
prop_reassembly_discards = once $
    let body = B.replicate 100 0x44
        frag ty len s o e = HandshakeFragment ty len s o (B.take (e - o) $ B.drop o body)
        st0 = newHandshakeReassembly 5
        -- stale message
        (st1, m1, d1) = insertFragment (frag HandshakeType_Certificate 100 4 0 100) st0
        -- beyond the declared length
        (st2, m2, d2) = insertFragment (frag HandshakeType_Certificate 50 5 40 100) st1
        -- first piece of message 5
        (st3, m3, d3) = insertFragment (frag HandshakeType_Certificate 100 5 0 60) st2
        -- inconsistent type for message 5
        (st4, m4, d4) = insertFragment (frag HandshakeType_Finished 100 5 60 100) st3
        -- duplicate
        (st5, m5, d5) = insertFragment (frag HandshakeType_Certificate 100 5 10 50) st4
        -- completing piece
        (_,   m6, d6) = insertFragment (frag HandshakeType_Certificate 100 5 50 100) st5
        isJust' = maybe False (const True)
    in conjoin [ null (m1 ++ m2 ++ m3 ++ m4 ++ m5) === True
               , map isJust' [d1, d2, d3, d4, d5, d6] === [True, True, False, True, True, False]
               , m6 === [(HandshakeType_Certificate, 5, body)]
               ]

-- A ClientHello without cookie is processed whatever its message_seq,
-- and doesn't affect the sequence of the following messages.
prop_reassembly_stateless_hello :: Property
prop_reassembly_stateless_hello = once $
    let hello = clientHelloBody "" 200
        whole ty s b = HandshakeFragment ty (B.length b) s 0 b
        st0 = newHandshakeReassembly 1
        (st1, m1, _) = insertFragment (whole HandshakeType_ClientHello 0 hello) st0
        (st2, m2, _) = insertFragment (whole HandshakeType_ClientHello 0 hello) st1
        cookied = clientHelloBody "cookie" 200
        (_,   m3, _) = insertFragment (whole HandshakeType_ClientHello 1 cookied) st2
    in (m1, m2, m3) === ( [(HandshakeType_ClientHello, 0, hello)]
                        , [(HandshakeType_ClientHello, 0, hello)]
                        , [(HandshakeType_ClientHello, 1, cookied)] )

----------------------------------------------------------------
-- replay window

acceptRecords :: [Word64] -> [Word64]
acceptRecords = reverse . snd . foldl' step (newReplayWindow, [])
  where step (w, acc) sn
            | isReplayed sn w = (w, acc)
            | otherwise       = (markReceived sn w, sn : acc)

prop_replay_unique :: [Word64] -> Property
prop_replay_unique sns = let acc = acceptRecords sns in length acc === length (nub acc)

-- Sequence numbers shuffled within blocks of 32 (so never displaced by
-- more than the window), with duplicates: each accepted exactly once.
prop_replay_reordered :: Property
prop_replay_reordered = property $ do
    epoch <- choose (0, 3) :: Gen Word64
    n <- choose (1, 300)
    let sns = map (+ (epoch * 0x1000000000000)) [0 .. n - 1]
    blocks <- forM (chunksOf 32 sns) $ \blk -> do
        dups <- sublistOf blk
        shuffle (blk ++ dups)
    return $ sort (acceptRecords $ concat blocks) === sns
  where chunksOf k xs = case splitAt k xs of
            (a, []) -> [a]
            (a, b)  -> a : chunksOf k b

----------------------------------------------------------------
-- complete handshakes

data LinkMode = InOrder | SwapHandshakePairs | Duplicate
    deriving (Show, Eq)

-- | One direction of a datagram link.
relay :: LinkMode -> Chan B.ByteString -> Chan B.ByteString -> IO ()
relay InOrder inp out = forever $ readChan inp >>= writeChan out
relay Duplicate inp out = forever $ do
    d <- readChan inp
    writeChan out d
    writeChan out d
-- Datagrams carrying handshake records which are sent back to back are
-- delivered in reverse order: this splits fragmented messages and flights
-- the way some VPNs and multi-queue paths do.
relay SwapHandshakePairs inp out = forever $ do
    a <- readChan inp
    if not (isHandshake a)
        then writeChan out a
        else do
            mb <- timeout 50000 (readChan inp)
            case mb of
                Nothing -> writeChan out a
                Just b | isHandshake b -> writeChan out b >> writeChan out a
                       | otherwise     -> writeChan out a >> writeChan out b
  where isHandshake d = not (B.null d) && B.head d == 22

prop_handshake_dtls :: LinkMode -> Property
prop_handshake_dtls mode = once $ ioProperty $ do
    cred <- generate $ arbitraryRSACredentialWithUsage [KeyUsage_digitalSignature, KeyUsage_keyEncipherment]
    c2s <- (,) <$> newChan <*> newChan
    s2c <- (,) <$> newChan <*> newChan
    withAsync (relay mode (fst c2s) (snd c2s)) $ \_ ->
        withAsync (relay mode (fst s2c) (snd s2c)) $ \_ -> do
            cRecv <- makeStreamRecvFromDgram [] (readChan $ snd s2c)
            sRecv <- makeStreamRecvFromDgram [] (readChan $ snd c2s)
            let backend send = Backend (return ()) (return ()) send
                supported = def { supportedVersions = [DTLS12]
                                , supportedCiphers  = ciphersuite_default_DTLS }
                sParams = def { serverSupported = supported
                              , serverShared = def { sharedCredentials = Credentials [cred] } }
                -- a large ALPN list makes the ClientHello span two records
                alpn = [ B.replicate 200 (0x61 + i) | i <- [0 .. 6] ]
                cParams = (defaultParamsClient "" B.empty)
                    { clientSupported = supported
                    , clientHooks = def { onSuggestALPN = return $ Just alpn }
                    , clientShared = def { sharedValidationCache = ValidationCache
                                            { cacheAdd = \_ _ _ -> return ()
                                            , cacheQuery = \_ _ _ -> return ValidationCachePass } }
                    }
            cCtx <- contextNew (backend (writeChan $ fst c2s) cRecv) cParams
            sCtx <- contextNew (backend (writeChan $ fst s2c) sRecv) sParams
            let client = handshake cCtx >> sendData cCtx "ping" >> recvData cCtx
                server = handshake sCtx >> recvData sCtx >>= \d -> sendData sCtx "pong" >> return d
            r <- timeout 20000000 $ E.try $ concurrently client server
            return $ case r of
                Nothing                                 -> counterexample "timeout" False
                Just (Left e)                           -> counterexample (show (e :: E.SomeException)) False
                Just (Right (fromServer, fromClient))   -> (fromServer, fromClient) === ("pong", "ping")
