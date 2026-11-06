-- |
-- Module      : Network.TLS.Handshake.Reassembly
-- License     : BSD-style
-- Stability   : experimental
-- Portability : unknown
--
-- DTLS handshake message reassembly and in-order delivery
-- (RFC 6347 sections 4.2.2 and 4.2.3).
--
-- The record layer of DTLS gives no ordering guarantees, so handshake
-- fragments may arrive in any order, may be duplicated (retransmissions)
-- and may overlap (retransmissions with a different PMTU estimate).
-- Fragments are buffered per message_seq until the whole message is
-- covered; complete messages are then delivered strictly in message_seq
-- order, messages which are ahead of sequence being queued.
--
-- Problems with individual fragments are never fatal: such fragments are
-- discarded (the reason is reported back for logging) and the peer's
-- retransmission is expected to repair the flight. Fragments of messages
-- which have already been processed are reported as stale: they show that
-- the peer is retransmitting, i.e. that our response may have been lost.
--
module Network.TLS.Handshake.Reassembly
    ( HandshakeFragment(..)
    , FragmentOutcome(..)
    , HandshakeReassembly
    , newHandshakeReassembly
    , insertFragment
    , insertFragments
    , maxPendingMessages
    , maxBufferedBytes
    ) where

import Network.TLS.Struct
import Network.TLS.Imports

import qualified Data.ByteString as B
import qualified Data.Map.Strict as M

-- | One handshake fragment, as read from a DTLS record.
data HandshakeFragment = HandshakeFragment
    { hfType       :: !HandshakeType
    , hfLength     :: !Int    -- ^ length of the entire message
    , hfMessageSeq :: !Word16
    , hfOffset     :: !Int    -- ^ fragment offset within the message
    , hfData       :: !ByteString
    } deriving (Show, Eq)

-- | What became of a fragment fed to the reassembly.
data FragmentOutcome
    = FragmentProgress         -- ^ new data from the peer's current or next flight
    | FragmentStale String     -- ^ part of a message already processed
    | FragmentDiscarded String -- ^ unusable (reason given)
    deriving (Show, Eq)

data PartialMessage = PartialMessage
    { pmType   :: !HandshakeType
    , pmLength :: !Int
    , pmPieces :: ![(Int, ByteString)] -- ^ received pieces, sorted by offset
    }

data HandshakeReassembly = HandshakeReassembly
    { hrNextSeq  :: !Word16 -- ^ message_seq of the next message to deliver
    , hrSynced   :: !Bool   -- ^ whether any message has been delivered in order yet
    , hrPartial  :: !(M.Map Word16 PartialMessage)
    , hrComplete :: !(M.Map Word16 (HandshakeType, ByteString)) -- ^ complete, ahead of sequence
    }

-- | Upper bound on the number of messages (incomplete or queued) buffered at once.
maxPendingMessages :: Int
maxPendingMessages = 32

-- | Upper bound on the number of handshake bytes buffered at once.
maxBufferedBytes :: Int
maxBufferedBytes = 256 * 1024

-- | Create a reassembly state expecting the given message_seq next.
newHandshakeReassembly :: Word16 -> HandshakeReassembly
newHandshakeReassembly next = HandshakeReassembly next False M.empty M.empty

-- | Feed several fragments (e.g. all fragments of one record).
insertFragments :: [HandshakeFragment]
                -> HandshakeReassembly
                -> (HandshakeReassembly, ([(HandshakeType, Word16, ByteString)], [FragmentOutcome]))
insertFragments frags st0 = go st0 [] [] frags
  where go st msgs outcomes []     = (st, (concat (reverse msgs), reverse outcomes))
        go st msgs outcomes (f:fs) =
            let (st', ms, o) = insertFragment f st
            in go st' (ms:msgs) (o:outcomes) fs

-- | Feed one fragment. Returns the new state, the messages which are now
-- ready to be processed (type, message_seq, body), in order, and what
-- became of the fragment.
insertFragment :: HandshakeFragment
               -> HandshakeReassembly
               -> (HandshakeReassembly, [(HandshakeType, Word16, ByteString)], FragmentOutcome)
insertFragment f st
    | hfOffset f + B.length (hfData f) > hfLength f =
        discard "fragment exceeds declared message length"
    | stale && not (isStatelessHelloType ty) =
        (st, [], FragmentStale $ "fragment of an already processed message: " ++ describe f)
    | M.member msgSeq (hrComplete st) =
        discard "fragment of an already reassembled message"
    | otherwise =
        case M.lookup msgSeq (hrPartial st) of
            Nothing
                | M.size (hrPartial st) + M.size (hrComplete st) >= maxPendingMessages ->
                    discard "too many handshake messages buffered"
                | otherwise -> addPiece (PartialMessage ty (hfLength f) [])
            Just pm
                | pmType pm /= ty || pmLength pm /= hfLength f ->
                    discard "fragment inconsistent with previously received fragments"
                | otherwise -> addPiece pm
  where
    ty     = hfType f
    msgSeq = hfMessageSeq f
    off    = hfOffset f
    end    = off + B.length (hfData f)

    -- earlier ClientHello fragments are still buffered, in case it turns out
    -- to be a ClientHello without cookie
    stale  = msgSeq < hrNextSeq st

    discard reason
        | stale     = (st, [], FragmentStale $ reason ++ ": " ++ describe f)
        | otherwise = (st, [], FragmentDiscarded $ reason ++ ": " ++ describe f)

    addPiece pm
        | isComplete pm' =
            let body = assemble pm'
                st'  = st { hrPartial = M.delete msgSeq (hrPartial st) }
            in onComplete st' body
        | covered = discard "duplicate fragment"
        | bufferedBytes st + B.length (hfData f) > maxBufferedBytes =
            discard "too many handshake bytes buffered"
        | stale     = (st { hrPartial = M.insert msgSeq pm' (hrPartial st) }, []
                      , FragmentStale $ "fragment of an earlier ClientHello: " ++ describe f)
        | otherwise = (st { hrPartial = M.insert msgSeq pm' (hrPartial st) }, [], FragmentProgress)
      where covered = coveredUpTo off (pmPieces pm) >= end
            pm' | covered   = pm
                | otherwise = pm { pmPieces = insertBy (comparing fst) (off, hfData f) (pmPieces pm) }

    onComplete st' body
        -- ClientHello without cookie and HelloVerifyRequest are processed
        -- out of sequence: they belong to the stateless cookie exchange
        -- (RFC 6347 4.2.1) and may be retransmitted with any message_seq.
        | isStatelessHello ty body = (st', [(ty, msgSeq, body)], FragmentProgress)
        | stale                    = (st', [], FragmentStale $ "already processed message: " ++ describe f)
        | otherwise =
            let (st'', msgs) = drain st' { hrComplete = M.insert msgSeq (ty, body) (hrComplete st') }
            in (st'', msgs, FragmentProgress)

-- | Deliver queued complete messages which are next in sequence.
drain :: HandshakeReassembly -> (HandshakeReassembly, [(HandshakeType, Word16, ByteString)])
drain st0 = let (st, msgs) = go (sync st0) [] in (prune st, reverse msgs)
  where
    -- Until the first message is delivered we don't know the peer's
    -- starting message_seq for sure, so (as before reassembly was
    -- order-independent) allow a gap in front of a hello message.
    sync st
        | hrSynced st = st
        | otherwise = case M.lookupMin (hrComplete st) of
            Just (s, (t, _)) | s > hrNextSeq st && t `elem` [HandshakeType_ClientHello, HandshakeType_ServerHello]
                -> st { hrNextSeq = s }
            _ -> st
    go st acc = case M.lookup (hrNextSeq st) (hrComplete st) of
        Nothing     -> (st, acc)
        Just (t, b) -> go st { hrNextSeq  = hrNextSeq st + 1
                             , hrSynced   = True
                             , hrComplete = M.delete (hrNextSeq st) (hrComplete st)
                             } ((t, hrNextSeq st, b) : acc)
    prune st = st { hrPartial  = M.filterWithKey (\s pm -> s >= hrNextSeq st || isStatelessHelloType (pmType pm)) (hrPartial st)
                  , hrComplete = M.filterWithKey (\s _ -> s >= hrNextSeq st) (hrComplete st)
                  }

isStatelessHelloType :: HandshakeType -> Bool
isStatelessHelloType t = t == HandshakeType_ClientHello || t == HandshakeType_HelloVerifyRequest

isStatelessHello :: HandshakeType -> ByteString -> Bool
isStatelessHello HandshakeType_HelloVerifyRequest _ = True
isStatelessHello HandshakeType_ClientHello body =
    -- client_version(2) random(32) session_id<0..32> cookie<0..2^8-1> ...
    let sidLen   = fromIntegral (B.index body 34)
        cookieIx = 35 + sidLen
    in B.length body > 34 && B.length body > cookieIx && B.index body cookieIx == 0
isStatelessHello _ _ = False

-- | End of the contiguous range starting at the given offset which is
-- covered by the (sorted) pieces.
coveredUpTo :: Int -> [(Int, ByteString)] -> Int
coveredUpTo = foldl' step
  where step c (o, b) | o <= c    = max c (o + B.length b)
                      | otherwise = c

isComplete :: PartialMessage -> Bool
isComplete pm = coveredUpTo 0 (pmPieces pm) >= pmLength pm

assemble :: PartialMessage -> ByteString
assemble pm = B.take (pmLength pm) $ B.concat $ reverse $ snd $ foldl' step (0, []) (pmPieces pm)
  where step (c, acc) (o, b)
            | o + B.length b > c = (o + B.length b, B.drop (c - o) b : acc)
            | otherwise          = (c, acc)

bufferedBytes :: HandshakeReassembly -> Int
bufferedBytes st = sum (map pieceBytes $ M.elems $ hrPartial st)
                 + sum (map (B.length . snd) $ M.elems $ hrComplete st)
  where pieceBytes = sum . map (B.length . snd) . pmPieces

describe :: HandshakeFragment -> String
describe f = show (hfType f) ++ " message_seq=" ++ show (hfMessageSeq f)
          ++ " offset=" ++ show (hfOffset f) ++ " fragment_length=" ++ show (B.length $ hfData f)
          ++ " length=" ++ show (hfLength f)
