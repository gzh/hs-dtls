-- |
-- Module      : Network.TLS.Receiving
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : unknown
--
-- the Receiving module contains calls related to unmarshalling packets according
-- to the TLS state
--
{-# LANGUAGE FlexibleContexts #-}

module Network.TLS.Receiving
    ( processPacket
    ) where

import Control.Monad.State.Strict
import Control.Concurrent.MVar

import Network.TLS.Context.Internal
import Network.TLS.Struct
import Network.TLS.ErrT
import Network.TLS.Record
import Network.TLS.Packet
import Network.TLS.Wire
import Network.TLS.State
import Network.TLS.Handshake.State
import Network.TLS.Cipher
import Network.TLS.Util
import Network.TLS.Imports

import Network.TLS.Handshake.Reassembly (insertFragments)
import Network.TLS.Hooks
import Data.IORef

processPacket :: Context -> Record Plaintext -> IO (Either TLSError Packet)

processPacket _ (Record ProtocolType_AppData _ _ fragment) = return $ Right $ AppData $ fragmentGetBytes fragment

processPacket _ (Record ProtocolType_Alert _ _ fragment) = return (Alert `fmapEither` decodeAlerts (fragmentGetBytes fragment))

processPacket ctx (Record ProtocolType_ChangeCipherSpec _ _ fragment) =
    case decodeChangeCipherSpec $ fragmentGetBytes fragment of
        Left err -> return $ Left err
        Right _  -> do switchRxEncryption ctx
                       return $ Right ChangeCipherSpec

processPacket ctx (Record ProtocolType_Handshake ver _ fragment)
    | isDTLS ver = processHandshakeDTLS ctx ver fragment

processPacket ctx (Record ProtocolType_Handshake ver _ fragment) = do
    keyxchg <- getHState ctx >>= \hs -> return (hs >>= hstPendingCipher >>= Just . cipherKeyExchange)
    usingState ctx $ do
        let currentParams = CurrentParams
                            { cParamsVersion     = ver
                            , cParamsKeyXchgType = keyxchg
                            }
        -- get back the optional continuation, and parse as many handshake record as possible.
        mCont <- gets stHandshakeRecordCont
        modify (\st -> st { stHandshakeRecordCont = Nothing })
        hss   <- parseMany currentParams mCont (fragmentGetBytes fragment)
        return $ Handshake hss
  where parseMany currentParams mCont bs =
            case fromMaybe decodeHandshakeRecord mCont bs of
                GotError err                -> throwError err
                GotPartial cont             -> modify (\st -> st { stHandshakeRecordCont = Just cont }) >> return []
                GotSuccess (ty,decorate,content) ->
                    either throwError (return . (:[]) . decorate) $ decodeHandshake currentParams ty content
                GotSuccessRemaining (ty,decorate,content) left ->
                    case decodeHandshake currentParams ty content of
                        Left err -> throwError err
                        Right hh -> (decorate hh:) <$> parseMany currentParams Nothing left

processPacket _ (Record ProtocolType_DeprecatedHandshake _ _ fragment) =
    case decodeDeprecatedHandshake $ fragmentGetBytes fragment of
        Left err -> return $ Left err
        Right hs -> return $ Right $ Handshake [hs]

switchRxEncryption :: Context -> IO ()
switchRxEncryption ctx =
    usingHState ctx (gets hstPendingRxState) >>= \mrx ->
    liftIO $ modifyMVar_ (ctxRxState ctx) (\rxprev -> return $ let rx = fromJust "rx-state" mrx
                                                                   epoch = stSeqNumber rxprev
                                                               in rx { stSeqNumber = nextEpoch epoch })

-- | DTLS handshake records carry fragments which may arrive in any order,
-- duplicated or overlapping. They are handed to the reassembly buffer,
-- which returns the messages which became ready, in message_seq order
-- (possibly none). Fragments which cannot be used are discarded rather
-- than failing the association (RFC 6347 4.1.2.7): the peer will
-- retransmit.
processHandshakeDTLS :: Context -> Version -> Fragment Plaintext -> IO (Either TLSError Packet)
processHandshakeDTLS ctx ver fragment =
    case decodeHandshakeFragmentsDTLS (fragmentGetBytes fragment) of
        Left err -> do
            logDiscard $ "undecodable handshake record: " ++ show err
            return $ Right $ Handshake []
        Right frags -> do
            (msgs, discarded) <- atomicModifyIORef' (ctxHandshakeReassembly ctx) (insertFragments frags)
            mapM_ logDiscard discarded
            keyxchg <- getHState ctx >>= \hs -> return (hs >>= hstPendingCipher >>= Just . cipherKeyExchange)
            let currentParams = CurrentParams
                                { cParamsVersion     = ver
                                , cParamsKeyXchgType = keyxchg
                                }
                decode (ty, msgSeq, content) = DtlsHandshake msgSeq <$> decodeHandshake currentParams ty content
            return $ Handshake <$> mapM decode msgs
  where logDiscard reason = withLog ctx $ \logging ->
            loggingPacketRecv logging $ "Discarded handshake fragment: " ++ reason
