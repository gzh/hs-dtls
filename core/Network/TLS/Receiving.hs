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

import qualified Data.ByteString as BS

processPacket :: Context -> Record Plaintext -> IO (Either TLSError Packet)

processPacket _ (Record ProtocolType_AppData _ _ fragment) = return $ Right $ AppData $ fragmentGetBytes fragment

processPacket _ (Record ProtocolType_Alert _ _ fragment) = return (Alert `fmapEither` decodeAlerts (fragmentGetBytes fragment))

processPacket ctx (Record ProtocolType_ChangeCipherSpec _ _ fragment) =
    case decodeChangeCipherSpec $ fragmentGetBytes fragment of
        Left err -> return $ Left err
        Right _  -> do switchRxEncryption ctx
                       return $ Right ChangeCipherSpec

processPacket ctx (Record ProtocolType_Handshake ver _ fragment) = do
    keyxchg <- getHState ctx >>= \hs -> return (hs >>= hstPendingCipher >>= Just . cipherKeyExchange)
    ehss <- usingState ctx $ do
        let currentParams = CurrentParams
                            { cParamsVersion     = ver
                            , cParamsKeyXchgType = keyxchg
                            }
        -- get back the optional continuation, and parse as many handshake record as possible.
        mCont <- gets stHandshakeRecordCont
        modify (\st -> st { stHandshakeRecordCont = Nothing })
        hss   <- parseMany currentParams mCont (fragmentGetBytes fragment)
        return hss
    case ehss of
      Left err -> return $ Left err
      Right (hss@[DtlsHandshake _ (ClientHello _ _ _ cookie _ _ _ _)]) ->
        if cookie == HelloCookie BS.empty
        then return $ Right $ Handshake hss
        else (Right . Handshake . catMaybes) <$> mapM (replayGuard ctx) hss
      Right hss -> (Right . Handshake . catMaybes) <$> mapM (replayGuard ctx) hss
  where decodeHandshakeRecordX = if isDTLS ver
                                 then decodeHandshakeRecordsDTLS
                                 else decodeHandshakeRecord
        parseMany currentParams mCont bs =
            case fromMaybe decodeHandshakeRecordX mCont bs of
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

replayGuard :: Context -> Handshake -> IO (Maybe Handshake)
replayGuard ctx hs@(DtlsHandshake ind _) = do
  pass <- ctxUpdateHsMsgSeq ctx ind
  if pass then return $ Just hs else return Nothing
replayGuard _ hs = return $ Just hs
