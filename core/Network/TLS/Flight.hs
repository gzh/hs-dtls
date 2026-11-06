-- |
-- Module      : Network.TLS.Flight
-- License     : BSD-style
-- Stability   : experimental
-- Portability : unknown
--
-- DTLS flights: packing of records into datagrams, and retransmission of
-- the last flight sent (RFC 6347 4.2.4).
--
-- Handshake records are queued, and only sent when the flight is complete
-- (see 'flushFlight'), packed into as few datagrams as possible. Fewer
-- datagrams make a flight less sensitive to reordering and loss: e.g.
-- ChangeCipherSpec and Finished can't arrive in the wrong order.
--
-- A flight is retransmitted as the very datagrams which were sent: the
-- handshake messages are not encoded again, as that would update the
-- handshake transcript and the record layer state a second time.
--
module Network.TLS.Flight
    ( packDatagrams
    , datagramSizeLimit
    , queueFlightRecords
    , flushFlight
    , flightAcknowledged
    , retransmitFlight
    , retransmitFlightOnPeerRetransmission
    ) where

import Network.TLS.Context.Internal
import Network.TLS.Hooks
import Network.TLS.Imports

import Control.Concurrent.MVar
import GHC.Clock (getMonotonicTime)
import qualified Data.ByteString as B

-- | Group consecutive records into datagrams of at most the given size.
-- Records are never split; a record larger than the limit is sent alone.
packDatagrams :: Int -> [ByteString] -> [ByteString]
packDatagrams limit = map B.concat . go
  where go []     = []
        go (r:rs) = let (grp, rest) = fill (B.length r) rs in (r : grp) : go rest
        fill n (r:rs) | n + B.length r <= limit = let (grp, rest) = fill (n + B.length r) rs
                                                  in (r : grp, rest)
        fill _ rs = ([], rs)

-- | Size up to which records are packed together: that of a record
-- carrying a full size handshake fragment (record and handshake headers
-- included), so that packing never makes datagrams larger than they would
-- be with one record each.
datagramSizeLimit :: Context -> Int
datagramSizeLimit ctx = fromIntegral (ctxMTU ctx) + 13 + 12

-- | Minimal interval between retransmissions caused by the peer's own
-- retransmissions, so that one retransmitted flight of several records
-- gets a single response.
minRetransmitInterval :: Double
minRetransmitInterval = 0.1

-- | Queue handshake (and ChangeCipherSpec) records for sending. They
-- start a new flight if the peer has acknowledged the previous one,
-- otherwise they are appended to the current one.
queueFlightRecords :: Context -> [ByteString] -> IO ()
queueFlightRecords ctx records = modifyMVar_ (ctxFlight ctx) $ \fl -> return $
    if flightAcked fl
        then fl { flightDatagrams = [], flightPending = flightPending fl ++ records, flightAcked = False }
        else fl { flightPending = flightPending fl ++ records }

-- | Send the queued records, and keep them for retransmission. To be
-- called when the flight is complete (before waiting for the peer, after
-- the last flight of the handshake), and before sending anything else so
-- that the order of records is preserved.
flushFlight :: Context -> IO ()
flushFlight ctx = modifyMVar_ (ctxFlight ctx) $ \fl ->
    if null (flightPending fl)
        then return fl
        else do
            let dgrams = packDatagrams (datagramSizeLimit ctx) (flightPending fl)
            mapM_ (sendDatagram ctx) dgrams
            now <- getMonotonicTime
            return fl { flightDatagrams = flightDatagrams fl ++ dgrams
                      , flightPending   = []
                      , flightSentAt    = now }

-- | The peer has proceeded past our last flight, which needs no
-- retransmission any more.
flightAcknowledged :: Context -> IO ()
flightAcknowledged ctx = modifyMVar_ (ctxFlight ctx) $ \fl -> return fl { flightAcked = True }

-- | Retransmission on timer expiry.
retransmitFlight :: Context -> IO ()
retransmitFlight ctx = modifyMVar_ (ctxFlight ctx) $ \fl ->
    if flightAcked fl || null (flightDatagrams fl) then return fl else resend ctx fl

-- | The peer has retransmitted (part of) a flight we had already
-- received, so our response to it has probably been lost: retransmit it
-- now. This is what makes the last flight of the handshake recoverable,
-- as no timer runs for it.
retransmitFlightOnPeerRetransmission :: Context -> IO ()
retransmitFlightOnPeerRetransmission ctx = modifyMVar_ (ctxFlight ctx) $ \fl -> do
    now <- getMonotonicTime
    if flightAcked fl || null (flightDatagrams fl) || now - flightSentAt fl < minRetransmitInterval
        then return fl
        else resend ctx fl

resend :: Context -> Flight -> IO Flight
resend ctx fl = do
    withLog ctx $ \logging -> loggingPacketSent logging $
        "Retransmitting flight of " ++ show (length $ flightDatagrams fl) ++ " datagram(s)"
    mapM_ (sendDatagram ctx) (flightDatagrams fl)
    now <- getMonotonicTime
    return fl { flightSentAt = now }

sendDatagram :: Context -> ByteString -> IO ()
sendDatagram ctx d = do
    withLog ctx $ \logging -> loggingIOSent logging d
    contextSend ctx d
