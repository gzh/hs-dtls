-- |
-- Module      : Network.TLS.Record.ReplayWindow
-- License     : BSD-style
-- Stability   : experimental
-- Portability : unknown
--
-- DTLS anti-replay sliding window (RFC 6347 section 4.1.2.6).
--
-- Unlike a strictly increasing check, the window accepts records which
-- arrive out of order, as long as they are not too old and have not
-- been seen before. Sequence numbers are the full 64-bit DTLS values
-- (epoch in the 16 most significant bits).
--
module Network.TLS.Record.ReplayWindow
    ( ReplayWindow
    , newReplayWindow
    , replayWindowSize
    , isReplayed
    , markReceived
    ) where

import Network.TLS.Imports

data ReplayWindow = ReplayWindow
    { rwHighest :: !(Maybe Word64) -- ^ highest sequence number received so far
    , rwBitmap  :: !Word64         -- ^ bit n is set if (highest - n) was received
    } deriving (Show, Eq)

replayWindowSize :: Word64
replayWindowSize = 64

newReplayWindow :: ReplayWindow
newReplayWindow = ReplayWindow Nothing 0

-- | Whether a record with this sequence number has to be discarded, being
-- either a duplicate or too old to be checked.
isReplayed :: Word64 -> ReplayWindow -> Bool
isReplayed _ (ReplayWindow Nothing _) = False
isReplayed sn (ReplayWindow (Just h) bm)
    | sn > h                     = False
    | h - sn >= replayWindowSize = True
    | otherwise                  = testBit bm (fromIntegral $ h - sn)

-- | Record the sequence number as received. Should only be called for
-- records which passed verification.
markReceived :: Word64 -> ReplayWindow -> ReplayWindow
markReceived sn (ReplayWindow Nothing _) = ReplayWindow (Just sn) 1
markReceived sn w@(ReplayWindow (Just h) bm)
    | sn > h = let d = sn - h
                   bm' = if d >= replayWindowSize then 0 else bm `shiftL` fromIntegral d
               in ReplayWindow (Just sn) (bm' .|. 1)
    | h - sn >= replayWindowSize = w
    | otherwise = ReplayWindow (Just h) (bm `setBit` fromIntegral (h - sn))
