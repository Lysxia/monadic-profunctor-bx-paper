module Util where

headM :: [a] -> Maybe a
headM [] = Nothing
headM (x:_) = Just x

tailM :: [a] -> Maybe [a]
tailM []     = Nothing
tailM (_:xs) = Just xs