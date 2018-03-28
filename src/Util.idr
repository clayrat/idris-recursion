module Util

import Data.CoList

%default total
%access public export 

filterCo : (a -> Bool) -> CoList a -> CoList a
filterCo p []      = []
filterCo p (x::xs) =
  if p x then
    x :: filterCo p xs
  else
    assert_total $ filterCo p xs

notdiv : Integer -> Integer -> Bool
notdiv a b = assert_total $ b `mod` a /= 0    