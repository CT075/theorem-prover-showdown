
{- Proof that the length is correct -}
{-@ reflect leftPad @-}
{-@ leftPad :: n:Int -> c:a -> xs:[a] ->
      { result : [a] |
          size result = max n (size xs)
      }
  @-}
leftPad :: Int -> a -> [a] -> [a]
leftPad 0 _ xs = xs
leftPad x n xs = x ::: leftPad x (n-1) xs

{- Auxiliary: indexing -}
{-@ reflect !! @-}
{-@ (!!) :: xs:[a] -> {n:Nat | n < size xs} -> a @-}
(x:_) !! 0 = x
(_:xs) !! n = xs !! (n-1)

{- Proof that the elements are correct -}
{-@ thmElt :: n:Int -> c:a -> xs:[a] -> i:{Nat | i < n}
      { leftPad n c xs !! i == leftPadElt n c xs i }
  @-}
thmElt = error "oops!"

{-@ reflect leftPadElt @-}
leftPadElt n c xs i
  | i < k = c
  | otherwise = xs !! (i-k)
  where k = n - size xs

