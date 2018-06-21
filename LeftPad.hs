{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ infixr !!              @-}

import Prelude hiding ((!!), length, max)

{- Auxiliary -}
{-@ reflect !! @-}
{-@ (!!) :: xs:[a] -> {n:Nat | n < size xs} -> a @-}
(!!) :: [a] -> Int -> a
(x:_) !! 0 = x
(_:xs) !! n = xs !! (n-1)

{-@ reflect max @-}
max :: Int -> Int -> Int
max x y = if x > y then x else y

{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size :: [a] -> Int
size []     = 0
size (x:xs) = 1 + size xs


{- Proof that the length is correct -}
{-@ reflect leftPad @-}
{-@ leftPad :: n:Nat -> x:a -> xs:[a] ->
      { result : [a] |
          size result = max n (size xs)
      }
  @-}
leftPad :: Int -> a -> [a] -> [a]
leftPad n x xs = leftPad' k x xs
  where k = max 0 (n - size xs)

{-@ reflect leftPad' @-}
{-@ leftPad' :: n:Nat -> x:a -> xs:[a] ->
      { result : [a] |
          size result = n + size xs
      }
  @-}
leftPad' :: Int -> a -> [a] -> [a]
leftPad' 0 x xs = xs
leftPad' n x xs = x : leftPad' (n-1) x xs

{- Proof that the elements are correct -}

{-@ thmLeftPadA ::
      n:Nat -> x:a -> xs:[a] ->
      i:{Nat | i < n} ->
        { leftPad' n x xs !! i == x }
  @-}
thmLeftPadA :: Int -> a -> [a] -> Int -> ()
thmLeftPadA n x xs 0 = ()
thmLeftPadA n x xs i = thmLeftPadA (n-1) x xs (i-1)

{-@ thmLeftPadB ::
      n:Nat -> x:a -> xs:[a] ->
      i:{Nat | i >= n && i < n + size xs} ->
        { leftPad' n x xs !! i == xs !! (i-n) }
  @-}
thmLeftPadB :: Int -> a -> [a] -> Int -> ()
thmLeftPadB 0 x xs i = ()
thmLeftPadB n x xs i = thmLeftPadB (n-1) x xs (i-1)


{-@ thmLeftPad :: n:Int -> x:a -> xs:[a] -> i:{Nat | i < n} ->
      { leftPad n x xs !! i == leftPadElt n x xs i }
  @-}
thmLeftPad :: Int -> a -> [a] -> Int -> ()
thmLeftPad n x xs i
  | i < k = thmLeftPadA k x xs i
  | otherwise = thmLeftPadB k x xs i
  where k = max 0 (n - size xs)


{-@ reflect leftPadElt @-}
{-@ leftPadElt :: n:Int -> x:a -> xs:[a] -> i:{Nat | i < n} -> a @-}
leftPadElt :: Int -> a -> [a] -> Int -> a
leftPadElt n x xs i
  | i < k = x
  | otherwise = xs !! (i-k)
  where k = max 0 (n - size xs)

