{--! run liquid with no-termination -}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ infixr ++              @-}
{-@ infixr !!              @-}

module SimpleRefinements where
import Prelude hiding ((!!), length, max)
import Language.Haskell.Liquid.Prelude

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
{-@ leftPad :: n:Int -> c:a -> xs:[a] ->
      { result : [a] |
          size result = max n (size xs)
      }
  @-}
leftPad :: Int -> a -> [a] -> [a]
leftPad n x xs = leftPad' k x xs
  where k = max 0 (n - size xs)

{-@ reflect leftPad' @-}
leftPad' 0 n xs = xs
leftPad' n x xs = x : leftPad (n-1) x xs

{- Auxiliary: indexing -}
{-@ reflect !! @-}
{-@ (!!) :: xs:[a] -> {n:Nat | n < size xs} -> a @-}
(!!) :: [a] -> Int -> a
(x:_) !! 0 = x
(_:xs) !! n = xs !! (n-1)

{- Proof that the elements are correct -}
{-
{-@ thmLeftPadA :: n:Int -> c:a -> xs:[a] -> i:{Nat | i < n} ->
  @-}
thmLeftPadA n c xs i =
-}

{-@ thmLeftPad :: n:Int -> c:a -> xs:[a] -> i:{Nat | i < n} ->
      { leftPad n c xs !! i == leftPadElt n c xs i }
  @-}
thmLeftPad :: Int -> a -> [a] -> Int -> ()
thmLeftPad n c xs i = ()
  where k = max 0 (n - size xs)

{-@ reflect leftPadElt @-}
leftPadElt :: Int -> a -> [a] -> Int -> a
leftPadElt n c xs i
  | i < k = c
  | otherwise = xs !! (i-k)
  where k = max 0 (n - size xs)
