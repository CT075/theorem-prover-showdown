{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--higherorder" @-}
{-@ infixr !!              @-}
{-@ infixr ++ @-}

import Prelude hiding
  ((!!), (++), length, min, minimum, elem, abs, drop, take)
import Language.Haskell.Liquid.ProofCombinators

{-@ reflect !! @-}
{-@ !! :: xs:[a] -> i:{Nat | i < len xs} -> a @-}
(!!) :: [a] -> Int -> a
(x:_) !! 0 = x
(_:xs) !! i = xs !! (i-1)

{-@ reflect ++ @-}
{-@ ++ :: xs:[a] -> ys:[a] -> r:{len r == len xs + len ys} @-}
(++) :: [a] -> [a] -> [a]
[] ++ l = l
(x:xs) ++ l = x:(xs ++ l)

{-@ abs :: Int -> Nat @-}
abs :: Int -> Int
abs x = if x < 0 then 0 - x else x

{-@ reflect min @-}
{-@ min :: x:Int -> y:Int -> r:{Int | r <= x && r <= y} @-}
min :: Int -> Int -> Int
min x y = if x < y then x else y

{-@ reflect absmin @-}
absmin :: Int -> Int -> Int
absmin x y = min (abs x) (abs y)

{-@ reflect cons @-}
cons :: a -> [a] -> [a]
cons x xs = x:xs

{-@ reflect elem @-}
elem :: Eq a => a -> [a] -> Bool
x `elem` [] = False
x `elem` (y:ys) = x == y || x `elem` ys

{-@ reflect take @-}
{-@ take :: x:Nat -> xs:{[a] | len xs >= x} -> r:{[a] | len r == x} @-}
take :: Int -> [a] -> [a]
take 0 _ = []
take i (x:xs) = x:take (i-1) xs

{-@ reflect drop @-}
{-@ drop ::
      x:Nat -> xs:{[a] | len xs >= x} -> r:{[a] | len r == len xs - x}
  @-}
drop :: Int -> [a] -> [a]
drop 0 l = l
drop i (x:xs) = drop (i-1) xs

{-@ thmTakeDrop ::
      x:Nat -> xs:{[Int] | len xs >= x} -> {take x xs ++ drop x xs == xs}
  @-}
thmTakeDrop :: Int -> [Int] -> Proof
thmTakeDrop 0 xs
  =   take 0 xs ++ drop 0 xs
  ==. [] ++ xs
  ==. xs
  *** QED
thmTakeDrop i (x:xs)
  =   take i (x:xs) ++ drop i (x:xs)
  ==. (x:take (i-1) xs) ++ drop (i-1) xs
  ==. x:(take (i-1) xs ++ drop (i-1) xs)
  ==. x:xs ? thmTakeDrop (i-1) xs
  *** QED

{-@ reflect minimum @-}
{-@ minimum :: xs:{[Int] | len xs > 0} -> x:{Int | elem x xs} @-}
minimum :: [Int] -> Int
minimum (x:[]) = x
minimum (x:xs) = min x (minimum xs)

{-@ thmMinimum ::
      xs:{[Int] | len xs > 0} -> y:{Int | elem y xs} ->
      {minimum xs <= y}
  @-}
thmMinimum :: [Int] -> Int -> Proof
thmMinimum (x:[]) y = trivial *** QED
thmMinimum (x:xs) y
  | x == y = trivial *** QED
  | otherwise
      =   minimum (x:xs)
      ==. min x (minimum xs)
      <=. minimum xs
      <=. y ? thmMinimum xs y
      *** QED

  {-
{-@ fulcrum :: xs:[Int] ->
               i:{Nat | i < len xs && pivots xs !! i == minimum (pivots xs)}
  @-}
fulcrum _ = error "not implemented!"
-}
