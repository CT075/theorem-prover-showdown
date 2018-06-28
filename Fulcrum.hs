{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--higherorder" @-}
{-@ infixr !!              @-}

import Prelude hiding ((!!), length, min, minimum, elem, abs)
import Language.Haskell.Liquid.ProofCombinators

{-@ reflect !! @-}
{-@ !! :: xs:[a] -> i:{Nat | i < len xs} -> a @-}
(!!) :: [a] -> Int -> a
(x:_) !! 0 = x
(_:xs) !! i = xs !! (i-1)

{-@ abs :: Int -> Nat @-}
abs :: Int -> Int
abs x = if x < 0 then 0 - x else x

{-@ reflect min @-}
min :: Int -> Int -> Int
min x y = if x < y then x else y

{-@ reflect absmin @-}
absmin :: Int -> Int -> Int
absmin x y = min (abs x) (abs y)

{-@ reflect minimum @-}
{-@ minimum :: xs:{[Int] | len xs > 0} -> Int @-}
minimum :: [Int] -> Int
minimum (x:xs) = minimum' x xs

{-@ minimum' :: Int -> xs:[Int] -> Int / [len xs] @-}
minimum' :: Int -> [Int] -> Int
minimum' x [] = x
minimum' x (y:ys) = minimum' (min x y) ys

{-@ reflect elem @-}
elem :: Eq a => a -> [a] -> Bool
x `elem` [] = False
x `elem` (y:ys) = x == y || x `elem` ys

{-@ thmMinimum ::
      xs:{[Int] | len xs > 0} ->
      x:{Int | elem x xs} ->
      {x >= minimum xs}
  @-}
thmMinimum :: [Int] -> Int -> Proof
thmMinimum _ _ = trivial *** QED

  {-
{-@ fulcrum :: xs:[Int] ->
               i:{Nat | i < len xs && splits xs !! i == minimum (splits xs)}
  @-}
fulcrum _ = error "not implemented!"

splits l = splits' l (sum l)

splits' [] t = []
splits' (x:xs) t = t:splits' xs (abs (t - 2*x))

-}
