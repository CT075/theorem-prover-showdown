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
               i:{Nat | i < len xs && splits xs !! i == minimum (splits xs)}
  @-}
fulcrum _ = error "not implemented!"

splits l = splits' l (sum l)

splits' [] t = []
splits' (x:xs) t = t:splits' xs (abs (t - 2*x))

-}
