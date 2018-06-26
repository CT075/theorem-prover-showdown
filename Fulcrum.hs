{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--higherorder" @-}
{-@ infixr !!              @-}

import Prelude hiding ((!!), length, elem)
import Language.Haskell.Liquid.ProofCombinators

{-@ reflect !! @-}
{-@ !! :: xs:[a] -> i:{Nat | i < len xs} -> a @-}
(x:_) !! 0 = x
(_:xs) !! i = xs !! (i-1)

{-@ reflect min @-}
min :: Int -> Int -> Int
min x y = if x < y then x else y

{-@ reflect minimum @-}
{-@ minimum :: xs:{[Int] | len xs > 0} -> Int @-}
minimum :: [Int] -> Int
minimum (x:xs) = minimum' x xs

{-@ minimum' :: Int -> [Int] -> Int @-}
minimum' :: Int -> [Int] -> Int
minimum' x [] = x
minimum' x (y:ys) = minimum' (min x y) ys

{-@ thmMinimum ::
      xs:{[Int] | len xs > 0} ->
      i:{Nat | i < len xs} ->
      {xs !! i >= minimum xs}
  @-}
thmMinimum _ _ = error "not implemented!"

{-@ fulcrum :: xs:[Int] ->
               i:{Nat | i < len xs && splits xs !! i == minimum (splits xs)}
  @-}
fulcrum _ = error "not implemented!"

