{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--higherorder" @-}
{-@ infixr !!              @-}

import Prelude hiding ((!!), length, elem)
import Language.Haskell.Liquid.ProofCombinators

{-@ reflect !! @-}
{-@ (!!) :: xs:[a] -> i:{Nat | i < len xs} -> a @-}
(!!) :: [a] -> Int -> a
(x:xs) !! 0 = x
(x:xs) !! n = xs !! (n-1)

{-@ reflect elem @-}
elem :: Eq a => a -> [a] -> Bool
elem x [] = False
elem x (y:ys) = x == y || elem x ys

{-@ reflect count @-}
count :: Eq a => a -> [a] -> Int
count _ [] = 0
count x (y:ys)
  | x == y = 1 + count x ys
  | otherwise = count x ys

{-@ reflect hd @-}
{-@ hd :: xs:{[a] | len xs > 0} -> a @-}
hd (x:xs) = x

{-@ reflect tl @-}
{-@ tl :: xs:{[a] | len xs > 0} -> [a] @-}
tl (x:xs) = xs

{-@ reflect unique @-}
{-@ unique :: Eq a => inp:[a] -> out:[a] @-}
unique :: Eq a => [a] -> [a]
unique [] = []
unique (x:xs)
  | x `elem` xs = unique xs
  | otherwise = x:unique xs

{-@ reflect thmElemCount @-}
{-@ thmElemCount :: Eq a =>
      x:a -> xs:{[a] | not elem x xs} -> { count x xs == 0 }
  @-}
thmElemCount :: Eq a => a -> [a] -> ()
thmElemCount x [] = ()
thmElemCount x (y:ys) = thmElemCount x ys

{-@ equal :: x:a -> y:{a | y == x} -> {x == y} @-}
equal :: Eq a => a -> a -> Proof
equal x y = trivial *** QED

{-@ thmUniqueNoDup ::
      xs:[a] ->
      {x:a | elem x xs} ->
      { count x (unique xs) == 1 }
  @-}
thmUniqueNoDup :: Eq a => [a] -> a -> Proof
thmUniqueNoDup (x:xs) y
  | y `elem` xs =
      if x == y then
              count y (unique (x:xs))
          ==. count y (unique xs)
          ==. 1 ? thmUniqueNoDup xs y
          *** QED
      else
              count y (unique (x:xs))
          ==. count y (x:unique xs)
          ==. count y (unique xs)
          ==. 1 ? thmUniqueNoDup xs y
          *** QED
  | otherwise =
              count y (unique (x:xs))
          ==. 1 + count y (unique xs) ? equal x y
          ==. 1 ? thmUniqueExistInv xs y `seq` thmElemCount y (unique xs)
          *** QED

{-@ thmUniqueExist ::
      xs:[a] ->
      {x:a | elem x (unique xs)} ->
      { elem x xs }
  @-}
thmUniqueExist :: Eq a => [a] -> a -> Proof
thmUniqueExist (x:xs) y
  | y == x = trivial *** QED
  | otherwise
      =   elem y (x:xs)
      ==. elem y xs
      ==. True ? thmUniqueExist' (x:xs) y `seq` thmUniqueExist xs y
      *** QED

{-@ thmUniqueExist' ::
      xs:{[a] | len xs > 0} ->
      {x:a | elem x (unique xs) && x != hd xs} ->
      { elem x (unique (tl xs)) }
  @-}
thmUniqueExist' :: Eq a => [a] -> a -> Proof
thmUniqueExist' (x:xs) y
  =   elem y (unique (tl (x:xs)))
  ==. elem y (unique xs)
  ==. elem y (x:unique xs)
  ==. elem y (unique (x:xs))
  ==. True
  *** QED

{-@ thmUniqueExistInv ::
      xs:[a] ->
      {x:a | not elem x xs} ->
      { not elem x (unique xs) }
  @-}
thmUniqueExistInv :: Eq a => [a] -> a -> Proof
thmUniqueExistInv [] y = trivial *** QED
thmUniqueExistInv (x:xs) y
  =   elem y (unique (x:xs))
  ==. elem y (x:unique xs)
  ==. elem y (unique xs)
  ==. False ? thmUniqueExistInv xs y
  *** QED

