{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--higherorder" @-}
{-@ infixr !!              @-}

import Prelude hiding ((!!), length, elem)
import Language.Haskell.Liquid.ProofCombinators

{-@ absurd :: i:{Nat | i < 0} -> a @-}
absurd :: Int -> a
absurd _ = error "oops!"

{-@ measure size @-}
size :: [a] -> Int
size [] = 0
size (_:xs) = 1 + size xs

{-@ reflect !! @-}
{-@ (!!) :: xs:[a] -> i:{Nat | i < size xs} -> a @-}
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

{-@ thmUniqueA ::
      xs:[a] ->
      {x:a | elem x xs} ->
      { count x (unique xs) == 1 }
  @-}
thmUniqueA :: Eq a => [a] -> a -> Proof
thmUniqueA (x:xs) y
  | y `elem` xs =
      if x == y then
              count y (unique (x:xs))
          ==. count y (unique xs)
          ==. 1 ? thmUniqueA xs y
          *** QED
      else
              count y (unique (x:xs))
          ==. count y (x:unique xs)
          ==. count y (unique xs)
          ==. 1 ? thmUniqueA xs y
          *** QED
  | otherwise =
              count y (unique (x:xs))
          ==. 1 + count y (unique xs) ? equal x y
          ==. 1 ? thmUniqueB xs y `seq` thmElemCount y (unique xs)
          *** QED

{-@ thmUniqueB ::
      xs:[a] ->
      {x:a | not elem x xs} ->
      { not elem x (unique xs) }
  @-}
thmUniqueB :: Eq a => [a] -> a -> Proof
thmUniqueB [] y = trivial *** QED
thmUniqueB (x:xs) y
  =   elem y (unique (x:xs))
  ==. elem y (x:unique xs)
  ==. elem y (unique xs)
  ==. False ? thmUniqueB xs y
  *** QED

