{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ infixr !!              @-}

{-@ measure size @-}
size :: [a] -> Int
size [] = 0
size (_:xs) = 1 + size xs

{-@ reflect (!!) @-}
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
count x (y:ys) = if x == y then 1 + count x ys else count x ys

{-@ reflect unique @-}
{-@ unique :: Eq a => inp:[a] -> out:[a] @-}
unique :: Eq a => [a] -> [a]
unique [] = []
unique (x:xs) = if x `elem` xs then unique xs else x:unique xs

{-@ reflect thmUniqueNoDups @-}
{-@ thmUniqueNoDups :: Eq a =>
      xs:[a] ->
      i:{Nat | i < size inp} ->
        { count (out !! i) out == 1
            where out = unique xs
        }
  @-}
thmUniqueNoDups :: [a] -> Int -> ()
thmUniqueNoDups _ _ = ()

