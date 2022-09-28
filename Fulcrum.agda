module Fulcrum where

open import Data.Vec as Vec using (Vec)
open import Data.List as List using (List; take; drop; foldr; []; _∷_)
open import Data.List.Extrema.Nat using (argmin)
open import Data.Integer as Int hiding (_<_; suc)
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Fin as Fin hiding (_+_; _-_; suc)

sum : List ℤ → ℤ
sum = foldr (_+_) (+ 0)

abs : ℤ → ℕ
abs x = ∣ x ∣

enum : (n : ℕ) → List (Fin n)
enum zero = []
enum (suc n) = zero ∷ List.map Fin.suc (enum n)

fv : ∀{n} → Vec ℤ n → Fin n → ℕ
fv xs' i' = abs (sum (take i xs) - sum (drop i xs))
  where
    i = Fin.toℕ i'
    xs = Vec.toList xs'

fulcrumSlow : ∀{n : ℕ} → Vec ℤ (suc n) → Fin (suc n)
fulcrumSlow {n} xs = argmin (fv xs) zero (enum (suc n))

