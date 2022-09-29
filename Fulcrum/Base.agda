module Fulcrum.Base where

open import Data.Vec as Vec using (Vec; _∷_; []; take; drop; foldr′)
open import Data.List as List using (List; _∷_; [])
open import Data.List.Extrema.Nat using (argmin)
open import Data.Integer as Int hiding (_<_; suc)
open import Data.Nat as Nat using (ℕ; zero; suc; _∸_)
open import Data.Fin as Fin hiding (_+_; _-_; suc)
open import Data.Fin.Properties using (toℕ-fromℕ; opposite-suc)

sum : ∀{n : ℕ} → Vec ℤ n → ℤ
sum = foldr′ (_+_) (+ 0)

abs : ℤ → ℕ
abs x = ∣ x ∣

-- We could use [allFin], but I think this way works better with [Extrema]
enum : (n : ℕ) → List (Fin n)
enum zero = []
enum (suc n) = zero ∷ List.map Fin.suc (enum n)

takeFin : ∀{T : Set} {n : ℕ} → (i : Fin n) → Vec T n → Vec T (toℕ i)
takeFin zero _ = []
takeFin (Fin.suc n) (x ∷ xs) = x ∷ (takeFin n xs)

dropFin : ∀{T : Set} {n : ℕ} →
  (i : Fin n) → Vec T n → Vec T (suc (toℕ (opposite i)))
dropFin {n = n} zero xs rewrite (toℕ-fromℕ n) = xs
dropFin {n = suc n} (Fin.suc i) (_ ∷ xs)
  rewrite (opposite-suc i) = dropFin i xs

fv : ∀{n : ℕ} → Vec ℤ n → Fin n → ℕ
fv {n} xs i = abs (sum (takeFin i xs) - sum (dropFin i xs))

fulcrumSlow : ∀{n : ℕ} → Vec ℤ (suc n) → Fin (suc n)
fulcrumSlow {n} xs = argmin (fv xs) zero (enum (suc n))

leftSums : ∀{n : ℕ} → Vec ℤ n → Vec ℤ n
leftSums [] = []
leftSums (x ∷ xs) = (+ 0) ∷ Vec.map (_+ x) (leftSums xs)

--rightSums : ∀{n : ℕ} → Vec ℤ n → Vec ℤ n
--rightSums xs = Vec.map (λ x → s - x) xs
--  where
--    s = sum (Vec.toList xs)
