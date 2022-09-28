module Fulcrum.Properties where

open import Data.Vec as Vec using (Vec)
open import Data.Integer as Int hiding (suc; _≤_)
open import Data.Nat as Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties
open import Data.Fin as Fin hiding (_+_; _-_; suc; _≤_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All
open import Data.List.Extrema using (f[argmin]≤f[xs])
open import Relation.Binary.PropositionalEquality using (refl)

open import Fulcrum

-- All elements [Fin n] are in [enum n].
enum-all : ∀{n} → (m : Fin n) → m ∈ enum n
enum-all {zero} ()
enum-all {suc n} zero = here refl
enum-all {suc n} (Fin.suc m) = there (∈-map⁺ Fin.suc (enum-all {n} m))

-- [fv xs (fulcrumSlow xs) ≤ fv xs i] for all i ≤ n
fulcrum-min-fv : ∀{n : ℕ} →
  (i : Fin (suc n)) → (xs : Vec ℤ (suc n)) →
  fv xs (fulcrumSlow xs) ≤ fv xs i
fulcrum-min-fv {n} i xs = lookup all-enum≤fv (enum-all {suc n} i)
  where
    all-enum≤fv =
     f[argmin]≤f[xs] {_} {_} {_} ≤-totalOrder {_} {_} {fv xs} zero (enum (suc n))
