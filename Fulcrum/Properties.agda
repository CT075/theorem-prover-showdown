module Fulcrum.Properties where

open import Data.Vec as Vec using (Vec; take; drop; []; _∷_)
open import Data.Vec.Properties
open import Data.Integer as Int hiding (suc; _≤_)
open import Data.Nat as Nat using (ℕ; zero; suc; _≤_) renaming (_≡ᵇ_ to _≡ℕ_)
open import Data.Nat.Properties
open import Data.Fin as Fin hiding (_+_; _-_; suc; _≤_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All
open import Data.List.Extrema using (f[argmin]≤f[xs])
open import Relation.Binary.PropositionalEquality using (refl; _≡_; cong)

open import Fulcrum.Base

-- All elements [Fin n] are in [enum n].
enum-all : ∀{n} → (m : Fin n) → m ∈ enum n
enum-all {zero} ()
enum-all {suc n} zero = here refl
enum-all {suc n} (Fin.suc m) = there (∈-map⁺ Fin.suc (enum-all {n} m))

-- [fv xs (fulcrumSlow xs) ≤ fv xs i] for all i ≤ n
fulcrum-min-fv : ∀{n : ℕ} {xs : Vec ℤ (suc n)} →
  (i : Fin (suc n)) → fv xs (fulcrumSlow xs) ≤ fv xs i
fulcrum-min-fv {n} {xs} i = lookup all-enum≤fv (enum-all {suc n} i)
  where
    all-enum≤fv =
     f[argmin]≤f[xs] ≤-totalOrder {f = fv xs} zero (enum (suc n))

leftSumsSlow-take : ∀{n : ℕ} {xs : Vec ℤ n} →
  (i : Fin n) → Vec.lookup (leftSumsSlow xs) i ≡ sum (takeFin i xs)
leftSumsSlow-take {zero} {[]} ()
leftSumsSlow-take {suc n} {_ ∷ _} zero = refl
leftSumsSlow-take {suc n} {x ∷ xs} (Fin.suc i) =
    Vec.lookup (leftSumsSlow (x ∷ xs)) (Fin.suc i)
  ≡⟨ refl ⟩
    Vec.lookup ((+ 0) ∷ Vec.map (λ y → x + y) (leftSumsSlow xs)) (Fin.suc i)
  ≡⟨ refl ⟩
    Vec.lookup (Vec.map (λ y → x + y) (leftSumsSlow xs)) i
  ≡⟨ lookup-map i (λ y → x + y) (leftSumsSlow xs) ⟩
    (λ y → x + y) (Vec.lookup (leftSumsSlow xs) i)
  ≡⟨ cong (λ t → (λ y → x + y) t) (leftSumsSlow-take {n} {xs} i) ⟩
    (λ y → x + y) (sum (takeFin i xs))
  ≡⟨ refl ⟩
    x + (sum (takeFin i xs))
  ≡⟨ refl ⟩
    sum (takeFin (Fin.suc i) (x ∷ xs))
  ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
