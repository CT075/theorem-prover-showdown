module Fulcrum.Properties where

open import Data.Vec as Vec using (Vec; take; drop; []; _∷_; _++_; zipWith)
open import Data.Vec.Properties
open import Data.Integer as Int hiding (suc; _≤_)
open import Data.Integer.Properties
  using (+-identityʳ; +-identityˡ; +-assoc; +-comm; i≡j⇒i-j≡0)
open import Data.Nat as Nat
  using (ℕ; zero; suc; _≤_; _∸_)
  renaming (_≡ᵇ_ to _≡ℕ_)
open import Data.Nat.Properties
  using (≤-totalOrder; +-∸-assoc; +-∸-comm; ≤-reflexive; n∸n≡0; ≤-pred)
  renaming (+-comm to +ℕ-comm; +-identityʳ to +ℕ-identityʳ)
open import Data.Fin as Fin hiding (_+_; _-_; _≤_)
open import Data.Fin.Properties using (toℕ<n; opposite-prop)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All hiding (zipWith)
open import Data.List.Extrema using (f[argmin]≤f[xs])
open import Relation.Binary.PropositionalEquality using (refl; _≡_; cong; sym)

open import Fulcrum.Base

-- All elements [Fin n] are in [enum n].
enum-spec : ∀{n} → (m : Fin n) → m ∈ enum n
enum-spec {zero} ()
enum-spec {suc n} zero = here refl
enum-spec {suc n} (Fin.suc m) = there (∈-map⁺ Fin.suc (enum-spec {n} m))

-- [fv xs (fulcrumSlow xs) ≤ fv xs i] for all i ≤ n
fulcrumSlow-spec : ∀{n : ℕ} {xs : Vec ℤ (suc n)} →
  (i : Fin (suc n)) → fv xs (fulcrumSlow xs) ≤ fv xs i
fulcrumSlow-spec {n} {xs} i = lookup all-enum≤fv (enum-spec {suc n} i)
  where
    all-enum≤fv =
     f[argmin]≤f[xs] ≤-totalOrder {f = fv xs} zero (enum (suc n))

open Relation.Binary.PropositionalEquality.≡-Reasoning

leftSumsImpl-spec : ∀{n : ℕ} {xs : Vec ℤ n} →
  (acc : ℤ) → (i : Fin n) →
  Vec.lookup (leftSumsImpl acc xs) i ≡ acc + sum (takeFin i xs)
leftSumsImpl-spec {zero} {[]} acc ()
leftSumsImpl-spec {suc n} {x ∷ xs} acc zero =
    Vec.lookup (leftSumsImpl acc (x ∷ xs)) zero
  ≡⟨ refl ⟩
    Vec.lookup (acc ∷ leftSumsImpl (acc + x) xs) zero
  ≡⟨ refl ⟩
    acc
  ≡⟨ sym (+-identityʳ acc) ⟩
    acc + (+ 0)
  ≡⟨ refl ⟩
    acc + sum []
  ≡⟨ refl ⟩
    acc + sum (takeFin zero (x ∷ xs))
  ∎
leftSumsImpl-spec {suc n} {x ∷ xs} acc (suc i) =
    Vec.lookup (leftSumsImpl acc (x ∷ xs)) (suc i)
  ≡⟨ refl ⟩
    Vec.lookup (acc ∷ leftSumsImpl (acc + x) xs) (suc i)
  ≡⟨ refl ⟩
    Vec.lookup (leftSumsImpl (acc + x) xs) i
  ≡⟨ leftSumsImpl-spec {n} {xs} (acc + x) i ⟩
    (acc + x) + sum (takeFin i xs)
  ≡⟨ +-assoc acc x (sum (takeFin i xs)) ⟩
    acc + (x + sum (takeFin i xs))
  ≡⟨ refl ⟩
    acc + (sum (takeFin (suc i) (x ∷ xs)))
  ∎

leftSums-spec : ∀{n : ℕ} {xs : Vec ℤ n} →
  (i : Fin n) → Vec.lookup (leftSums xs) i ≡ sum (takeFin i xs)
leftSums-spec {n} {xs} i =
    Vec.lookup (leftSums xs) i
  ≡⟨ refl ⟩
    Vec.lookup (leftSumsImpl (+ 0) xs) i
  ≡⟨ leftSumsImpl-spec {n} {xs} (+ 0) i ⟩
    (+ 0) + sum (takeFin i xs)
  ≡⟨ +-identityˡ (sum (takeFin i xs)) ⟩
    sum (takeFin i xs)
  ∎

sum-append : ∀{n m : ℕ} →
  (xs : Vec ℤ n) → (ys : Vec ℤ m) → sum (xs ++ ys) ≡ sum xs + sum ys
sum-append {zero} {m} [] ys =
    sum ([] ++ ys)
  ≡⟨ refl ⟩
    sum ys
  ≡⟨ sym (+-identityˡ (sum ys)) ⟩
    (+ 0) + sum ys
  ≡⟨ refl ⟩
    sum [] + sum ys
  ∎
sum-append {suc n} {m} (x ∷ xs) ys =
    sum ((x ∷ xs) ++ ys)
  ≡⟨ refl ⟩
    sum (x ∷ (xs ++ ys))
  ≡⟨ refl ⟩
    x + sum (xs ++ ys)
  ≡⟨ cong (λ t → x + t) (sum-append {n} {m} xs ys) ⟩
    x + (sum xs + sum ys)
  ≡⟨ sym (+-assoc x (sum xs) (sum ys)) ⟩
    (x + sum xs) + sum ys
  ≡⟨ refl ⟩
    sum (x ∷ xs) + sum ys
  ∎

postulate
  takeFin-dropFin-sum : ∀{n : ℕ} →
    (xs : Vec ℤ n) → (i : Fin n) → sum (takeFin i xs ++ dropFin i xs) ≡ sum xs
{-
takeFin-dropFin-sum {zero} xs ()
takeFin-dropFin-sum {suc n} xs zero =
    sum (takeFin zero xs ++ dropFin zero xs)
  ≡⟨ cong (λ t → sum (t ++ dropFin zero xs)) refl ⟩
    sum ([] ++ dropFin zero xs)
  ≡⟨ cong (λ t → sum ([] ++ t)) refl ⟩
    sum ([] ++ xs)
  ≡⟨ refl ⟩
    sum xs
  ∎
takeFin-dropFin-sum {suc n} (x ∷ xs) (Fin.suc i) =
    sum (takeFin (Fin.suc i) (x ∷ xs) ++ dropFin (Fin.suc i) (x ∷ xs))
  ≡⟨ cong (λ t → sum (t ++ dropFin (Fin.suc i) (x ∷ xs))) refl ⟩
    sum ((x ∷ (takeFin i xs)) ++ dropFin (Fin.suc i) (x ∷ xs))
    {-
  ≡⟨ cong (λ t → sum ((x ∷ (takeFin i xs)) ++ t)) refl ⟩
    sum ((x ∷ (takeFin i xs)) ++ dropFin i xs)
    -}
  ≡⟨ {!!} ⟩
    {!!}
  ∎
-}

rightSums-spec : ∀{n : ℕ} {xs : Vec ℤ n} →
  (i : Fin n) → Vec.lookup (rightSums xs) i ≡ sum (dropFin i xs)
rightSums-spec {n} {xs} i =
    Vec.lookup (rightSums xs) i
  ≡⟨ refl ⟩
    Vec.lookup (
      let s = sum xs in
      Vec.map (λ x → s - x) (leftSums xs)) i
  ≡⟨ refl ⟩
    Vec.lookup (Vec.map (λ x → sum xs - x) (leftSums xs)) i
  ≡⟨ lookup-map i (λ x → sum xs - x) (leftSums xs) ⟩
    (λ x → sum xs - x) (Vec.lookup (leftSums xs) i)
  ≡⟨ cong (λ y → (λ x → sum xs - x) y) (leftSums-spec {n} {xs} i) ⟩
    (λ x → sum xs - x) (sum (takeFin i xs))
  ≡⟨ refl ⟩
    sum xs - sum (takeFin i xs)
  ≡⟨ cong (λ t → t - sum (takeFin i xs)) (sym (takeFin-dropFin-sum xs i)) ⟩
    sum (takeFin i xs ++ dropFin i xs) - sum (takeFin i xs)
  ≡⟨ cong (λ t → t - sum (takeFin i xs)) (sum-append (takeFin i xs) (dropFin i xs)) ⟩
    sum (takeFin i xs) + sum (dropFin i xs) - sum (takeFin i xs)
  ≡⟨ cong (λ t → t - sum (takeFin i xs)) (+-comm (sum (takeFin i xs)) (sum (dropFin i xs))) ⟩
    sum (dropFin i xs) + sum (takeFin i xs) - sum (takeFin i xs)
  ≡⟨ +-assoc (sum (dropFin i xs)) (sum (takeFin i xs)) (- sum (takeFin i xs)) ⟩
    sum (dropFin i xs) + (sum (takeFin i xs) - sum (takeFin i xs))
  ≡⟨ cong (λ t → sum (dropFin i xs) + t) (i≡j⇒i-j≡0 {sum (takeFin i xs)} refl) ⟩
    sum (dropFin i xs) + (+ 0)
  ≡⟨ +-identityʳ (sum (dropFin i xs)) ⟩
    sum (dropFin i xs)
  ∎

fvs-spec : ∀{n : ℕ} {xs : Vec ℤ n} →
  (i : Fin n) → Vec.lookup (fvs xs) i ≡ fv xs i
fvs-spec {n} {xs} i =
    Vec.lookup (fvs xs) i
  ≡⟨ refl ⟩
    Vec.lookup (zipWith absDiff (leftSums xs) (rightSums xs)) i
  ≡⟨ lookup-zipWith absDiff i (leftSums xs) (rightSums xs) ⟩
    absDiff (Vec.lookup (leftSums xs) i) (Vec.lookup (rightSums xs) i)
  ≡⟨ cong (λ t → absDiff t (Vec.lookup (rightSums xs) i)) (leftSums-spec i) ⟩
    absDiff (sum (takeFin i xs)) (Vec.lookup (rightSums xs) i)
  ≡⟨ cong (λ t → absDiff (sum (takeFin i xs)) t) (rightSums-spec i) ⟩
    absDiff (sum (takeFin i xs)) (sum (dropFin i xs))
  ≡⟨ refl ⟩
    fv xs i
  ∎

postulate
  lookup-indexMin≤lookup : ∀{n} {xs : Vec ℕ (suc n)} →
    (i : Fin (suc n)) → Vec.lookup xs (indexMin xs) ≤ Vec.lookup xs i

---

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
