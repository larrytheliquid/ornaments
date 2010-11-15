module Alg where
open import Data.Unit
open import Data.Product hiding (map)
open import Data.Function
open import Relation.Binary.PropositionalEquality
open import Desc

_⊆_ : {I : Set} → (I → Set) → (I → Set) → Set
_⊆_ X Y = {i : _} → X i → Y i

Alg : ∀ {I} → Desc I → (I → Set) → Set
Alg D X = ⟦ D ⟧ X ⊆ X

map : ∀ {I X Y}
  (D : Desc I) → (X ⊆ Y) → ⟦ D ⟧ X ⊆ ⟦ D ⟧ Y
map (arg _ D) f (a , ds) = a , map (D a) f ds
map (rec _ D) f (d , ds) = f d , map D f ds
map (ret _) _ ds = ds

-- fold : ∀ {I X} {D : Desc I} →
--   ⟦ D ⟧ X ⊆ X → Data D ⊆ X
-- fold {D = D} φ ⟪ ds ⟫ = φ (map D (fold φ) ds)

mutual
  fold : ∀ {I X} {D : Desc I} →
    ⟦ D ⟧ X ⊆ X → Data D ⊆ X
  fold {D = D} φ ⟪ ds ⟫ = φ (map-fold D D φ ds)

  map-fold : ∀ {I X} (D' D : Desc I) →
    (⟦ D' ⟧ X ⊆ X) → ⟦ D ⟧ (Data D') ⊆ ⟦ D ⟧ X
  map-fold D' (arg _ D) φ (a , ds) = a , map-fold D' (D a) φ ds
  map-fold D' (rec _ D) φ (d , ds) = fold φ d , map-fold D' D φ ds
  map-fold D' (ret _) _ ds = ds

-- Nat → ⟦ NatDesc ⟧ (λ _ → Nat) → (λ _ → Nat)
add-Alg : Nat → Alg NatDesc (λ _ → Nat)
add-Alg n (zz , refl) = n
add-Alg _ (ss , acc , refl) = suc acc

_+_ : Nat → Nat → Nat
n + m = fold (add-Alg m) n

-- Vec here is really shorthand for fixpoint Data = ⟪ ⟦VecDesc X⟧ ⟪⟦VecDesc X⟧ etc⟫ ⟫
-- Vec X n → ⟦ VecDesc X ⟧ (λ m → Vec X (m + n)) → (λ m → Vec X (m + n))
concat-Alg : ∀ {n X} → Vec X n → Alg (VecDesc X) (λ m → Vec X (m + n))
concat-Alg ys (zz , refl) = ys
concat-Alg _ (ss , x , _ , acc , refl) = vcons x acc

_++_ : ∀ {X m n} → Vec X m → Vec X n → Vec X (m + n)
xs ++ ys = fold (concat-Alg ys) xs
