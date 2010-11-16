module Desc where
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

data NatTag : Set where
  zz ss : NatTag

data Desc (I : Set) : Set₁ where
  arg : (A : Set) → (A → Desc I) → Desc I
  rec : I → Desc I → Desc I
  ret : I → Desc I

⟦_⟧ : {I : Set} → Desc I → (I → Set) → I → Set
⟦ arg A Df ⟧ R i = Σ A (λ a → ⟦ Df a ⟧ R i)
⟦ rec h D ⟧ R i = R h × ⟦ D ⟧ R i
⟦ ret o ⟧ R i = o ≡ i

data μ {I : Set} (D : Desc I) : I → Set where
  ⟪_⟫ : ∀ {i} → ⟦ D ⟧ (μ D) i → μ D i

NatDesc : Desc ⊤
NatDesc = arg NatTag f where
  f : NatTag → Desc ⊤
  f zz = ret _
  f ss = rec _ (ret _)

Nat : Set
Nat = μ NatDesc _

zero : Nat
zero = ⟪ zz , refl ⟫

suc : Nat → Nat
suc n = ⟪ ss , n , refl ⟫

-- ListDesc : Set → Desc ⊤
-- ListDesc X = arg NatTag f where
--   f : NatTag → Desc ⊤
--   f zz = ret _
--   f ss = arg X (λ _ → rec _ (ret _))

-- List : Set → Set
-- List X = μ (ListDesc X) _

-- nil : ∀ {X} → List X
-- nil = ⟪ zz , refl ⟫

-- cons : ∀ {X} → X → List X → List X
-- cons x xs = ⟪ ss , x , xs , refl ⟫

-- VecDesc : Set → Desc Nat
-- VecDesc X = arg NatTag f where
--   g : Nat → Desc Nat
--   g n = rec n (ret (suc n))

--   h : X → Desc Nat
--   h _ = arg Nat g

--   f : NatTag → Desc Nat
--   f zz = ret zero
--   f ss = arg X h

-- Vec : Set → Nat → Set
-- Vec X n = μ (VecDesc X) n

-- vnil : ∀ {X} → Vec X zero
-- vnil = ⟪ zz , refl ⟫

-- vcons : ∀ {n X} → X → Vec X n → Vec X (suc n)
-- vcons {n} x xs = ⟪ ss , x , n , xs , refl ⟫

