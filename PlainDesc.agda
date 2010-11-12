module PlainDesc where
open import Data.Unit
open import Data.Product

data NatTag : Set where
  zz ss : NatTag

data PlainDesc : Set₁ where
  arg : (A : Set) → (A → PlainDesc) → PlainDesc
  rec : PlainDesc → PlainDesc
  ret : PlainDesc

NatPlain : PlainDesc
NatPlain = arg NatTag f where
  f : NatTag → PlainDesc
  f zz = ret
  f ss = rec ret

⟦_⟧ : PlainDesc → Set → Set
⟦ arg A D ⟧ R = Σ A (λ a → ⟦ D a ⟧ R)
⟦ rec D ⟧   R = R × ⟦ D ⟧ R
⟦ ret ⟧     R = ⊤

data PlainData (D : PlainDesc) : Set where
  ⟪_⟫ : ⟦ D ⟧ (PlainData D) → PlainData D

Nat : Set
Nat = PlainData NatPlain

zero : Nat
zero = ⟪ zz , _ ⟫

suc : Nat → Nat
suc n = ⟪ ss , n , _ ⟫

three : Nat
three = suc (suc zero)
