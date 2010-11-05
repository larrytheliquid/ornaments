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

NatDesc : Desc ⊤
NatDesc = arg NatTag f where
  f : NatTag → Desc ⊤
  f zz = ret _
  f ss = rec _ (ret _)

⟦_⟧ : {I : Set} → Desc I → (I → Set) → I → Set
⟦ arg A D ⟧ R i = Σ A (λ a → ⟦ D a ⟧ R i)
⟦ rec h D ⟧ R i = R h × ⟦ D ⟧ R i
⟦ ret o ⟧ R i = o ≡ i

data Data {I : Set} (D : Desc I) : I → Set where
  ⟪_⟫ : ∀ {i} → ⟦ D ⟧ (Data D) i → Data D i

Nat : Set
Nat = Data NatDesc _

zero : Nat
zero = ⟪ zz , refl ⟫

suc : Nat → Nat
suc n = ⟪ ss , n , refl ⟫

VecDesc : Set → Desc Nat
VecDesc X = arg NatTag f where
  g : Nat → Desc Nat
  g n = rec n (ret (suc n))

  h : X → Desc Nat
  h _ = arg Nat g

  f : NatTag → Desc Nat
  f zz = ret zero
  f ss = arg X h

Vec : Set → Nat → Set
Vec X n = Data (VecDesc X) n

nil : ∀ {X} → Vec X zero
nil = ⟪ zz , refl ⟫

cons : ∀ {n X} → X → Vec X n → Vec X (suc n)
cons {n} x xs = ⟪ ss , x , n , xs , refl ⟫


