module Orn where
open import Data.Unit
open import Data.Product
open import Data.Function
open import Relation.Binary.PropositionalEquality
open import Desc

! : {A : Set} → A → ⊤
! = const tt

data Inv {I J : Set} (e : J → I) : I → Set where
  inv : (j : J) → Inv e (e j)

data Orn {I : Set} (J : Set) (e : J → I) : Desc I → Set₁ where
  arg : (A : Set) → {Df : A → Desc I}  →
    ((a : A) → Orn J e (Df a)) → Orn J e (arg A Df)
  rec : ∀ {i} {D : Desc I} →
    Inv e i → Orn J e D → Orn J e (rec i D)
  ret : ∀ {i} → 
    Inv e i → Orn J e (ret i)
  new : {D : Desc I} →
    (A : Set) → (A → Orn J e D) → Orn J e D

ListOrn : Set → Orn ⊤ _ NatDesc
ListOrn X = arg NatTag f where
  f : (_ : NatTag) → Orn _ _ _
  f zz = ret (inv _)
  f ss = new X (λ _ → rec (inv _) (ret (inv _)))


