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

List-Orn : Set → Orn ⊤ _ NatDesc
List-Orn X = arg NatTag f where
  f : (_ : NatTag) → Orn _ _ _
  f zz = ret (inv _)
  f ss = new X (λ _ → rec (inv _) (ret (inv _)))

orn : ∀ {J I} {e : J → I} {D : Desc I} →
  Orn J e D → Desc J
orn (arg A Of) = arg A (λ a → orn (Of a))
orn (rec (inv j) O) = rec j (orn O)
orn (ret (inv j)) = ret j
orn (new A Of) = arg A (λ a → orn (Of a))

List-Desc : Set → Desc ⊤
List-Desc X = orn (List-Orn X)

List : Set → Set
List X = μ (List-Desc X) _

nil : ∀ {X} → List X
nil = ⟪ zz , refl ⟫

cons : ∀ {X} → X → List X → List X
cons x xs = ⟪ ss , x , xs , refl ⟫

Fin-Orn : Orn Nat _ NatDesc
Fin-Orn = arg NatTag f where
  f : (_ : NatTag) → Orn _ _ _
  f zz = new Nat (λ n → ret (inv n))
  f ss = new Nat (λ n → rec (inv n) (ret (inv (suc n))))

Fin-Desc : Desc Nat
Fin-Desc = orn Fin-Orn

Fin : Nat → Set
Fin n = μ Fin-Desc n
