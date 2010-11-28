module FunctorOnFam where
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Tag : Set where
  ret rec : Tag

data Desc (I : Set) : Set₁ where
  ret : I → Desc I
  rec : I → Desc I → Desc I
  arg : (A : Set) → (A → Desc I) → Desc I

⟦_⟧ : {I : Set} → Desc I → (I → Set) → I → Set
⟦ ret j ⟧ P i = j ≡ i
⟦ rec j D ⟧ P i = P j × ⟦ D ⟧ P i
⟦ arg A Df ⟧ P i = Σ A (λ a → ⟦ Df a ⟧ P i)

data μ {I : Set} (D : Desc I) : I → Set where
  in-Alg : ∀ {i} → ⟦ D ⟧ (μ D) i → μ D i

data Inv {I J : Set} (e : J → I) : I → Set where
  inv : (j : J) → Inv e (e j)

data Orn {I : Set} (J : Set) (e : J → I) : Desc I → Set₁ where
  ret : ∀ {i} → 
    Inv e i → Orn J e (ret i)
  rec : ∀ {i} {D : Desc I} →
    Inv e i → Orn J e D → Orn J e (rec i D)
  arg : (A : Set) → {Df : A → Desc I}  →
    ((a : A) → Orn J e (Df a)) → Orn J e (arg A Df)
  new : {D : Desc I} →
    (A : Set) → (A → Orn J e D) → Orn J e D
