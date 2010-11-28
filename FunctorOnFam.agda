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

Orn⇒Desc : ∀ {J I} {e : J → I} {D : Desc I} →
  Orn J e D → Desc J
Orn⇒Desc (ret (inv j)) = ret j
Orn⇒Desc (rec (inv j) O) = rec j (Orn⇒Desc O)
Orn⇒Desc (arg A Of) = arg A (λ a → Orn⇒Desc (Of a))
Orn⇒Desc (new A Of) = arg A (λ a → Orn⇒Desc (Of a))

----------------------------------------------------

ℕ-Desc : Desc ⊤
ℕ-Desc = arg Tag f where
  f : Tag → Desc _
  f ret = ret _
  f rec = rec _ (ret _)

ℕ : Set
ℕ = μ ℕ-Desc _

zero : ℕ
zero = in-Alg (ret , refl)

suc : ℕ → ℕ
suc n = in-Alg (rec , n , refl)

Fin-Orn : Orn ℕ _ ℕ-Desc
Fin-Orn = arg Tag f where
  f : (_ : Tag) → Orn _ _ _
  f ret = new ℕ (λ n → ret (inv n))
  f rec = new ℕ (λ n → rec (inv n) (ret (inv (suc n))))

List-Orn : Set → Orn ⊤ _ ℕ-Desc
List-Orn X = arg Tag f where
  f : (_ : Tag) → Orn _ _ _
  f ret = ret (inv _)
  f rec = new X (λ _ → rec (inv _) (ret (inv _)))

List-Desc : Set → Desc ⊤
List-Desc X = Orn⇒Desc (List-Orn X)

List : Set → Set
List X = μ (List-Desc X) _

nil : ∀ {X} → List X
nil = in-Alg (ret , refl)

cons : ∀ {X} → X → List X → List X
cons x xs = in-Alg (rec , x , xs , refl)
