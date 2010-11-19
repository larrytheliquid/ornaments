module FunctorOnSet where
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Two : Set where
  one two : Two

data Desc : Set₁ where
  arg : (X : Set) → (X → Desc) → Desc
  rec : Desc → Desc
  ret : Desc

⟦_⟧ : Desc → Set → Set
⟦ arg X D ⟧ R = Σ X (λ x → ⟦ D x ⟧ R)
⟦ rec D ⟧   R = R × ⟦ D ⟧ R
⟦ ret ⟧     R = ⊤

data μ (D : Desc) : Set where
  init : ⟦ D ⟧ (μ D) → μ D

data Orn : Desc → Set₁ where
  arg : (X : Set) → {Df : X → Desc}  →
    ((x : X) → Orn (Df x)) → Orn (arg X Df)
  rec : {D : Desc} →
    Orn D → Orn (rec D)
  ret :
    Orn ret
  new : {D : Desc} →
    (X : Set) → (X → Orn D) → Orn D

Orn⇛Desc : {D : Desc} → Orn D → Desc
Orn⇛Desc (arg X Of) = arg X (λ x → Orn⇛Desc (Of x))
Orn⇛Desc (rec O) = rec (Orn⇛Desc O)
Orn⇛Desc ret = ret
Orn⇛Desc (new X Of) = arg X (λ x → Orn⇛Desc (Of x))

ℕ-Desc : Desc
ℕ-Desc = arg Two f where
  f : Two → Desc
  f one = ret
  f two = rec ret

ℕ : Set
ℕ = μ ℕ-Desc

zero : ℕ
zero = init (one , _)

suc : ℕ → ℕ
suc n = init (two , n , _)

List-Orn : Set → Orn ℕ-Desc
List-Orn X = arg Two f where
  f : (_ : Two) → Orn _
  f one = ret
  f two = new X (λ _ → rec ret)

List-Desc : Set → Desc
List-Desc X = Orn⇛Desc (List-Orn X)

List : Set → Set
List X = μ (List-Desc X)

[] : ∀ {X} → List X
[] = init (one , _)

_∷_ : ∀ {X} → X → List X → List X
x ∷ xs = init (two , x , xs , _)

