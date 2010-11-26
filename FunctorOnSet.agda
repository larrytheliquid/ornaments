module FunctorOnSet where
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Two : Set where
  one two : Two

data Desc : Set₁ where
  ret : Desc
  rec : Desc → Desc
  arg : (X : Set) → (X → Desc) → Desc

⟦_⟧ : Desc → Set → Set
⟦ ret ⟧     R = ⊤
⟦ rec D ⟧   R = R × ⟦ D ⟧ R
⟦ arg X D ⟧ R = Σ X (λ x → ⟦ D x ⟧ R)

data μ (D : Desc) : Set where
  init : ⟦ D ⟧ (μ D) → μ D

Alg : Desc → Set → Set
Alg D X = ⟦ D ⟧ X → X

data Orn : Desc → Set₁ where
  ret :
    Orn ret
  rec : {D : Desc} →
    Orn D → Orn (rec D)
  arg : (X : Set) → {Df : X → Desc}  →
    ((x : X) → Orn (Df x)) → Orn (arg X Df)
  new : {D : Desc} →
    (X : Set) → (X → Orn D) → Orn D

Alg⇒Orn : ∀ {X} {D : Desc} →
  Alg D X →
  Orn D
Alg⇒Orn {_} {ret} _ = ret
Alg⇒Orn {X} {rec D} φ =
  new X (λ x → rec (Alg⇒Orn (λ y → φ (x , y))))
Alg⇒Orn {_} {arg X Df} φ = arg X (λ x → Alg⇒Orn (λ y → φ (x , y)))

Orn⇒Desc : {D : Desc} → Orn D → Desc
Orn⇒Desc ret = ret
Orn⇒Desc (rec O) = rec (Orn⇒Desc O)
Orn⇒Desc (arg X Of) = arg X (λ x → Orn⇒Desc (Of x))
Orn⇒Desc (new X Of) = arg X (λ x → Orn⇒Desc (Of x))

mutual
  fold : ∀ {X} {D : Desc} →
    Alg D X → μ D → X
  fold {D = D} φ (init ds) = φ (map-fold D D φ ds)

  map-fold : ∀ {X} (D' D : Desc) →
    Alg D' X → ⟦ D ⟧ (μ D') → ⟦ D ⟧ X
  map-fold D' ret _ ds = ds
  map-fold D' (rec D) φ (d , ds) = fold φ d , map-fold D' D φ ds
  map-fold D' (arg _ Df) φ (x , ds) = x , map-fold D' (Df x) φ ds

id : {D : Desc} → μ D → μ D
id x = fold init x

----------------------------------------------------

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

----------------------------------------------------

init-ℕ-Alg : Alg ℕ-Desc ℕ
init-ℕ-Alg = init

----------------------------------------------------

List-Orn : Orn ℕ-Desc
List-Orn = Alg⇒Orn init-ℕ-Alg

List-Desc : Desc 
List-Desc = Orn⇒Desc List-Orn

List : Set
List = μ List-Desc

[] : List
[] = init (one , _)

_∷_ : ℕ → List → List
x ∷ xs = init (two , x , xs , _)

----------------------------------------------------

init-List-Alg : Alg List-Desc List
init-List-Alg = init

----------------------------------------------------

forget-Alg : ∀ {D : Desc}
  (O : Orn D) →
  Alg (Orn⇒Desc O) (μ D)
forget-Alg O ds = init (forget-Alg' O ds)
  where
  forget-Alg' : ∀ {R} {D : Desc}
    (O : Orn D) →
    ⟦ Orn⇒Desc O ⟧ R →
    ⟦ D ⟧ R
  forget-Alg' ret _ = _
  forget-Alg' (rec O) (d , ds) = d , forget-Alg' O ds
  forget-Alg' (arg X Of) (x , ds) = x , forget-Alg' (Of x) ds
  forget-Alg' (new X Of) (x , ds) = forget-Alg' (Of x) ds

forget : {D : Desc}
  (O : Orn D) →
  μ (Orn⇒Desc O) →
  μ D
forget O = fold (forget-Alg O)

length : List → ℕ
length = forget List-Orn

----------------------------------------------------

Vec-Orn : Orn List-Desc
Vec-Orn = Alg⇒Orn (forget-Alg List-Orn)

Vec-Desc : Desc
Vec-Desc = Orn⇒Desc Vec-Orn

Vec : Set
Vec = μ Vec-Desc

nil : Vec
nil = init (one , _)

cons : ℕ → ℕ → Vec → Vec
cons n x xs = init (two , x , n , xs , _)

