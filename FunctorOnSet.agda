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

Orn⇛Desc : {D : Desc} → Orn D → Desc
Orn⇛Desc ret = ret
Orn⇛Desc (rec O) = rec (Orn⇛Desc O)
Orn⇛Desc (arg X Of) = arg X (λ x → Orn⇛Desc (Of x))
Orn⇛Desc (new X Of) = arg X (λ x → Orn⇛Desc (Of x))

mutual
  fold : ∀ {X} {D : Desc} →
    Alg D X → μ D → X
  fold {D = D} φ (init ds) = φ (map-fold D D φ ds)

  map-fold : ∀ {X} (D' D : Desc) →
    Alg D' X → ⟦ D ⟧ (μ D') → ⟦ D ⟧ X
  map-fold D' ret _ ds = ds
  map-fold D' (rec D) φ (d , ds) = fold φ d , map-fold D' D φ ds
  map-fold D' (arg _ Df) φ (x , ds) = x , map-fold D' (Df x) φ ds

Alg-Orn : ∀ {X}
  (D : Desc) →
  Alg D X →
  Orn D
Alg-Orn ret _ = ret
Alg-Orn {X = X} (rec D) φ =
  new X (λ x → rec (Alg-Orn D (λ y → φ (x , y))))
Alg-Orn (arg X Df) φ = arg X (λ x → Alg-Orn (Df x) (λ y → φ (x , y)))

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

----------------------------------------------------

add-Alg : ℕ → Alg ℕ-Desc ℕ
add-Alg n (one , _) = n
add-Alg _ (two , acc , _) = suc acc

_+_ : ℕ → ℕ → ℕ
n + m = fold (add-Alg m) n

concat-Alg : ∀ {X} → List X → Alg (List-Desc X) (List X)
concat-Alg ys (one , _) = ys
concat-Alg _ (two , x , acc , _) = x ∷ acc

_++_ : ∀ {X} → List X → List X → List X
xs ++ ys = fold (concat-Alg ys) xs

----------------------------------------------------

id-ℕ-Alg : Alg ℕ-Desc ℕ
id-ℕ-Alg (one , _) = zero
id-ℕ-Alg (two , acc , _) = suc acc

id-ℕ : ℕ → ℕ
id-ℕ n = fold id-ℕ-Alg n

id-List-Alg : ∀ {X} → Alg (List-Desc X) (List X)
id-List-Alg (one , _) = []
id-List-Alg (two , x , acc , _) = x ∷ acc

id-List : ∀ {X} → List X → List X
id-List xs = fold id-List-Alg xs

----------------------------------------------------

forget-Alg : ∀ {D : Desc}
  (O : Orn D) →
  Alg (Orn⇛Desc O) (μ D)
forget-Alg O ds = init (forget-Alg' O ds)
  where
  forget-Alg' : ∀ {R} {D : Desc}
    (O : Orn D) →
    ⟦ Orn⇛Desc O ⟧ R →
    ⟦ D ⟧ R
  forget-Alg' ret _ = _
  forget-Alg' (rec O) (d , ds) = d , forget-Alg' O ds
  forget-Alg' (arg X Of) (x , ds) = x , forget-Alg' (Of x) ds
  forget-Alg' (new X Of) (x , ds) = forget-Alg' (Of x) ds

forget : {D : Desc}
  (O : Orn D) →
  μ (Orn⇛Desc O) →
  μ D
forget O = fold (forget-Alg O)

length : ∀ {X} → List X → ℕ
length {X} = forget (List-Orn X)
