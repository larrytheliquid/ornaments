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

----------------------------------------------------

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

----------------------------------------------------

Env-Orn : {X : Set} → (P : X → Set) →
  Orn (List X) _ (List-Desc X)
Env-Orn P = arg Tag f where
  f : (_ : Tag) → Orn _ _ _
  f ret = ret (inv nil)
  f rec = arg _ λ x → (new (List _)
    λ xs → rec (inv xs) (ret (inv (cons x xs))))

Env-Desc : {X : Set} → (P : X → Set) → Desc (List X)
Env-Desc P = Orn⇒Desc (Env-Orn P)

Env : {X : Set} → (P : X → Set) → List X → Set
Env P xs = μ (Env-Desc P) xs

----------------------------------------------------

Fin-Orn : Orn ℕ _ ℕ-Desc
Fin-Orn = arg Tag f where
  f : (_ : Tag) → Orn _ _ _
  f ret = new ℕ (λ n → ret (inv (suc n)))
  f rec = new ℕ (λ n → rec (inv n) (ret (inv (suc n))))

Fin-Desc : Desc ℕ
Fin-Desc = Orn⇒Desc Fin-Orn

Fin : ℕ → Set
Fin n = μ Fin-Desc n

----------------------------------------------------

Vec-Orn : (X : Set) → Orn ℕ _ (List-Desc X)
Vec-Orn X = arg Tag f where
  f : (_ : Tag) → Orn _ _ _
  f ret = ret (inv zero)
  f rec = arg X (λ _ → new ℕ
    (λ n → rec (inv n) (ret (inv (suc n)))))

Vec-Desc : Set → Desc ℕ
Vec-Desc X = Orn⇒Desc (Vec-Orn X)

Vec : Set → ℕ → Set
Vec X n = μ (Vec-Desc X) n

vnil : ∀ {X} → Vec X zero
vnil = in-Alg (ret , refl)

vcons : ∀ {n X} → X → Vec X n → Vec X (suc n)
vcons {n} x xs = in-Alg (rec , x , n , xs , refl)

lookup : {X : Set} {n : ℕ} → Fin n → Vec X n → X
lookup (in-Alg (ret , _ , refl)) (in-Alg (ret , ()))
lookup (in-Alg (ret , _ , refl)) (in-Alg (rec , x , _)) = x
lookup (in-Alg (rec , n , i , refl)) (in-Alg (ret , ()))
lookup (in-Alg (rec , n , i , refl)) (in-Alg (rec , _ , .n , xs , refl)) = lookup i xs
