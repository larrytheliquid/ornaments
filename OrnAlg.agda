module OrnAlg where
open import Data.Unit hiding (_≤_)
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Desc
open import Alg
open import Orn

orn-Alg' : ∀ {I J e} {D : Desc I} {R : I → Set}
  (O : Orn J e D) →
  ⟦ orn O ⟧ (λ x → R (e x)) ⊆
  (λ x → ⟦ D ⟧ R (e x))
orn-Alg' (arg A Of) (a , ds) = a , orn-Alg' (Of a) ds
orn-Alg' (rec (inv j) O) (d , ds) = d , orn-Alg' O ds
orn-Alg' (ret (inv j)) refl = refl
orn-Alg' (new A Of) (a , ds) = orn-Alg' (Of a) ds

orn-Alg : ∀ {I J e} {D : Desc I}
  (O : Orn J e D) →
  Alg (orn O) (λ x → μ D (e x))
orn-Alg O ds = ⟪ orn-Alg' O ds ⟫

forget : ∀ {I J e} {D : Desc I} 
  (O : Orn J e D) →
  μ (orn O) ⊆ (λ x → μ D (e x))
forget O = fold (orn-Alg O)

length : ∀ {X} → List X → Nat
length {X} = forget (List-Orn X)

Alg-orn : ∀ {I J}
  (D : Desc I) →
  Alg D J →
  Orn (Σ I J) proj₁ D
Alg-orn (arg A Df) φ = arg A (λ a → Alg-orn (Df a) (λ x → φ (a , x)))
Alg-orn {J = J} (rec i D) φ =
  new (J i) (λ j → rec (inv (i , j)) (Alg-orn D (λ x → φ (j , x))))
Alg-orn (ret i) φ = ret (inv (i , φ refl))

Vec-Orn : (X : Set) → Orn (⊤ × Nat) proj₁ (List-Desc X)
Vec-Orn X = Alg-orn (List-Desc X) (orn-Alg (List-Orn X))

Vec-Desc : (X : Set) → Desc (⊤ × Nat)
Vec-Desc X = orn (Vec-Orn X)

Vec : Set → Nat → Set
Vec X n = μ (Vec-Desc X) (_ , n)

vnil : ∀ {X} → Vec X zero
vnil = ⟪ zz , refl ⟫

vcons : ∀ {n X} → X → Vec X n → Vec X (suc n)
vcons {n} x xs = ⟪ ss , x , n , xs , refl ⟫

concat-Alg : ∀ {n X} → Vec X n → Alg (Vec-Desc X) (λ m → Vec X (proj₂ m + n))
concat-Alg ys (zz , refl) = ys
concat-Alg _ (ss , x , _ , acc , refl) = vcons x acc

_++_ : ∀ {X m n} → Vec X m → Vec X n → Vec X (m + n)
xs ++ ys = fold (concat-Alg ys) xs

to-list : ∀ {X n} → Vec X n → List X
to-list {X} = forget (Vec-Orn X)

Ge-Orn : Nat → Orn (⊤ × Nat) proj₁ NatDesc
Ge-Orn n = Alg-orn NatDesc (add-Alg n)

Ge-Desc : Nat → Desc (⊤ × Nat)
Ge-Desc n = orn (Ge-Orn n)

Ge : Nat → Nat → Set
Ge m n = μ (Ge-Desc n) (_ , m)

gez : {m : Nat} → Ge m m
gez {m} = ⟪ zz , refl ⟫

ges : {m n : Nat} → Ge m n → Ge (suc m) n
ges p = ⟪ ss , _ , p , refl ⟫
