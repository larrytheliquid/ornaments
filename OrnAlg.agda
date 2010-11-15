module OrnAlg where
open import Data.Unit
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

Alg-orn : ∀ {I J}
  (D : Desc I) →
  Alg D J →
  Orn (Σ I J) proj₁ D
Alg-orn (arg A Df) φ = arg A (λ a → Alg-orn (Df a) (λ x → φ (a , x)))
Alg-orn {J = J} (rec i D) φ =
  new (J i) (λ j → rec (inv (i , j)) (Alg-orn D (λ x → φ (j , x))))
Alg-orn (ret i) φ = ret (inv (i , φ refl))
