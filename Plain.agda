module Plain where
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Nat

F : Set → Set
F X = ⊤ ⊎ X

record Alg : Set₁ where
  field
    C  : Set
    φ  : F C → C

record IniAlg : Set₁ where
  field
    alg : Alg
    μF  : Set
    ini : F μF → μF
    ⟦φ⟧ : μF → Alg.C alg

μF = ℕ
--           ⊤ ⊎ ℕ → ℕ
[zero,suc] : F μF   → μF
[zero,suc] (inj₁ _) = zero
[zero,suc] (inj₂ n) = n + 1

