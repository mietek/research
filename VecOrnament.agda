module OrnamentedVec where

open import Prelude
open import Fin
open import Vec


--------------------------------------------------------------------------------


data All◇ {X P} (`P : ∀ {A : X} → P A → Set) : ∀ {n} → {Ξ : Vec X n}
                                                       → All P Ξ → Set
  where
    ∙ : All◇ `P ∙

    _,_ : ∀ {A n} → {Ξ : Vec X n}
                     {ξ : All P Ξ} {x : P A}
                  → All◇ `P ξ → `P x
                  → All◇ `P (ξ , x)


lookup◇ : ∀ {X P A n i} → {Ξ : Vec X n} {x : P A}
                           {ξ : All P Ξ} {𝒾 : Ξ ∋⟨ i ⟩ A}
                           {`P : ∀ {A} → P A → Set}
                        → All◇ `P ξ → ξ ∋◇⟨ 𝒾 ⟩ x
                        → `P x
lookup◇ (`ξ , `x) zero     = `x
lookup◇ (`ξ , `y) (suc `𝒾) = lookup◇ `ξ `𝒾


mapAll◇ : ∀ {X P n} → {Ξ : Vec X n} {Q : X → Set}
                       {f : ∀ {A} → P A → Q A} {ξ : All P Ξ}
                       {`P : ∀ {A} → P A → Set} {`Q : ∀ {A} → Q A → Set}
                    → (∀ {A} → {x : P A} → `P x → `Q (f x)) → All◇ `P ξ
                    → All◇ `Q (mapAll f ξ)
mapAll◇ `f ∙         = ∙
mapAll◇ `f (`ξ , `x) = mapAll◇ `f `ξ , `f `x


--------------------------------------------------------------------------------
