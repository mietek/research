module ListOrnament where

open import Prelude
open import Fin
open import List








--------------------------------------------------------------------------------


data All◇ {X P} (`P : ∀ {A : X} → P A → Set) : ∀ {Ξ} → All P Ξ → Set
  where
    ∙ : All◇ `P ∙

    _,_ : ∀ {Ξ A} → {ξ : All P Ξ} {x : P A}
                  → All◇ `P ξ → `P x
                  → All◇ `P (ξ , x)


lookup◇ : ∀ {X P A} → {Ξ : List X} {x : P A}
                       {ξ : All P Ξ} {𝒾 : Ξ ∋ A}
                       {`P : ∀ {A} → P A → Set}
                    → All◇ `P ξ → ξ ∋⟨ 𝒾 ⟩ x
                    → `P x
lookup◇ (`ξ , `x) zero     = `x
lookup◇ (`ξ , `y) (suc `𝒾) = lookup◇ `ξ `𝒾


lookups◇ : ∀ {X P} → {Ξ Ξ′ : List X} {η : Ξ′ ⊇ Ξ}
                      {ξ : All P Ξ} {ξ′ : All P Ξ′}
                      {`P : ∀ {A} → P A → Set}
                   → All◇ `P ξ′ → ξ′ ⊇⟨ η ⟩ ξ
                   → All◇ `P ξ
lookups◇ ∙         done      = ∙
lookups◇ (`ξ , `x) (drop `η) = lookups◇ `ξ `η
lookups◇ (`ξ , `x) (keep `η) = lookups◇ `ξ `η , `x


mapAll◇ : ∀ {X P} → {Ξ : List X} {Q : X → Set}
                     {f : ∀ {A} → P A → Q A} {ξ : All P Ξ}
                     {`P : ∀ {A} → P A → Set} {`Q : ∀ {A} → Q A → Set}
                  → (∀ {A} → {x : P A} → `P x → `Q (f x)) → All◇ `P ξ
                  → All◇ `Q (mapAll f ξ)
mapAll◇ `f ∙         = ∙
mapAll◇ `f (`ξ , `x) = mapAll◇ `f `ξ , `f `x


--------------------------------------------------------------------------------
