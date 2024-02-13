module Isomorphism where

open import Prelude


----------------------------------------------------------------------------------------------------

-- isomorphism
infix 4 _≃_
record _≃_ {𝓍 𝓎} (X : Set 𝓍) (Y : Set 𝓎) : Set (𝓍 ⊔ 𝓎) where
  field
    to      : X → Y
    from    : Y → X
    from∘to : ∀ (x : X) → (from ∘ to) x ≡ x
    to∘from : ∀ (y : Y) → (to ∘ from) y ≡ y

open _≃_

refl≃ : ∀ {𝓍} {X : Set 𝓍} → X ≃ X
refl≃ = record
          { to      = id
          ; from    = id
          ; from∘to = λ x → refl
          ; to∘from = λ y → refl
          }

sym≃ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → X ≃ Y → Y ≃ X
sym≃ eq = record
            { to      = from eq
            ; from    = to eq
            ; from∘to = to∘from eq
            ; to∘from = from∘to eq
            }

trans≃ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : Set 𝓏} → X ≃ Y → Y ≃ Z → X ≃ Z
trans≃ eq eq′ = record
                  { to      = to eq′ ∘ to eq
                  ; from    = from eq ∘ from eq′
                  ; from∘to = λ x → from eq & from∘to eq′ (to eq x)
                                   ⋮ from∘to eq x
                  ; to∘from = λ y → to eq′ & to∘from eq (from eq′ y)
                                   ⋮ to∘from eq′ y
                  }

≡→≃ : ∀ {𝓍} {X X′ : Set 𝓍} → X ≡ X′ → X ≃ X′
≡→≃ refl = refl≃

module ≃-Reasoning where
  infix 1 begin_
  begin_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → X ≃ Y → X ≃ Y
  begin_ eq = eq

  infixr 2 _≃⟨_⟩_
  _≃⟨_⟩_ : ∀ {𝓍 𝓎 𝓏} (X : Set 𝓍) {Y : Set 𝓎} {Z : Set 𝓏} → X ≃ Y → Y ≃ Z → X ≃ Z
  X ≃⟨ eq ⟩ eq′ = trans≃ eq eq′

  infixr 2 _≃˘⟨_⟩_
  _≃˘⟨_⟩_ : ∀ {𝓍 𝓎 𝓏} (X : Set 𝓍) {Y : Set 𝓎} {Z : Set 𝓏} → Y ≃ X → Y ≃ Z → X ≃ Z
  X ≃˘⟨ eq ⟩ eq′ = trans≃ (sym≃ eq) eq′

  infixr 2 _≡⟨⟩_
  _≡⟨⟩_ : ∀ {𝓍 𝓎} (X : Set 𝓍) {Y : Set 𝓎} → X ≃ Y → X ≃ Y
  X ≡⟨⟩ eq = eq

  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ : ∀ {𝓍} {𝓎} (X : Set 𝓍) {X′ : Set 𝓍} {Y : Set 𝓎} → X ≡ X′ → X′ ≃ Y → X ≃ Y
  X ≡⟨ eq ⟩ eq′ = trans≃ (≡→≃ eq) eq′

  infixr 2 _≡˘⟨_⟩_
  _≡˘⟨_⟩_ : ∀ {𝓍} {𝓎} (X : Set 𝓍) {X′ : Set 𝓍} {Y : Set 𝓎} → X′ ≡ X → X′ ≃ Y → X ≃ Y
  X ≡˘⟨ eq ⟩ eq′ = trans≃ (≡→≃ (sym eq)) eq′

  infix 3 _∎
  _∎ : ∀ {𝓍} (X : Set 𝓍) → X ≃ X
  X ∎ = refl≃


----------------------------------------------------------------------------------------------------

-- embedding
infix 4 _≲_
record _≲_ {𝓍 𝓎} (X : Set 𝓍) (Y : Set 𝓎) : Set (𝓍 ⊔ 𝓎) where
  field
    to      : X → Y
    from    : Y → X
    from∘to : ∀ (x : X) → (from ∘ to) x ≡ x

open _≲_

refl≲ : ∀ {𝓍} {X : Set 𝓍} → X ≲ X
refl≲ = record
          { to      = id
          ; from    = id
          ; from∘to = λ x → refl
          }

trans≲ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : Set 𝓏} → X ≲ Y → Y ≲ Z → X ≲ Z
trans≲ leq leq′ = record
                    { to      = to leq′ ∘ to leq
                    ; from    = from leq ∘ from leq′
                    ; from∘to = λ x → from leq & from∘to leq′ (to leq x)
                                     ⋮ from∘to leq x
                    }

antisym≲ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (leq : X ≲ Y) (leq′ : Y ≲ X) →
           to leq ≡ from leq′ → from leq ≡ to leq′ → X ≃ Y
antisym≲ leq leq′ eq eq′ = record
                             { to      = to leq
                             ; from    = from leq
                             ; from∘to = from∘to leq
                             ; to∘from = λ y → to leq & congapp eq′ y
                                              ⋮ congapp eq (to leq′ y)
                                              ⋮ from∘to leq′ y
                             }

≃→≲ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → X ≃ Y → X ≲ Y
≃→≲ X≃Y = record
             { to      = to X≃Y
             ; from    = from X≃Y
             ; from∘to = from∘to X≃Y
             }

≡→≲ : ∀ {𝓍} {X X′ : Set 𝓍} → X ≡ X′ → X ≲ X′
≡→≲ = ≃→≲ ∘ ≡→≃

module ≲-Reasoning where
  infix 1 begin_
  begin_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → X ≲ Y → X ≲ Y
  begin_ leq = leq

  infixr 2 _≲⟨_⟩_
  _≲⟨_⟩_ : ∀ {𝓍 𝓎 𝓏} (X : Set 𝓍) {Y : Set 𝓎} {Z : Set 𝓏} → X ≲ Y → Y ≲ Z → X ≲ Z
  X ≲⟨ leq ⟩ leq′ = trans≲ leq leq′

  infixr 2 _≃⟨_⟩_
  _≃⟨_⟩_ : ∀ {𝓍 𝓎 𝓏} (X : Set 𝓍) {Y : Set 𝓎} {Z : Set 𝓏} → X ≃ Y → Y ≲ Z → X ≲ Z
  X ≃⟨ eq ⟩ leq′ = trans≲ (≃→≲ eq) leq′

  infixr 2 _≃˘⟨_⟩_
  _≃˘⟨_⟩_ : ∀ {𝓍 𝓎 𝓏} (X : Set 𝓍) {Y : Set 𝓎} {Z : Set 𝓏} → Y ≃ X → Y ≲ Z → X ≲ Z
  X ≃˘⟨ eq ⟩ leq′ = trans≲ (≃→≲ (sym≃ eq)) leq′

  infixr 2 _≡⟨⟩_
  _≡⟨⟩_ : ∀ {𝓍 𝓎} (X : Set 𝓍) {Y : Set 𝓎} → X ≲ Y → X ≲ Y
  X ≡⟨⟩ leq = leq

  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ : ∀ {𝓍} {𝓎} (X : Set 𝓍) {X′ : Set 𝓍} {Y : Set 𝓎} → X ≡ X′ → X′ ≲ Y → X ≲ Y
  X ≡⟨ eq ⟩ leq′ = trans≲ (≡→≲ eq) leq′

  infixr 2 _≡˘⟨_⟩_
  _≡˘⟨_⟩_ : ∀ {𝓍} {𝓎} (X : Set 𝓍) {X′ : Set 𝓍} {Y : Set 𝓎} → X′ ≡ X → X′ ≲ Y → X ≲ Y
  X ≡˘⟨ eq ⟩ leq′ = trans≲ (≡→≲ (sym eq)) leq′

  infix 3 _∎
  _∎ : ∀ {𝓍} (X : Set 𝓍) → X ≲ X
  X ∎ = refl≲


----------------------------------------------------------------------------------------------------
