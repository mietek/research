----------------------------------------------------------------------------------------------------

-- bits of naive category theory

module GAN where

import Prelude
open Prelude hiding (_∘_ ; _⨾_ ; id)


----------------------------------------------------------------------------------------------------

record Category (ℴ 𝓂 : Level) : Set (lsuc (ℴ ⊔ 𝓂)) where
  field
    Obj  : Set ℴ
    _▻_  : ∀ (x y : Obj) → Set 𝓂
    id   : ∀ {x} → x ▻ x
    _∘_  : ∀ {x y z} (q : y ▻ z) (p : x ▻ y) → x ▻ z
    lid▻ : ∀ {x y} (p : y ▻ x) → id ∘ p ≡ p
    rid▻ : ∀ {x y} (p : y ▻ x) → p ∘ id ≡ p
    ass▻ : ∀ {w x y z} (r : y ▻ z) (q : x ▻ y) (p : w ▻ x) → r ∘ (q ∘ p) ≡ (r ∘ q) ∘ p

  _◅_ : ∀ (y x : Obj) → Set 𝓂
  y ◅ x = x ▻ y

  _⨾_ : ∀ {x y z} (p : x ▻ y) (q : y ▻ z) → x ▻ z
  p ⨾ q = q ∘ p

  field
    ◅ssa : ∀ {w x y z} (r : y ◅ z) (q : x ◅ y) (p : w ◅ x) → r ⨾ (q ⨾ p) ≡ (r ⨾ q) ⨾ p

-- opposite
_ᵒᵖ : ∀ {ℴ 𝓂} (C : Category ℴ 𝓂) → Category ℴ 𝓂
_ᵒᵖ C = record
          { Obj  = C.Obj
          ; _▻_  = flip C._▻_
          ; id   = C.id
          ; _∘_  = flip C._∘_
          ; lid▻ = C.rid▻
          ; rid▻ = C.lid▻
          ; ass▻ = C.◅ssa
          ; ◅ssa = C.ass▻
          }
        where
          private
            module C = Category C

⟪Set⟫ : ∀ (𝓍 : Level) → Category (lsuc 𝓍) 𝓍
⟪Set⟫ 𝓍 = record
            { Obj  = Set 𝓍
            ; _▻_  = λ X Y → X → Y
            ; id   = Prelude.id
            ; _∘_  = λ q p → q Prelude.∘ p
            ; lid▻ = λ p → refl
            ; rid▻ = λ p → refl
            ; ass▻ = λ r q p → refl
            ; ◅ssa = λ r q p → refl
            }

⟪Set₀⟫ : Category (lsuc lzero) lzero
⟪Set₀⟫ = ⟪Set⟫ lzero


----------------------------------------------------------------------------------------------------

record Functor {ℴ₁ ℴ₂ 𝓂₁ 𝓂₂} (C : Category ℴ₁ 𝓂₁) (D : Category ℴ₂ 𝓂₂) :
    Set (ℴ₁ ⊔ ℴ₂ ⊔ 𝓂₁ ⊔ 𝓂₂) where
  private
    module C = Category C
    module D = Category D

  field
    ƒObj : ∀ (x : C.Obj) → D.Obj
    ƒ    : ∀ {x y} (p : x C.▻ y) → (ƒObj x) D.▻ (ƒObj y)
    idƒ  : ∀ {x} → ƒ C.id ≡ D.id :> (ƒObj x D.▻ ƒObj x)
    _∘ƒ_ : ∀ {x y z} (q : y C.▻ z) (p : x C.▻ y) → ƒ (q C.∘ p) ≡ (ƒ q) D.∘ (ƒ p)

  -- opposite
  op : Functor (C ᵒᵖ) (D ᵒᵖ)
  op = record
         { ƒObj = ƒObj
         ; ƒ    = ƒ
         ; idƒ  = idƒ
         ; _∘ƒ_ = flip _∘ƒ_
         }

ƒId : ∀ {ℴ 𝓂} (C : Category ℴ 𝓂) → Functor C C
ƒId C = record
          { ƒObj = Prelude.id
          ; ƒ    = Prelude.id
          ; idƒ  = refl
          ; _∘ƒ_ = λ q p → refl
          }

Presheaf : ∀ {ℴ 𝓂} (C : Category ℴ 𝓂) (𝓍 : Level) → Set (ℴ ⊔ 𝓂 ⊔ lsuc 𝓍)
Presheaf C 𝓍 = Functor (C ᵒᵖ) (⟪Set⟫ 𝓍)


----------------------------------------------------------------------------------------------------

-- natural transformation
record NatTrans {ℴ₁ ℴ₂ 𝓂₁ 𝓂₂} {C : Category ℴ₁ 𝓂₁} {D : Category ℴ₂ 𝓂₂} (F G : Functor C D) :
    Set (ℴ₁ ⊔ ℴ₂ ⊔ 𝓂₁ ⊔ 𝓂₂) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G

  field
    ν    : ∀ (x : C.Obj) → (F.ƒObj x) D.▻ (G.ƒObj x)
    natν : ∀ (x y : C.Obj) (p : x C.▻ y) → ν y D.∘ F.ƒ p ≡ G.ƒ p D.∘ ν x

  -- opposite
  op : NatTrans G.op F.op
  op = record
         { ν    = ν
         ; natν = λ x y f → natν y x f ⁻¹
         }


----------------------------------------------------------------------------------------------------

-- isomorphism
infix 4 _≃_
record _≃_ {𝓍 𝓎} (X : Set 𝓍) (Y : Set 𝓎) : Set (𝓍 ⊔ 𝓎) where
  field
    to      : X → Y
    from    : Y → X
    from∘to : ∀ (x : X) → (from Prelude.∘ to) x ≡ x
    to∘from : ∀ (y : Y) → (to Prelude.∘ from) y ≡ y

open _≃_

refl≃ : ∀ {𝓍} {X : Set 𝓍} → X ≃ X
refl≃ = record
          { to      = Prelude.id
          ; from    = Prelude.id
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
                  { to      = to eq′ Prelude.∘ to eq
                  ; from    = from eq Prelude.∘ from eq′
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
  begin eq = eq

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
    from∘to : ∀ (x : X) → (from Prelude.∘ to) x ≡ x

open _≲_

refl≲ : ∀ {𝓍} {X : Set 𝓍} → X ≲ X
refl≲ = record
          { to      = Prelude.id
          ; from    = Prelude.id
          ; from∘to = λ x → refl
          }

trans≲ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : Set 𝓏} → X ≲ Y → Y ≲ Z → X ≲ Z
trans≲ leq leq′ = record
                    { to      = to leq′ Prelude.∘ to leq
                    ; from    = from leq Prelude.∘ from leq′
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
≡→≲ = ≃→≲ Prelude.∘ ≡→≃

module ≲-Reasoning where
  infix 1 begin_
  begin_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → X ≲ Y → X ≲ Y
  begin leq = leq

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
