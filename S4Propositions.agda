module S4Propositions where

open import Prelude
open import Category
open import List


--------------------------------------------------------------------------------


infixr 8 _⊃_
data Prop : Set
  where
    BASE : Prop
    _⊃_  : Prop → Prop → Prop
    □_   : Prop → Prop


--------------------------------------------------------------------------------


inj⊃₁ : ∀ {A₁ A₂ B₁ B₂} → A₁ ⊃ B₁ ≡ A₂ ⊃ B₂ → A₁ ≡ A₂
inj⊃₁ refl = refl


inj⊃₂ : ∀ {A₁ A₂ B₁ B₂} → A₁ ⊃ B₁ ≡ A₂ ⊃ B₂ → B₁ ≡ B₂
inj⊃₂ refl = refl


inj□ : ∀ {A₁ A₂} → □ A₁ ≡ □ A₂ → A₁ ≡ A₂
inj□ refl = refl


_≟ₚ_ : (A₁ A₂ : Prop) → Dec (A₁ ≡ A₂)
BASE      ≟ₚ BASE      = yes refl
BASE      ≟ₚ (A₂ ⊃ B₂) = no (\ ())
BASE      ≟ₚ (□ A₂)    = no (\ ())
(A₁ ⊃ B₁) ≟ₚ BASE      = no (\ ())
(A₁ ⊃ B₁) ≟ₚ (A₂ ⊃ B₂) with A₁ ≟ₚ A₂ | B₁ ≟ₚ B₂
...                    | yes refl | yes refl = yes refl
...                    | yes refl | no B₁≢B₂ = no (B₁≢B₂ ∘ inj⊃₂)
...                    | no A₁≢A₂ | _        = no (A₁≢A₂ ∘ inj⊃₁)
(A₁ ⊃ B₁) ≟ₚ (□ A₂)    = no (\ ())
(□ A₁)    ≟ₚ BASE      = no (\ ())
(□ A₁)    ≟ₚ (A₂ ⊃ B₂) = no (\ ())
(□ A₁)    ≟ₚ (□ A₂)    with A₁ ≟ₚ A₂
...                    | yes refl = yes refl
...                    | no A₁≢A₂ = no (A₁≢A₂ ∘ inj□)


--------------------------------------------------------------------------------


infix 7 _true
record Truth : Set
  where
    constructor _true
    field
      A : Prop


infix 7 _valid
record Validity : Set
  where
    constructor _valid
    field
      A : Prop


-- TODO: Remove this

infix 7 _valid[_]
record ContextualValidity : Set
  where
    constructor _valid[_]
    field
      A : Prop
      Ψ : List Truth


--------------------------------------------------------------------------------
