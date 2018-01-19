module IPLPropositions where

open import Prelude
open import Category


--------------------------------------------------------------------------------


infixr 8 _⊃_
data Prop : Set
  where
    BASE : Prop
    _⊃_  : Prop → Prop → Prop


--------------------------------------------------------------------------------


inj⊃₁ : ∀ {A₁ A₂ B₁ B₂} → A₁ ⊃ B₁ ≡ A₂ ⊃ B₂ → A₁ ≡ A₂
inj⊃₁ refl = refl


inj⊃₂ : ∀ {A₁ A₂ B₁ B₂} → A₁ ⊃ B₁ ≡ A₂ ⊃ B₂ → B₁ ≡ B₂
inj⊃₂ refl = refl


_≟ₚ_ : (A₁ A₂ : Prop) → Dec (A₁ ≡ A₂)
BASE      ≟ₚ BASE      = yes refl
BASE      ≟ₚ (A₂ ⊃ B₂) = no (\ ())
(A₁ ⊃ B₁) ≟ₚ BASE      = no (\ ())
(A₁ ⊃ B₁) ≟ₚ (A₂ ⊃ B₂) with A₁ ≟ₚ A₂ | B₁ ≟ₚ B₂
...                    | yes refl | yes refl = yes refl
...                    | yes refl | no B₁≢B₂ = no (B₁≢B₂ ∘ inj⊃₂)
...                    | no A₁≢A₂ | _        = no (A₁≢A₂ ∘ inj⊃₁)


--------------------------------------------------------------------------------
