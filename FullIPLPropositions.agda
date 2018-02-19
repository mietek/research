module FullIPLPropositions where

open import Prelude
open import Category
open import List


--------------------------------------------------------------------------------


infixl 9 _∨_ _∧_
infixr 8 _⊃_
data Prop : Set
  where
    ι_  : String → Prop
    _⊃_ : Prop → Prop → Prop
    _∧_ : Prop → Prop → Prop
    𝟏   : Prop
    𝟎   : Prop
    _∨_ : Prop → Prop → Prop


~_ : Prop → Prop
~ A = A ⊃ 𝟎


instance
  PropVar : IsString Prop
  PropVar =
    record
      { Constraint = \ s → ⊤
      ; fromString = \ s → ι s
      }


--------------------------------------------------------------------------------


injι : ∀ {P₁ P₂} → ι P₁ ≡ ι P₂
                 → P₁ ≡ P₂
injι refl = refl


inj⊃₁ : ∀ {A₁ A₂ B₁ B₂} → A₁ ⊃ B₁ ≡ A₂ ⊃ B₂
                        → A₁ ≡ A₂
inj⊃₁ refl = refl


inj⊃₂ : ∀ {A₁ A₂ B₁ B₂} → A₁ ⊃ B₁ ≡ A₂ ⊃ B₂
                        → B₁ ≡ B₂
inj⊃₂ refl = refl


inj∧₁ : ∀ {A₁ A₂ B₁ B₂} → A₁ ∧ B₁ ≡ A₂ ∧ B₂
                        → A₁ ≡ A₂
inj∧₁ refl = refl


inj∧₂ : ∀ {A₁ A₂ B₁ B₂} → A₁ ∧ B₁ ≡ A₂ ∧ B₂
                        → B₁ ≡ B₂
inj∧₂ refl = refl


inj∨₁ : ∀ {A₁ A₂ B₁ B₂} → A₁ ∨ B₁ ≡ A₂ ∨ B₂
                        → A₁ ≡ A₂
inj∨₁ refl = refl


inj∨₂ : ∀ {A₁ A₂ B₁ B₂} → A₁ ∨ B₁ ≡ A₂ ∨ B₂
                        → B₁ ≡ B₂
inj∨₂ refl = refl


_≟ₚ_ : (A₁ A₂ : Prop) → Dec (A₁ ≡ A₂)
(ι P₁)    ≟ₚ (ι P₂)    with P₁ ≟ₛ P₂
...                    | yes refl = yes refl
...                    | no P₁≢P₂ = no (P₁≢P₂ ∘ injι)
(ι P₁)    ≟ₚ (A₂ ⊃ B₂) = no (\ ())
(ι P₁)    ≟ₚ (A₂ ∧ B₂) = no (\ ())
(ι P₁)    ≟ₚ 𝟏         = no (\ ())
(ι P₁)    ≟ₚ 𝟎         = no (\ ())
(ι P₁)    ≟ₚ (A₂ ∨ B₂) = no (\ ())
(A₁ ⊃ B₁) ≟ₚ (ι P₂)    = no (\ ())
(A₁ ⊃ B₁) ≟ₚ (A₂ ⊃ B₂) with A₁ ≟ₚ A₂ | B₁ ≟ₚ B₂
...                    | yes refl | yes refl = yes refl
...                    | yes refl | no B₁≢B₂ = no (B₁≢B₂ ∘ inj⊃₂)
...                    | no A₁≢A₂ | _        = no (A₁≢A₂ ∘ inj⊃₁)
(A₁ ⊃ B₁) ≟ₚ (A₂ ∧ B₂) = no (\ ())
(A₁ ⊃ B₁) ≟ₚ 𝟏         = no (\ ())
(A₁ ⊃ B₁) ≟ₚ 𝟎         = no (\ ())
(A₁ ⊃ B₁) ≟ₚ (A₂ ∨ B₂) = no (\ ())
(A₁ ∧ B₁) ≟ₚ (ι P₂)    = no (\ ())
(A₁ ∧ B₁) ≟ₚ (A₂ ⊃ B₂) = no (\ ())
(A₁ ∧ B₁) ≟ₚ (A₂ ∧ B₂) with A₁ ≟ₚ A₂ | B₁ ≟ₚ B₂
...                    | yes refl | yes refl = yes refl
...                    | yes refl | no B₁≢B₂ = no (B₁≢B₂ ∘ inj∧₂)
...                    | no A₁≢A₂ | _        = no (A₁≢A₂ ∘ inj∧₁)
(A₁ ∧ B₁) ≟ₚ 𝟏         = no (\ ())
(A₁ ∧ B₁) ≟ₚ 𝟎         = no (\ ())
(A₁ ∧ B₁) ≟ₚ (A₂ ∨ B₂) = no (\ ())
𝟏         ≟ₚ (ι P₂)    = no (\ ())
𝟏         ≟ₚ (A₂ ⊃ B₂) = no (\ ())
𝟏         ≟ₚ (A₂ ∧ B₂) = no (\ ())
𝟏         ≟ₚ 𝟏         = yes refl
𝟏         ≟ₚ 𝟎         = no (\ ())
𝟏         ≟ₚ (A₂ ∨ B₂) = no (\ ())
𝟎         ≟ₚ (ι P₂)    = no (\ ())
𝟎         ≟ₚ (A₂ ⊃ B₂) = no (\ ())
𝟎         ≟ₚ (A₂ ∧ B₂) = no (\ ())
𝟎         ≟ₚ 𝟏         = no (\ ())
𝟎         ≟ₚ 𝟎         = yes refl
𝟎         ≟ₚ (A₂ ∨ B₂) = no (\ ())
(A₁ ∨ B₁) ≟ₚ (ι P₂)    = no (\ ())
(A₁ ∨ B₁) ≟ₚ (A₂ ⊃ B₂) = no (\ ())
(A₁ ∨ B₁) ≟ₚ (A₂ ∧ B₂) = no (\ ())
(A₁ ∨ B₁) ≟ₚ 𝟏         = no (\ ())
(A₁ ∨ B₁) ≟ₚ 𝟎         = no (\ ())
(A₁ ∨ B₁) ≟ₚ (A₂ ∨ B₂) with A₁ ≟ₚ A₂ | B₁ ≟ₚ B₂
...                    | yes refl | yes refl = yes refl
...                    | yes refl | no B₁≢B₂ = no (B₁≢B₂ ∘ inj∨₂)
...                    | no A₁≢A₂ | _        = no (A₁≢A₂ ∘ inj∨₁)


--------------------------------------------------------------------------------


_⊃⋯⊃_ : List Prop → Prop → Prop
∙       ⊃⋯⊃ A = A
(Ξ , B) ⊃⋯⊃ A = Ξ ⊃⋯⊃ (B ⊃ A)


--------------------------------------------------------------------------------
