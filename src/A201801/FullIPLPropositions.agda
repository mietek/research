module A201801.FullIPLPropositions where

open import A201801.Prelude
open import A201801.Category
open import A201801.List


--------------------------------------------------------------------------------


infixl 9 _∨_ _∧_
infixr 8 _⊃_
data Form : Set
  where
    ι_  : String → Form
    _⊃_ : Form → Form → Form
    _∧_ : Form → Form → Form
    𝟙   : Form
    𝟘   : Form
    _∨_ : Form → Form → Form


~_ : Form → Form
~ A = A ⊃ 𝟘


instance
  FormVar : IsString Form
  FormVar =
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


_≟ₚ_ : (A₁ A₂ : Form) → Dec (A₁ ≡ A₂)
(ι P₁)    ≟ₚ (ι P₂)    with P₁ ≟ₛ P₂
...                    | yes refl = yes refl
...                    | no P₁≢P₂ = no (P₁≢P₂ ∘ injι)
(ι P₁)    ≟ₚ (A₂ ⊃ B₂) = no (\ ())
(ι P₁)    ≟ₚ (A₂ ∧ B₂) = no (\ ())
(ι P₁)    ≟ₚ 𝟙         = no (\ ())
(ι P₁)    ≟ₚ 𝟘         = no (\ ())
(ι P₁)    ≟ₚ (A₂ ∨ B₂) = no (\ ())
(A₁ ⊃ B₁) ≟ₚ (ι P₂)    = no (\ ())
(A₁ ⊃ B₁) ≟ₚ (A₂ ⊃ B₂) with A₁ ≟ₚ A₂ | B₁ ≟ₚ B₂
...                    | yes refl | yes refl = yes refl
...                    | yes refl | no B₁≢B₂ = no (B₁≢B₂ ∘ inj⊃₂)
...                    | no A₁≢A₂ | _        = no (A₁≢A₂ ∘ inj⊃₁)
(A₁ ⊃ B₁) ≟ₚ (A₂ ∧ B₂) = no (\ ())
(A₁ ⊃ B₁) ≟ₚ 𝟙         = no (\ ())
(A₁ ⊃ B₁) ≟ₚ 𝟘         = no (\ ())
(A₁ ⊃ B₁) ≟ₚ (A₂ ∨ B₂) = no (\ ())
(A₁ ∧ B₁) ≟ₚ (ι P₂)    = no (\ ())
(A₁ ∧ B₁) ≟ₚ (A₂ ⊃ B₂) = no (\ ())
(A₁ ∧ B₁) ≟ₚ (A₂ ∧ B₂) with A₁ ≟ₚ A₂ | B₁ ≟ₚ B₂
...                    | yes refl | yes refl = yes refl
...                    | yes refl | no B₁≢B₂ = no (B₁≢B₂ ∘ inj∧₂)
...                    | no A₁≢A₂ | _        = no (A₁≢A₂ ∘ inj∧₁)
(A₁ ∧ B₁) ≟ₚ 𝟙         = no (\ ())
(A₁ ∧ B₁) ≟ₚ 𝟘         = no (\ ())
(A₁ ∧ B₁) ≟ₚ (A₂ ∨ B₂) = no (\ ())
𝟙         ≟ₚ (ι P₂)    = no (\ ())
𝟙         ≟ₚ (A₂ ⊃ B₂) = no (\ ())
𝟙         ≟ₚ (A₂ ∧ B₂) = no (\ ())
𝟙         ≟ₚ 𝟙         = yes refl
𝟙         ≟ₚ 𝟘         = no (\ ())
𝟙         ≟ₚ (A₂ ∨ B₂) = no (\ ())
𝟘         ≟ₚ (ι P₂)    = no (\ ())
𝟘         ≟ₚ (A₂ ⊃ B₂) = no (\ ())
𝟘         ≟ₚ (A₂ ∧ B₂) = no (\ ())
𝟘         ≟ₚ 𝟙         = no (\ ())
𝟘         ≟ₚ 𝟘         = yes refl
𝟘         ≟ₚ (A₂ ∨ B₂) = no (\ ())
(A₁ ∨ B₁) ≟ₚ (ι P₂)    = no (\ ())
(A₁ ∨ B₁) ≟ₚ (A₂ ⊃ B₂) = no (\ ())
(A₁ ∨ B₁) ≟ₚ (A₂ ∧ B₂) = no (\ ())
(A₁ ∨ B₁) ≟ₚ 𝟙         = no (\ ())
(A₁ ∨ B₁) ≟ₚ 𝟘         = no (\ ())
(A₁ ∨ B₁) ≟ₚ (A₂ ∨ B₂) with A₁ ≟ₚ A₂ | B₁ ≟ₚ B₂
...                    | yes refl | yes refl = yes refl
...                    | yes refl | no B₁≢B₂ = no (B₁≢B₂ ∘ inj∨₂)
...                    | no A₁≢A₂ | _        = no (A₁≢A₂ ∘ inj∨₁)


--------------------------------------------------------------------------------


_⊃⋯⊃_ : List Form → Form → Form
∙       ⊃⋯⊃ A = A
(Ξ , B) ⊃⋯⊃ A = Ξ ⊃⋯⊃ (B ⊃ A)


--------------------------------------------------------------------------------
