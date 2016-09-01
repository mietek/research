module BasicIPC where

open import Common.Context public


-- Propositions of intuitionistic propositional calculus, without ∨ or ⊥.

infixl 8 _∧_
infixr 6 _▻_
data Ty : Set where
  α_  : Atom → Ty
  _▻_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty
  ⊤  : Ty

infix 6 _▻◅_
_▻◅_ : Ty → Ty → Ty
A ▻◅ B = (A ▻ B) ∧ (B ▻ A)


-- Inversion principles.

invα : ∀ {P P′} → α P ≡ α P′ → P ≡ P′
invα refl = refl

inv▻ₗ : ∀ {A A′ B B′} → A ▻ B ≡ A′ ▻ B′ → A ≡ A′
inv▻ₗ refl = refl

inv▻ᵣ : ∀ {A A′ B B′} → A ▻ B ≡ A′ ▻ B′ → B ≡ B′
inv▻ᵣ refl = refl

inv∧ₗ : ∀ {A A′ B B′} → A ∧ B ≡ A′ ∧ B′ → A ≡ A′
inv∧ₗ refl = refl

inv∧ᵣ : ∀ {A A′ B B′} → A ∧ B ≡ A′ ∧ B′ → B ≡ B′
inv∧ᵣ refl = refl


-- Decidable equality.

_≟ᵀ_ : (A A′ : Ty) → Dec (A ≡ A′)
(α P)   ≟ᵀ (α P′)    with P ≟ᵅ P′
(α P)   ≟ᵀ (α .P)    | yes refl = yes refl
(α P)   ≟ᵀ (α P′)    | no  P≢P′ = no (P≢P′ ∘ invα)
(α P)   ≟ᵀ (A′ ▻ B′) = no λ ()
(α P)   ≟ᵀ (A′ ∧ B′) = no λ ()
(α P)   ≟ᵀ ⊤        = no λ ()
(A ▻ B) ≟ᵀ (α P′)    = no λ ()
(A ▻ B) ≟ᵀ (A′ ▻ B′) with A ≟ᵀ A′ | B ≟ᵀ B′
(A ▻ B) ≟ᵀ (.A ▻ .B) | yes refl | yes refl = yes refl
(A ▻ B) ≟ᵀ (A′ ▻ B′) | no  A≢A′ | _        = no (A≢A′ ∘ inv▻ₗ)
(A ▻ B) ≟ᵀ (A′ ▻ B′) | _        | no  B≢B′ = no (B≢B′ ∘ inv▻ᵣ)
(A ▻ B) ≟ᵀ (A′ ∧ B′) = no λ ()
(A ▻ B) ≟ᵀ ⊤        = no λ ()
(A ∧ B) ≟ᵀ (α P′)    = no λ ()
(A ∧ B) ≟ᵀ (A′ ▻ B′) = no λ ()
(A ∧ B) ≟ᵀ (A′ ∧ B′) with A ≟ᵀ A′ | B ≟ᵀ B′
(A ∧ B) ≟ᵀ (.A ∧ .B) | yes refl | yes refl = yes refl
(A ∧ B) ≟ᵀ (A′ ∧ B′) | no  A≢A′ | _        = no (A≢A′ ∘ inv∧ₗ)
(A ∧ B) ≟ᵀ (A′ ∧ B′) | _        | no  B≢B′ = no (B≢B′ ∘ inv∧ᵣ)
(A ∧ B) ≟ᵀ ⊤        = no λ ()
⊤      ≟ᵀ (α P′)    = no λ ()
⊤      ≟ᵀ (A′ ▻ B′) = no λ ()
⊤      ≟ᵀ (A′ ∧ B′) = no λ ()
⊤      ≟ᵀ ⊤        = yes refl

open ContextEquality (_≟ᵀ_) public


-- Additional useful propositions.

infixr 6 _▻⋯▻_
_▻⋯▻_ : Cx Ty → Ty → Ty
∅       ▻⋯▻ B = B
(Ξ , A) ▻⋯▻ B = Ξ ▻⋯▻ (A ▻ B)

infixr 6 _▻⋯▻⋆_
_▻⋯▻⋆_ : Cx Ty → Cx Ty → Ty
Γ ▻⋯▻⋆ ∅       = ⊤
Γ ▻⋯▻⋆ (Ξ , A) = (Γ ▻⋯▻⋆ Ξ) ∧ (Γ ▻⋯▻ A)
