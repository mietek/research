module BasicIPC where

open import Common.Context public


-- Propositions of intuitionistic propositional calculus, without ∨ or ⊥.

infixl 7 _∧_
infixr 5 _▻_
data Ty : Set where
  α_  : Atom → Ty
  _▻_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty
  ⊤  : Ty

infix 5 _▻◅_
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

_≟ᵗʸ_ : (A A′ : Ty) → Dec (A ≡ A′)
(α P)   ≟ᵗʸ (α P′)    with P ≟ᵅ P′
(α P)   ≟ᵗʸ (α .P)    | yes refl = yes refl
(α P)   ≟ᵗʸ (α P′)    | no  P≢P′ = no (P≢P′ ∘ invα)
(α P)   ≟ᵗʸ (A′ ▻ B′) = no λ ()
(α P)   ≟ᵗʸ (A′ ∧ B′) = no λ ()
(α P)   ≟ᵗʸ ⊤        = no λ ()
(A ▻ B) ≟ᵗʸ (α P′)    = no λ ()
(A ▻ B) ≟ᵗʸ (A′ ▻ B′) with A ≟ᵗʸ A′ | B ≟ᵗʸ B′
(A ▻ B) ≟ᵗʸ (.A ▻ .B) | yes refl | yes refl = yes refl
(A ▻ B) ≟ᵗʸ (A′ ▻ B′) | no  A≢A′ | _        = no (A≢A′ ∘ inv▻ₗ)
(A ▻ B) ≟ᵗʸ (A′ ▻ B′) | _        | no  B≢B′ = no (B≢B′ ∘ inv▻ᵣ)
(A ▻ B) ≟ᵗʸ (A′ ∧ B′) = no λ ()
(A ▻ B) ≟ᵗʸ ⊤        = no λ ()
(A ∧ B) ≟ᵗʸ (α P′)    = no λ ()
(A ∧ B) ≟ᵗʸ (A′ ▻ B′) = no λ ()
(A ∧ B) ≟ᵗʸ (A′ ∧ B′) with A ≟ᵗʸ A′ | B ≟ᵗʸ B′
(A ∧ B) ≟ᵗʸ (.A ∧ .B) | yes refl | yes refl = yes refl
(A ∧ B) ≟ᵗʸ (A′ ∧ B′) | no  A≢A′ | _        = no (A≢A′ ∘ inv∧ₗ)
(A ∧ B) ≟ᵗʸ (A′ ∧ B′) | _        | no  B≢B′ = no (B≢B′ ∘ inv∧ᵣ)
(A ∧ B) ≟ᵗʸ ⊤        = no λ ()
⊤      ≟ᵗʸ (α P′)    = no λ ()
⊤      ≟ᵗʸ (A′ ▻ B′) = no λ ()
⊤      ≟ᵗʸ (A′ ∧ B′) = no λ ()
⊤      ≟ᵗʸ ⊤        = yes refl

open ContextEquality (_≟ᵗʸ_) public


-- Additional useful propositions.

infixr 5 _▻⋯▻_
_▻⋯▻_ : Cx Ty → Ty → Ty
⌀       ▻⋯▻ B = B
(Π , A) ▻⋯▻ B = Π ▻⋯▻ (A ▻ B)

infixr 5 _▻⋯▻⋆_
_▻⋯▻⋆_ : Cx Ty → Cx Ty → Ty
Γ ▻⋯▻⋆ ⌀       = ⊤
Γ ▻⋯▻⋆ (Π , A) = (Γ ▻⋯▻⋆ Π) ∧ (Γ ▻⋯▻ A)
