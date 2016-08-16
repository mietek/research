-- Common syntax.

module New.BasicIS4.Syntax.Common where

open import Common.Context public


-- Types, or propositions.

infixl 7 _∧_
infixr 6 □_
infixr 5 _▻_
data Ty : Set where
  α_  : Atom → Ty
  _▻_ : Ty → Ty → Ty
  □_  : Ty → Ty
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

inv□ : ∀ {A A′} → □ A ≡ □ A′ → A ≡ A′
inv□ refl = refl

inv∧ₗ : ∀ {A A′ B B′} → A ∧ B ≡ A′ ∧ B′ → A ≡ A′
inv∧ₗ refl = refl

inv∧ᵣ : ∀ {A A′ B B′} → A ∧ B ≡ A′ ∧ B′ → B ≡ B′
inv∧ᵣ refl = refl


-- Decidable equality on types.

_≟ᵗʸ_ : (A A′ : Ty) → Dec (A ≡ A′)
(α P)   ≟ᵗʸ (α P′)    with P ≟ᵅ P′
(α P)   ≟ᵗʸ (α .P)    | yes refl = yes refl
(α P)   ≟ᵗʸ (α P′)    | no  P≢P′ = no (P≢P′ ∘ invα)
(α P)   ≟ᵗʸ (A′ ▻ B′) = no λ ()
(α P)   ≟ᵗʸ (□ A′)    = no λ ()
(α P)   ≟ᵗʸ (A′ ∧ B′) = no λ ()
(α P)   ≟ᵗʸ ⊤        = no λ ()
(A ▻ B) ≟ᵗʸ (α P′)    = no λ ()
(A ▻ B) ≟ᵗʸ (A′ ▻ B′) with A ≟ᵗʸ A′ | B ≟ᵗʸ B′
(A ▻ B) ≟ᵗʸ (.A ▻ .B) | yes refl | yes refl = yes refl
(A ▻ B) ≟ᵗʸ (A′ ▻ B′) | no  A≢A′ | _        = no (A≢A′ ∘ inv▻ₗ)
(A ▻ B) ≟ᵗʸ (A′ ▻ B′) | _        | no  B≢B′ = no (B≢B′ ∘ inv▻ᵣ)
(A ▻ B) ≟ᵗʸ (□ A′)    = no λ ()
(A ▻ B) ≟ᵗʸ (A′ ∧ B′) = no λ ()
(A ▻ B) ≟ᵗʸ ⊤        = no λ ()
(□ A)   ≟ᵗʸ (α P′)    = no λ ()
(□ A)   ≟ᵗʸ (A′ ▻ B′) = no λ ()
(□ A)   ≟ᵗʸ (□ A′)    with A ≟ᵗʸ A′
(□ A)   ≟ᵗʸ (□ .A)    | yes refl = yes refl
(□ A)   ≟ᵗʸ (□ A′)    | no  A≢A′ = no (A≢A′ ∘ inv□)
(□ A)   ≟ᵗʸ (A′ ∧ B′) = no λ ()
(□ A)   ≟ᵗʸ ⊤        = no λ ()
(A ∧ B) ≟ᵗʸ (α P′)    = no λ ()
(A ∧ B) ≟ᵗʸ (A′ ▻ B′) = no λ ()
(A ∧ B) ≟ᵗʸ (□ A′)    = no λ ()
(A ∧ B) ≟ᵗʸ (A′ ∧ B′) with A ≟ᵗʸ A′ | B ≟ᵗʸ B′
(A ∧ B) ≟ᵗʸ (.A ∧ .B) | yes refl | yes refl = yes refl
(A ∧ B) ≟ᵗʸ (A′ ∧ B′) | no  A≢A′ | _        = no (A≢A′ ∘ inv∧ₗ)
(A ∧ B) ≟ᵗʸ (A′ ∧ B′) | _        | no  B≢B′ = no (B≢B′ ∘ inv∧ᵣ)
(A ∧ B) ≟ᵗʸ ⊤        = no λ ()
⊤      ≟ᵗʸ (α P′)    = no λ ()
⊤      ≟ᵗʸ (A′ ▻ B′) = no λ ()
⊤      ≟ᵗʸ (□ A′)    = no λ ()
⊤      ≟ᵗʸ (A′ ∧ B′) = no λ ()
⊤      ≟ᵗʸ ⊤        = yes refl

open ContextEquality (_≟ᵗʸ_) public


-- Additional useful types.

infixr 5 _▻⋯▻_
_▻⋯▻_ : Cx Ty → Ty → Ty
⌀       ▻⋯▻ B = B
(Π , A) ▻⋯▻ B = Π ▻⋯▻ (A ▻ B)

infixr 6 □⋆_
□⋆_ : Cx Ty → Cx Ty
□⋆ ⌀       = ⌀
□⋆ (Π , A) = □⋆ Π , □ A

dist□⋆ₗ : ∀ Π Π′ → □⋆ (Π ⧺ Π′) ≡ (□⋆ Π) ⧺ (□⋆ Π′)
dist□⋆ₗ Π ⌀        = refl
dist□⋆ₗ Π (Π′ , A) = cong₂ _,_ (dist□⋆ₗ Π Π′) refl

lift⊆ : ∀ {Δ Δ′} → Δ ⊆ Δ′ → □⋆ Δ ⊆ □⋆ Δ′
lift⊆ done     = done
lift⊆ (skip θ) = skip (lift⊆ θ)
lift⊆ (keep θ) = keep (lift⊆ θ)
