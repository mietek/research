module BasicIS4 where

open import Common.Context public


-- Propositions of intuitionistic modal logic S4, without ∨, ⊥, or ◇.

infixr 8 □_
infixl 7 _∧_
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


-- Decidable equality.

_≟ᵀ_ : (A A′ : Ty) → Dec (A ≡ A′)
(α P)   ≟ᵀ (α P′)    with P ≟ᵅ P′
(α P)   ≟ᵀ (α .P)    | yes refl = yes refl
(α P)   ≟ᵀ (α P′)    | no  P≢P′ = no (P≢P′ ∘ invα)
(α P)   ≟ᵀ (A′ ▻ B′) = no λ ()
(α P)   ≟ᵀ (□ A′)    = no λ ()
(α P)   ≟ᵀ (A′ ∧ B′) = no λ ()
(α P)   ≟ᵀ ⊤        = no λ ()
(A ▻ B) ≟ᵀ (α P′)    = no λ ()
(A ▻ B) ≟ᵀ (A′ ▻ B′) with A ≟ᵀ A′ | B ≟ᵀ B′
(A ▻ B) ≟ᵀ (.A ▻ .B) | yes refl | yes refl = yes refl
(A ▻ B) ≟ᵀ (A′ ▻ B′) | no  A≢A′ | _        = no (A≢A′ ∘ inv▻ₗ)
(A ▻ B) ≟ᵀ (A′ ▻ B′) | _        | no  B≢B′ = no (B≢B′ ∘ inv▻ᵣ)
(A ▻ B) ≟ᵀ (□ A′)    = no λ ()
(A ▻ B) ≟ᵀ (A′ ∧ B′) = no λ ()
(A ▻ B) ≟ᵀ ⊤        = no λ ()
(□ A)   ≟ᵀ (α P′)    = no λ ()
(□ A)   ≟ᵀ (A′ ▻ B′) = no λ ()
(□ A)   ≟ᵀ (□ A′)    with A ≟ᵀ A′
(□ A)   ≟ᵀ (□ .A)    | yes refl = yes refl
(□ A)   ≟ᵀ (□ A′)    | no  A≢A′ = no (A≢A′ ∘ inv□)
(□ A)   ≟ᵀ (A′ ∧ B′) = no λ ()
(□ A)   ≟ᵀ ⊤        = no λ ()
(A ∧ B) ≟ᵀ (α P′)    = no λ ()
(A ∧ B) ≟ᵀ (A′ ▻ B′) = no λ ()
(A ∧ B) ≟ᵀ (□ A′)    = no λ ()
(A ∧ B) ≟ᵀ (A′ ∧ B′) with A ≟ᵀ A′ | B ≟ᵀ B′
(A ∧ B) ≟ᵀ (.A ∧ .B) | yes refl | yes refl = yes refl
(A ∧ B) ≟ᵀ (A′ ∧ B′) | no  A≢A′ | _        = no (A≢A′ ∘ inv∧ₗ)
(A ∧ B) ≟ᵀ (A′ ∧ B′) | _        | no  B≢B′ = no (B≢B′ ∘ inv∧ᵣ)
(A ∧ B) ≟ᵀ ⊤        = no λ ()
⊤      ≟ᵀ (α P′)    = no λ ()
⊤      ≟ᵀ (A′ ▻ B′) = no λ ()
⊤      ≟ᵀ (□ A′)    = no λ ()
⊤      ≟ᵀ (A′ ∧ B′) = no λ ()
⊤      ≟ᵀ ⊤        = yes refl

open ContextEquality (_≟ᵀ_) public


-- Additional useful propositions.

infixr 5 _▻⋯▻_
_▻⋯▻_ : Cx Ty → Ty → Ty
⌀       ▻⋯▻ B = B
(Ξ , A) ▻⋯▻ B = Ξ ▻⋯▻ (A ▻ B)

infixr 8 □⋆_
□⋆_ : Cx Ty → Cx Ty
□⋆ ⌀       = ⌀
□⋆ (Ξ , A) = □⋆ Ξ , □ A

dist□⋆ₗ : ∀ Ξ Ξ′ → □⋆ (Ξ ⧺ Ξ′) ≡ (□⋆ Ξ) ⧺ (□⋆ Ξ′)
dist□⋆ₗ Ξ ⌀        = refl
dist□⋆ₗ Ξ (Ξ′ , A) = cong₂ _,_ (dist□⋆ₗ Ξ Ξ′) refl

lift⊆ : ∀ {Δ Δ′} → Δ ⊆ Δ′ → □⋆ Δ ⊆ □⋆ Δ′
lift⊆ done     = done
lift⊆ (skip θ) = skip (lift⊆ θ)
lift⊆ (keep θ) = keep (lift⊆ θ)
