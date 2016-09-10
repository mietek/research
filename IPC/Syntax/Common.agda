-- Intuitionistic propositional calculus.
-- Common syntax.

module IPC.Syntax.Common where

open import Common.Context public


-- Types, or propositions.

infixl 9 _∧_
infixl 8 _∨_
infixr 7 _▻_
data Ty : Set where
  α_  : Atom → Ty
  _▻_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty
  ⊤  : Ty
  ⊥  : Ty
  _∨_ : Ty → Ty → Ty


-- Additional useful types.

¬_ : Ty → Ty
¬ A = A ▻ ⊥

infix 7 _▻◅_
_▻◅_ : Ty → Ty → Ty
A ▻◅ B = (A ▻ B) ∧ (B ▻ A)

infixr 7 _▻⋯▻_
_▻⋯▻_ : Cx Ty → Ty → Ty
∅       ▻⋯▻ B = B
(Ξ , A) ▻⋯▻ B = Ξ ▻⋯▻ (A ▻ B)

infixr 7 _▻⋯▻⋆_
_▻⋯▻⋆_ : Cx Ty → Cx Ty → Ty
Γ ▻⋯▻⋆ ∅       = ⊤
Γ ▻⋯▻⋆ (Ξ , A) = (Γ ▻⋯▻⋆ Ξ) ∧ (Γ ▻⋯▻ A)


-- Inversion principles.

invα : ∀ {P P′} → α P ≡ α P′ → P ≡ P′
invα refl = refl

inv▻₁ : ∀ {A A′ B B′} → A ▻ B ≡ A′ ▻ B′ → A ≡ A′
inv▻₁ refl = refl

inv▻₂ : ∀ {A A′ B B′} → A ▻ B ≡ A′ ▻ B′ → B ≡ B′
inv▻₂ refl = refl

inv∧₁ : ∀ {A A′ B B′} → A ∧ B ≡ A′ ∧ B′ → A ≡ A′
inv∧₁ refl = refl

inv∧₂ : ∀ {A A′ B B′} → A ∧ B ≡ A′ ∧ B′ → B ≡ B′
inv∧₂ refl = refl

inv∨₁ : ∀ {A A′ B B′} → A ∨ B ≡ A′ ∨ B′ → A ≡ A′
inv∨₁ refl = refl

inv∨₂ : ∀ {A A′ B B′} → A ∨ B ≡ A′ ∨ B′ → B ≡ B′
inv∨₂ refl = refl


-- Decidable equality on types.

_≟ᵀ_ : (A A′ : Ty) → Dec (A ≡ A′)
(α P)   ≟ᵀ (α P′)    with P ≟ᵅ P′
(α P)   ≟ᵀ (α .P)    | yes refl = yes refl
(α P)   ≟ᵀ (α P′)    | no  P≢P′ = no (P≢P′ ∘ invα)
(α P)   ≟ᵀ (A′ ▻ B′) = no λ ()
(α P)   ≟ᵀ (A′ ∧ B′) = no λ ()
(α P)   ≟ᵀ ⊤        = no λ ()
(α P)   ≟ᵀ ⊥        = no λ ()
(α P)   ≟ᵀ (A′ ∨ B′) = no λ ()
(A ▻ B) ≟ᵀ (α P′)    = no λ ()
(A ▻ B) ≟ᵀ (A′ ▻ B′) with A ≟ᵀ A′ | B ≟ᵀ B′
(A ▻ B) ≟ᵀ (.A ▻ .B) | yes refl | yes refl = yes refl
(A ▻ B) ≟ᵀ (A′ ▻ B′) | no  A≢A′ | _        = no (A≢A′ ∘ inv▻₁)
(A ▻ B) ≟ᵀ (A′ ▻ B′) | _        | no  B≢B′ = no (B≢B′ ∘ inv▻₂)
(A ▻ B) ≟ᵀ (A′ ∧ B′) = no λ ()
(A ▻ B) ≟ᵀ ⊤        = no λ ()
(A ▻ B) ≟ᵀ ⊥        = no λ ()
(A ▻ B) ≟ᵀ (A′ ∨ B′) = no λ ()
(A ∧ B) ≟ᵀ (α P′)    = no λ ()
(A ∧ B) ≟ᵀ (A′ ▻ B′) = no λ ()
(A ∧ B) ≟ᵀ (A′ ∧ B′) with A ≟ᵀ A′ | B ≟ᵀ B′
(A ∧ B) ≟ᵀ (.A ∧ .B) | yes refl | yes refl = yes refl
(A ∧ B) ≟ᵀ (A′ ∧ B′) | no  A≢A′ | _        = no (A≢A′ ∘ inv∧₁)
(A ∧ B) ≟ᵀ (A′ ∧ B′) | _        | no  B≢B′ = no (B≢B′ ∘ inv∧₂)
(A ∧ B) ≟ᵀ ⊤        = no λ ()
(A ∧ B) ≟ᵀ ⊥        = no λ ()
(A ∧ B) ≟ᵀ (A′ ∨ B′) = no λ ()
⊤      ≟ᵀ (α P′)    = no λ ()
⊤      ≟ᵀ (A′ ▻ B′) = no λ ()
⊤      ≟ᵀ (A′ ∧ B′) = no λ ()
⊤      ≟ᵀ ⊤        = yes refl
⊤      ≟ᵀ ⊥        = no λ ()
⊤      ≟ᵀ (A′ ∨ B′) = no λ ()
⊥      ≟ᵀ (α P′)    = no λ ()
⊥      ≟ᵀ (A′ ▻ B′) = no λ ()
⊥      ≟ᵀ (A′ ∧ B′) = no λ ()
⊥      ≟ᵀ ⊤        = no λ ()
⊥      ≟ᵀ ⊥        = yes refl
⊥      ≟ᵀ (A′ ∨ B′) = no λ ()
(A ∨ B) ≟ᵀ (α P′)    = no λ ()
(A ∨ B) ≟ᵀ (A′ ▻ B′) = no λ ()
(A ∨ B) ≟ᵀ (A′ ∧ B′) = no λ ()
(A ∨ B) ≟ᵀ ⊤        = no λ ()
(A ∨ B) ≟ᵀ ⊥        = no λ ()
(A ∨ B) ≟ᵀ (A′ ∨ B′) with A ≟ᵀ A′ | B ≟ᵀ B′
(A ∨ B) ≟ᵀ (.A ∨ .B) | yes refl | yes refl = yes refl
(A ∨ B) ≟ᵀ (A′ ∨ B′) | no  A≢A′ | _        = no (A≢A′ ∘ inv∨₁)
(A ∨ B) ≟ᵀ (A′ ∨ B′) | _        | no  B≢B′ = no (B≢B′ ∘ inv∨₂)

open ContextEquality (_≟ᵀ_) public
