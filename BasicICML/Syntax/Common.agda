-- Common syntax.

module BasicICML.Syntax.Common where

open import Common.ContextPair public


-- Types, or propositions.
-- [ Ψ ] A means the type A is inhabited given assumptions in the context Ψ.

infixr 10 [_]_
infixl 9 _∧_
infixr 7 _▻_
data Ty : Set where
  α_   : Atom → Ty
  _▻_  : Ty → Ty → Ty
  [_]_ : Cx Ty → Ty → Ty
  _∧_  : Ty → Ty → Ty
  ⊤   : Ty


-- Context/type pairs.

record Box : Set where
  inductive
  constructor [_]_
  field
    Ψ : Cx Ty
    A : Ty


-- Additional useful types.

infix 7 _▻◅_
_▻◅_ : Ty → Ty → Ty
A ▻◅ B = (A ▻ B) ∧ (B ▻ A)

infixr 7 _▻⋯▻_
_▻⋯▻_ : Cx Ty → Ty → Ty
∅       ▻⋯▻ B = B
(Ξ , A) ▻⋯▻ B = Ξ ▻⋯▻ (A ▻ B)

infixr 10 [_]⋆_
[_]⋆_ : Cx Ty → Cx Ty → Cx Box
[ Ψ ]⋆ ∅       = ∅
[ Ψ ]⋆ (Ξ , A) = [ Ψ ]⋆ Ξ , [ Ψ ] A


-- Inversion principles.

invα : ∀ {P P′} → α P ≡ α P′ → P ≡ P′
invα refl = refl

inv▻₁ : ∀ {A A′ B B′} → A ▻ B ≡ A′ ▻ B′ → A ≡ A′
inv▻₁ refl = refl

inv▻₂ : ∀ {A A′ B B′} → A ▻ B ≡ A′ ▻ B′ → B ≡ B′
inv▻₂ refl = refl

inv□₁ : ∀ {A A′ Ψ Ψ′} → Ty.[ Ψ ] A ≡ [ Ψ′ ] A′ → Ψ ≡ Ψ′
inv□₁ refl = refl

inv□₂ : ∀ {A A′ Ψ Ψ′} → Ty.[ Ψ ] A ≡ [ Ψ′ ] A′ → A ≡ A′
inv□₂ refl = refl

inv∧₁ : ∀ {A A′ B B′} → A ∧ B ≡ A′ ∧ B′ → A ≡ A′
inv∧₁ refl = refl

inv∧₂ : ∀ {A A′ B B′} → A ∧ B ≡ A′ ∧ B′ → B ≡ B′
inv∧₂ refl = refl


-- Decidable equality on types.

-- FIXME: How to show this?
{-# TERMINATING #-}
_≟ᵀ_ : (A A′ : Ty) → Dec (A ≡ A′)
(α P)     ≟ᵀ (α P′)      with P ≟ᵅ P′
(α P)     ≟ᵀ (α .P)      | yes refl = yes refl
(α P)     ≟ᵀ (α P′)      | no  P≢P′ = no (P≢P′ ∘ invα)
(α P)     ≟ᵀ (A′ ▻ B′)   = no λ ()
(α P)     ≟ᵀ ([ Ψ′ ] A′) = no λ ()
(α P)     ≟ᵀ (A′ ∧ B′)   = no λ ()
(α P)     ≟ᵀ ⊤          = no λ ()
(A ▻ B)   ≟ᵀ (α P′)      = no λ ()
(A ▻ B)   ≟ᵀ (A′ ▻ B′)   with A ≟ᵀ A′ | B ≟ᵀ B′
(A ▻ B)   ≟ᵀ (.A ▻ .B)   | yes refl | yes refl = yes refl
(A ▻ B)   ≟ᵀ (A′ ▻ B′)   | no  A≢A′ | _        = no (A≢A′ ∘ inv▻₁)
(A ▻ B)   ≟ᵀ (A′ ▻ B′)   | _        | no  B≢B′ = no (B≢B′ ∘ inv▻₂)
(A ▻ B)   ≟ᵀ ([ Ψ′ ] A′) = no λ ()
(A ▻ B)   ≟ᵀ (A′ ∧ B′)   = no λ ()
(A ▻ B)   ≟ᵀ ⊤          = no λ ()
([ Ψ ] A) ≟ᵀ (α P′)      = no λ ()
([ Ψ ] A) ≟ᵀ (A′ ▻ B′)   = no λ ()
([ Ψ ] A) ≟ᵀ ([ Ψ′ ] A′) with ContextEquality._≟ᵀ⋆_ _≟ᵀ_ Ψ Ψ′ | A ≟ᵀ A′
([ Ψ ] A) ≟ᵀ ([ .Ψ ] .A) | yes refl | yes refl = yes refl
([ Ψ ] A) ≟ᵀ ([ Ψ′ ] A′) | no Ψ≢Ψ′  | _        = no (Ψ≢Ψ′ ∘ inv□₁)
([ Ψ ] A) ≟ᵀ ([ Ψ′ ] A′) | _        | no  A≢A′ = no (A≢A′ ∘ inv□₂)
([ Ψ ] A) ≟ᵀ (A′ ∧ B′)   = no λ ()
([ Ψ ] A) ≟ᵀ ⊤          = no λ ()
(A ∧ B)   ≟ᵀ (α P′)      = no λ ()
(A ∧ B)   ≟ᵀ (A′ ▻ B′)   = no λ ()
(A ∧ B)   ≟ᵀ ([ Ψ′ ] A′) = no λ ()
(A ∧ B)   ≟ᵀ (A′ ∧ B′)   with A ≟ᵀ A′ | B ≟ᵀ B′
(A ∧ B)   ≟ᵀ (.A ∧ .B)   | yes refl | yes refl = yes refl
(A ∧ B)   ≟ᵀ (A′ ∧ B′)   | no  A≢A′ | _        = no (A≢A′ ∘ inv∧₁)
(A ∧ B)   ≟ᵀ (A′ ∧ B′)   | _        | no  B≢B′ = no (B≢B′ ∘ inv∧₂)
(A ∧ B)   ≟ᵀ ⊤          = no λ ()
⊤        ≟ᵀ (α P′)      = no λ ()
⊤        ≟ᵀ (A′ ▻ B′)   = no λ ()
⊤        ≟ᵀ ([ Ψ′ ] A′) = no λ ()
⊤        ≟ᵀ (A′ ∧ B′)   = no λ ()
⊤        ≟ᵀ ⊤          = yes refl

open ContextEquality (_≟ᵀ_) public
