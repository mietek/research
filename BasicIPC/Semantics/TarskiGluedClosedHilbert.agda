-- Basic intuitionistic propositional calculus, without ∨ or ⊥.
-- Tarski-style semantics with glueing for α and ▻, after Coquand-Dybjer.
-- Hilbert-style closed syntax.

module BasicIPC.Semantics.TarskiGluedClosedHilbert where

open import BasicIPC.Syntax.Common public
open import Common.Semantics public


-- Tarski models with explicit syntax.

record Model : Set₁ where
  infix 3 ⊩ᵅ_ [⊢]_
  field
    -- Forcing for atomic propositions.
    ⊩ᵅ_ : Atom → Set

    -- Hilbert-style closed syntax representation.
    [⊢]_   : Ty → Set
    [app]   : ∀ {A B}   → [⊢] A ▻ B  → [⊢] A → [⊢] B
    [ci]    : ∀ {A}     → [⊢] A ▻ A
    [ck]    : ∀ {A B}   → [⊢] A ▻ B ▻ A
    [cs]    : ∀ {A B C} → [⊢] (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
    [cpair] : ∀ {A B}   → [⊢] A ▻ B ▻ A ∧ B
    [cfst]  : ∀ {A B}   → [⊢] A ∧ B ▻ A
    [csnd]  : ∀ {A B}   → [⊢] A ∧ B ▻ B
    [unit]  : [⊢] ⊤

  infix 3 [⊢]⋆_
  [⊢]⋆_ : Cx Ty → Set
  [⊢]⋆ ∅     = 𝟙
  [⊢]⋆ Ξ , A = [⊢]⋆ Ξ × [⊢] A

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 ⊩_
  ⊩_ : Ty → Set
  ⊩ α P   = Glue ([⊢] α P) (⊩ᵅ P)
  ⊩ A ▻ B = Glue ([⊢] A ▻ B) (⊩ A → ⊩ B)
  ⊩ A ∧ B = ⊩ A × ⊩ B
  ⊩ ⊤    = 𝟙

  infix 3 ⊩⋆_
  ⊩⋆_ : Cx Ty → Set
  ⊩⋆ ∅     = 𝟙
  ⊩⋆ Ξ , A = ⊩⋆ Ξ × ⊩ A


-- Entailment, or forcing in all models.

infix 3 ⊨_
⊨_ : Ty → Set₁
⊨ A = ∀ {{_ : Model}} → ⊩ A


-- Extraction of syntax representation in a particular model.

module _ {{_ : Model}} where
  reifyʳ : ∀ {A} → ⊩ A → [⊢] A
  reifyʳ {α P}   s = syn s
  reifyʳ {A ▻ B} s = syn s
  reifyʳ {A ∧ B} s = [app] ([app] [cpair] (reifyʳ (π₁ s))) (reifyʳ (π₂ s))
  reifyʳ {⊤}    s = [unit]

  reifyʳ⋆ : ∀ {Ξ} → ⊩⋆ Ξ → [⊢]⋆ Ξ
  reifyʳ⋆ {∅}     ∙        = ∙
  reifyʳ⋆ {Ξ , A} (ts , t) = reifyʳ⋆ ts , reifyʳ t


-- Useful theorems in functional form.

module _ {{_ : Model}} where
  [multicut] : ∀ {Ξ A} → [⊢]⋆ Ξ → [⊢] Ξ ▻⋯▻ A → [⊢] A
  [multicut] {∅}     ∙        u = u
  [multicut] {Ξ , B} (ts , t) u = [app] ([multicut] ts u) t


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B} → ⊩ A ▻ B → ⊩ A → ⊩ B
  s ⟪$⟫ a = sem s a

  ⟪K⟫ : ∀ {A B} → ⊩ A → ⊩ B ▻ A
  ⟪K⟫ a = [app] [ck] (reifyʳ a) ⅋ K a

  ⟪S⟫ : ∀ {A B C} → ⊩ A ▻ B ▻ C → ⊩ A ▻ B → ⊩ A → ⊩ C
  ⟪S⟫ s₁ s₂ a = (s₁ ⟪$⟫ a) ⟪$⟫ (s₂ ⟪$⟫ a)

  ⟪S⟫′ : ∀ {A B C} → ⊩ A ▻ B ▻ C → ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ s₁ = [app] [cs] (reifyʳ s₁) ⅋ λ s₂ →
              [app] ([app] [cs] (reifyʳ s₁)) (reifyʳ s₂) ⅋ ⟪S⟫ s₁ s₂

  _⟪,⟫′_ : ∀ {A B} → ⊩ A → ⊩ B ▻ A ∧ B
  _⟪,⟫′_ a = [app] [cpair] (reifyʳ a) ⅋ _,_ a


-- Forcing in a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 ⊩_⇒_
  ⊩_⇒_ : Cx Ty → Ty → Set
  ⊩ Γ ⇒ A = ⊩⋆ Γ → ⊩ A

  infix 3 ⊩_⇒⋆_
  ⊩_⇒⋆_ : Cx Ty → Cx Ty → Set
  ⊩ Γ ⇒⋆ Ξ = ⊩⋆ Γ → ⊩⋆ Ξ


-- Entailment, or forcing in all models, for sequents.

infix 3 _⊨_
_⊨_ : Cx Ty → Ty → Set₁
Γ ⊨ A = ∀ {{_ : Model}} → ⊩ Γ ⇒ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx Ty → Cx Ty → Set₁
Γ ⊨⋆ Ξ = ∀ {{_ : Model}} → ⊩ Γ ⇒⋆ Ξ


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ} → A ∈ Γ → ⊩ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  ⟦λ⟧ : ∀ {A B Γ} → [⊢] A ▻ B → ⊩ Γ , A ⇒ B → ⊩ Γ ⇒ A ▻ B
  ⟦λ⟧ t s γ = t ⅋ λ a → s (γ , a)

  _⟦$⟧_ : ∀ {A B Γ} → ⊩ Γ ⇒ A ▻ B → ⊩ Γ ⇒ A → ⊩ Γ ⇒ B
  (s₁ ⟦$⟧ s₂) γ = s₁ γ ⟪$⟫ s₂ γ

  ⟦K⟧ : ∀ {A B Γ} → ⊩ Γ ⇒ A → ⊩ Γ ⇒ B ▻ A
  ⟦K⟧ {A} {B} a γ = ⟪K⟫ {A} {B} (a γ)

  ⟦S⟧ : ∀ {A B C Γ} → ⊩ Γ ⇒ A ▻ B ▻ C → ⊩ Γ ⇒ A ▻ B → ⊩ Γ ⇒ A → ⊩ Γ ⇒ C
  ⟦S⟧ s₁ s₂ a γ = ⟪S⟫ (s₁ γ) (s₂ γ) (a γ)

  _⟦,⟧_ : ∀ {A B Γ} → ⊩ Γ ⇒ A → ⊩ Γ ⇒ B → ⊩ Γ ⇒ A ∧ B
  (a ⟦,⟧ b) γ = a γ , b γ

  ⟦π₁⟧ : ∀ {A B Γ} → ⊩ Γ ⇒ A ∧ B → ⊩ Γ ⇒ A
  ⟦π₁⟧ s γ = π₁ (s γ)

  ⟦π₂⟧ : ∀ {A B Γ} → ⊩ Γ ⇒ A ∧ B → ⊩ Γ ⇒ B
  ⟦π₂⟧ s γ = π₂ (s γ)
