-- Basic intuitionistic propositional calculus, without ∨ or ⊥.
-- Tarski-style semantics with contexts as concrete worlds, and glueing for α and ▻.
-- Implicit syntax.

module BasicIPC.Semantics.TarskiGluedImplicit where

open import BasicIPC.Syntax.Common public
open import Common.Semantics public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_   : Cx Ty → Atom → Set
    mono⊩ᵅ : ∀ {P w w′} → w ⊆ w′ → w ⊩ᵅ P → w′ ⊩ᵅ P

open Model {{…}} public




module ImplicitSyntax
    (_[⊢]_   : Cx Ty → Ty → Set)
    (mono[⊢] : ∀ {A w w′} → w ⊆ w′ → w [⊢] A → w′ [⊢] A)
  where


  -- Forcing in a particular world of a particular model.

  module _ {{_ : Model}} where
    infix 3 _⊩_
    _⊩_ : Cx Ty → Ty → Set
    w ⊩ α P   = Glue (w [⊢] (α P)) (w ⊩ᵅ P)
    w ⊩ A ▻ B = ∀ {w′} → w ⊆ w′ → Glue (w′ [⊢] (A ▻ B)) (w′ ⊩ A → w′ ⊩ B)
    w ⊩ A ∧ B = w ⊩ A × w ⊩ B
    w ⊩ ⊤    = 𝟙

    infix 3 _⊩⋆_
    _⊩⋆_ : Cx Ty → Cx Ty → Set
    w ⊩⋆ ∅     = 𝟙
    w ⊩⋆ Ξ , A = w ⊩⋆ Ξ × w ⊩ A


  -- Monotonicity with respect to context inclusion.

  module _ {{_ : Model}} where
    mono⊩ : ∀ {A w w′} → w ⊆ w′ → w ⊩ A → w′ ⊩ A
    mono⊩ {α P}   η s = mono[⊢] η (syn s) ⅋ mono⊩ᵅ η (sem s)
    mono⊩ {A ▻ B} η s = λ η′ → s (trans⊆ η η′)
    mono⊩ {A ∧ B} η s = mono⊩ {A} η (π₁ s) , mono⊩ {B} η (π₂ s)
    mono⊩ {⊤}    η s = ∙

    mono⊩⋆ : ∀ {Ξ w w′} → w ⊆ w′ → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
    mono⊩⋆ {∅}     η ∙        = ∙
    mono⊩⋆ {Ξ , A} η (ts , t) = mono⊩⋆ {Ξ} η ts , mono⊩ {A} η t


  -- Additional useful equipment.

  module _ {{_ : Model}} where
    _⟪$⟫_ : ∀ {A B w} → w ⊩ A ▻ B → w ⊩ A → w ⊩ B
    s ⟪$⟫ a = sem (s refl⊆) a

    ⟪S⟫ : ∀ {A B C w} → w ⊩ A ▻ B ▻ C → w ⊩ A ▻ B → w ⊩ A → w ⊩ C
    ⟪S⟫ s₁ s₂ a = (s₁ ⟪$⟫ a) ⟪$⟫ (s₂ ⟪$⟫ a)


  -- Forcing in a particular world of a particular model, for sequents.

  module _ {{_ : Model}} where
    infix 3 _⊩_⇒_
    _⊩_⇒_ : Cx Ty → Cx Ty → Ty → Set
    w ⊩ Γ ⇒ A = w ⊩⋆ Γ → w ⊩ A

    infix 3 _⊩_⇒⋆_
    _⊩_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
    w ⊩ Γ ⇒⋆ Ξ = w ⊩⋆ Γ → w ⊩⋆ Ξ


  -- Entailment, or forcing in all worlds of all models, for sequents.

  infix 3 _⊨_
  _⊨_ : Cx Ty → Ty → Set₁
  Γ ⊨ A = ∀ {{_ : Model}} {w : Cx Ty} → w ⊩ Γ ⇒ A

  infix 3 _⊨⋆_
  _⊨⋆_ : Cx Ty → Cx Ty → Set₁
  Γ ⊨⋆ Ξ = ∀ {{_ : Model}} {w : Cx Ty} → w ⊩ Γ ⇒⋆ Ξ


  -- Additional useful equipment, for sequents.

  module _ {{_ : Model}} where
    lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩ Γ ⇒ A
    lookup top     (γ , a) = a
    lookup (pop i) (γ , b) = lookup i γ

    _⟦$⟧_ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B
    (s₁ ⟦$⟧ s₂) γ = s₁ γ ⟪$⟫ s₂ γ

    ⟦S⟧ : ∀ {A B C Γ w} → w ⊩ Γ ⇒ A ▻ B ▻ C → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ C
    ⟦S⟧ s₁ s₂ a γ = ⟪S⟫ (s₁ γ) (s₂ γ) (a γ)

    _⟦,⟧_ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B → w ⊩ Γ ⇒ A ∧ B
    (a ⟦,⟧ b) γ = a γ , b γ

    ⟦π₁⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ∧ B → w ⊩ Γ ⇒ A
    ⟦π₁⟧ s γ = π₁ (s γ)

    ⟦π₂⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ∧ B → w ⊩ Γ ⇒ B
    ⟦π₂⟧ s γ = π₂ (s γ)
