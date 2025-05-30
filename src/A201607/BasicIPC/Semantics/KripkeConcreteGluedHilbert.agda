{-# OPTIONS --sized-types #-}

-- Basic intuitionistic propositional calculus, without ∨ or ⊥.
-- Kripke-style semantics with contexts as concrete worlds, and glueing for α and ▻.
-- Hilbert-style syntax.

module A201607.BasicIPC.Semantics.KripkeConcreteGluedHilbert where

open import A201607.BasicIPC.Syntax.Common public
open import A201607.Common.Semantics public

open ConcreteWorlds (Ty) public


-- Partial intuitionistic Kripke models with explicit syntax.

record Model : Set₁ where
  infix 3 _⊩ᵅ_ _[⊢]_
  field
    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_   : World → Atom → Set
    mono⊩ᵅ : ∀ {P w w′} → w ≤ w′ → w ⊩ᵅ P → w′ ⊩ᵅ P

    -- Hilbert-style syntax representation; monotonic.
    _[⊢]_   : Cx Ty → Ty → Set
    mono[⊢] : ∀ {A Γ Γ′}  → Γ ⊆ Γ′ → Γ [⊢] A → Γ′ [⊢] A
    [var]    : ∀ {A Γ}     → A ∈ Γ → Γ [⊢] A
    [app]    : ∀ {A B Γ}   → Γ [⊢] A ▻ B → Γ [⊢] A → Γ [⊢] B
    [ci]     : ∀ {A Γ}     → Γ [⊢] A ▻ A
    [ck]     : ∀ {A B Γ}   → Γ [⊢] A ▻ B ▻ A
    [cs]     : ∀ {A B C Γ} → Γ [⊢] (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
    [cpair]  : ∀ {A B Γ}   → Γ [⊢] A ▻ B ▻ A ∧ B
    [cfst]   : ∀ {A B Γ}   → Γ [⊢] A ∧ B ▻ A
    [csnd]   : ∀ {A B Γ}   → Γ [⊢] A ∧ B ▻ B
    [unit]   : ∀ {Γ}       → Γ [⊢] ⊤

    -- NOTE: [lam] is necessary to give meaning to Gentzen-style syntax.
    [lam] : ∀ {A B Γ} → Γ , A [⊢] B → Γ [⊢] A ▻ B

  infix 3 _[⊢]⋆_
  _[⊢]⋆_ : Cx Ty → Cx Ty → Set
  Γ [⊢]⋆ ∅     = 𝟙
  Γ [⊢]⋆ Ξ , A = Γ [⊢]⋆ Ξ × Γ [⊢] A

open Model {{…}} public


-- Forcing in a particular world of a particular model.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Ty → Set
  w ⊩ α P   = Glue (unwrap w [⊢] α P) (w ⊩ᵅ P)
  w ⊩ A ▻ B = Glue (unwrap w [⊢] (A ▻ B)) (∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B)
  w ⊩ A ∧ B = w ⊩ A × w ⊩ B
  w ⊩ ⊤    = 𝟙

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ∅     = 𝟙
  w ⊩⋆ Ξ , A = w ⊩⋆ Ξ × w ⊩ A


-- Monotonicity with respect to context inclusion.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}   ξ s = mono[⊢] (unwrap≤ ξ) (syn s) ⅋ mono⊩ᵅ ξ (sem s)
  mono⊩ {A ▻ B} ξ s = mono[⊢] (unwrap≤ ξ) (syn s) ⅋ λ ξ′ → sem s (trans≤ ξ ξ′)
  mono⊩ {A ∧ B} ξ s = mono⊩ {A} ξ (π₁ s) , mono⊩ {B} ξ (π₂ s)
  mono⊩ {⊤}    ξ s = ∙

  mono⊩⋆ : ∀ {Ξ w w′} → w ≤ w′ → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ {∅}     ξ ∙        = ∙
  mono⊩⋆ {Ξ , A} ξ (ts , t) = mono⊩⋆ {Ξ} ξ ts , mono⊩ {A} ξ t


-- Extraction of syntax representation in a particular model.

module _ {{_ : Model}} where
  reifyʳ : ∀ {A w} → w ⊩ A → unwrap w [⊢] A
  reifyʳ {α P}   s = syn s
  reifyʳ {A ▻ B} s = syn s
  reifyʳ {A ∧ B} s = [app] ([app] [cpair] (reifyʳ {A} (π₁ s))) (reifyʳ {B} (π₂ s))
  reifyʳ {⊤}    s = [unit]

  reifyʳ⋆ : ∀ {Ξ w} → w ⊩⋆ Ξ → unwrap w [⊢]⋆ Ξ
  reifyʳ⋆ {∅}     ∙        = ∙
  reifyʳ⋆ {Ξ , A} (ts , t) = reifyʳ⋆ ts , reifyʳ t


-- Useful theorems in functional form.

module _ {{_ : Model}} where
  [multicut] : ∀ {Ξ A Γ} → Γ [⊢]⋆ Ξ → Ξ [⊢] A → Γ [⊢] A
  [multicut] {∅}     ∙        u = mono[⊢] bot⊆ u
  [multicut] {Ξ , B} (ts , t) u = [app] ([multicut] ts ([lam] u)) t

  [pair] : ∀ {A B Γ} → Γ [⊢] A → Γ [⊢] B → Γ [⊢] A ∧ B
  [pair] t u = [app] ([app] [cpair] t) u

  [fst] : ∀ {A B Γ} → Γ [⊢] A ∧ B → Γ [⊢] A
  [fst] t = [app] [cfst] t

  [snd] : ∀ {A B Γ} → Γ [⊢] A ∧ B → Γ [⊢] B
  [snd] t = [app] [csnd] t


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B w} → w ⊩ A ▻ B → w ⊩ A → w ⊩ B
  s ⟪$⟫ a = sem s refl≤ a

  ⟪K⟫ : ∀ {A B w} → w ⊩ A → w ⊩ B ▻ A
  ⟪K⟫ {A} a = [app] [ck] (reifyʳ a) ⅋ λ ξ →
                K (mono⊩ {A} ξ a)

  ⟪S⟫ : ∀ {A B C w} → w ⊩ A ▻ B ▻ C → w ⊩ A ▻ B → w ⊩ A → w ⊩ C
  ⟪S⟫ s₁ s₂ a = (s₁ ⟪$⟫ a) ⟪$⟫ (s₂ ⟪$⟫ a)

  ⟪S⟫′ : ∀ {A B C w} → w ⊩ A ▻ B ▻ C → w ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} s₁ = [app] [cs] (syn s₁) ⅋ λ ξ s₂ →
                          [app] ([app] [cs] (mono[⊢] (unwrap≤ ξ) (syn s₁))) (syn s₂) ⅋ λ ξ′ →
                            ⟪S⟫ (mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) s₁) (mono⊩ {A ▻ B} ξ′ s₂)

  _⟪,⟫′_ : ∀ {A B w} → w ⊩ A → w ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} a = [app] [cpair] (reifyʳ a) ⅋ λ ξ →
                   _,_ (mono⊩ {A} ξ a)


-- Forcing in a particular world of a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⊩_⇒_
  _⊩_⇒_ : World → Cx Ty → Ty → Set
  w ⊩ Γ ⇒ A = w ⊩⋆ Γ → w ⊩ A

  infix 3 _⊩_⇒⋆_
  _⊩_⇒⋆_ : World → Cx Ty → Cx Ty → Set
  w ⊩ Γ ⇒⋆ Ξ = w ⊩⋆ Γ → w ⊩⋆ Ξ


-- Entailment, or forcing in all worlds of all models, for sequents.

infix 3 _⊨_
_⊨_ : Cx Ty → Ty → Set₁
Γ ⊨ A = ∀ {{_ : Model}} {w : World} → w ⊩ Γ ⇒ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx Ty → Cx Ty → Set₁
Γ ⊨⋆ Ξ = ∀ {{_ : Model}} {w : World} → w ⊩ Γ ⇒⋆ Ξ


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  _⟦$⟧_ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B
  (s₁ ⟦$⟧ s₂) γ = s₁ γ ⟪$⟫ s₂ γ

  ⟦K⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B ▻ A
  ⟦K⟧ {A} {B} a γ = ⟪K⟫ {A} {B} (a γ)

  ⟦S⟧ : ∀ {A B C Γ w} → w ⊩ Γ ⇒ A ▻ B ▻ C → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ C
  ⟦S⟧ s₁ s₂ a γ = ⟪S⟫ (s₁ γ) (s₂ γ) (a γ)

  _⟦,⟧_ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B → w ⊩ Γ ⇒ A ∧ B
  (a ⟦,⟧ b) γ = a γ , b γ

  ⟦π₁⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ∧ B → w ⊩ Γ ⇒ A
  ⟦π₁⟧ s γ = π₁ (s γ)

  ⟦π₂⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ∧ B → w ⊩ Γ ⇒ B
  ⟦π₂⟧ s γ = π₂ (s γ)
