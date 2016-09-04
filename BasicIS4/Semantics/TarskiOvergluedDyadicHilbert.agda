-- Basic intuitionistic modal logic S4, without ∨, ⊥, or ◇.
-- Tarski-style semantics with context pairs as concrete worlds, and glueing for α, ▻, and □.
-- Hilbert-style syntax.

module BasicIS4.Semantics.TarskiOvergluedDyadicHilbert where

open import BasicIS4.Syntax.Common public
open import Common.Semantics public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_ _[⊢]_
  field
    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_    : Cx² Ty Ty → Atom → Set
    mono²⊩ᵅ : ∀ {P Π Π′} → Π ⊆² Π′ → Π ⊩ᵅ P → Π′ ⊩ᵅ P

    -- Hilbert-style syntax representation; monotonic.
    _[⊢]_    : Cx² Ty Ty → Ty → Set
    mono²[⊢] : ∀ {A Π Π′}    → Π ⊆² Π′ → Π [⊢] A → Π′ [⊢] A
    [var]     : ∀ {A Γ Δ}     → A ∈ Γ → Γ ⁏ Δ [⊢] A
    [app]     : ∀ {A B Γ Δ}   → Γ ⁏ Δ [⊢] A ▻ B → Γ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] B
    [ci]      : ∀ {A Γ Δ}     → Γ ⁏ Δ [⊢] A ▻ A
    [ck]      : ∀ {A B Γ Δ}   → Γ ⁏ Δ [⊢] A ▻ B ▻ A
    [cs]      : ∀ {A B C Γ Δ} → Γ ⁏ Δ [⊢] (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
    [mvar]    : ∀ {A Γ Δ}     → A ∈ Δ → Γ ⁏ Δ [⊢] A
    [box]     : ∀ {A Γ Δ}     → ∅ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] □ A
    [cdist]   : ∀ {A B Γ Δ}   → Γ ⁏ Δ [⊢] □ (A ▻ B) ▻ □ A ▻ □ B
    [cup]     : ∀ {A Γ Δ}     → Γ ⁏ Δ [⊢] □ A ▻ □ □ A
    [cdown]   : ∀ {A Γ Δ}     → Γ ⁏ Δ [⊢] □ A ▻ A
    [cpair]   : ∀ {A B Γ Δ}   → Γ ⁏ Δ [⊢] A ▻ B ▻ A ∧ B
    [cfst]    : ∀ {A B Γ Δ}   → Γ ⁏ Δ [⊢] A ∧ B ▻ A
    [csnd]    : ∀ {A B Γ Δ}   → Γ ⁏ Δ [⊢] A ∧ B ▻ B
    [tt]      : ∀ {Γ Δ}       → Γ ⁏ Δ [⊢] ⊤

    -- NOTE: [mlam] is necessary for [mmulticut], which is necessary for eval.
    [mlam] : ∀ {A B Γ Δ} → Γ ⁏ Δ , A [⊢] B → Γ ⁏ Δ [⊢] □ A ▻ B

  infix 3 _[⊢]⋆_
  _[⊢]⋆_ : Cx² Ty Ty → Cx Ty → Set
  Π [⊢]⋆ ∅     = 𝟙
  Π [⊢]⋆ Ξ , A = Π [⊢]⋆ Ξ × Π [⊢] A

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : Cx² Ty Ty → Ty → Set
  Π ⊩ α P   = Glue (Π [⊢] α P) (Π ⊩ᵅ P)
  Π ⊩ A ▻ B = ∀ {Π′} → Π ⊆² Π′ → Glue (Π′ [⊢] A ▻ B) (Π′ ⊩ A → Π′ ⊩ B)
  Π ⊩ □ A   = ∀ {Π′} → Π ⊆² Π′ → Glue (Π′ [⊢] □ A) (Π′ ⊩ A)
  Π ⊩ A ∧ B = Π ⊩ A × Π ⊩ B
  Π ⊩ ⊤    = 𝟙

  infix 3 _⊩⋆_
  _⊩⋆_ : Cx² Ty Ty → Cx Ty → Set
  Π ⊩⋆ ∅     = 𝟙
  Π ⊩⋆ Ξ , A = Π ⊩⋆ Ξ × Π ⊩ A


-- Monotonicity with respect to context inclusion.

module _ {{_ : Model}} where
  mono²⊩ : ∀ {A Π Π′} → Π ⊆² Π′ → Π ⊩ A → Π′ ⊩ A
  mono²⊩ {α P}   ψ s = mono²[⊢] ψ (syn s) ⅋ mono²⊩ᵅ ψ (sem s)
  mono²⊩ {A ▻ B} ψ s = λ ψ′ → s (trans⊆² ψ ψ′)
  mono²⊩ {□ A}   ψ s = λ ψ′ → s (trans⊆² ψ ψ′)
  mono²⊩ {A ∧ B} ψ s = mono²⊩ {A} ψ (π₁ s) , mono²⊩ {B} ψ (π₂ s)
  mono²⊩ {⊤}    ψ s = ∙

  mono²⊩⋆ : ∀ {Ξ Π Π′} → Π ⊆² Π′ → Π ⊩⋆ Ξ → Π′ ⊩⋆ Ξ
  mono²⊩⋆ {∅}     ψ ∙        = ∙
  mono²⊩⋆ {Ξ , A} ψ (ts , t) = mono²⊩⋆ ψ ts , mono²⊩ {A} ψ t


-- Extraction of syntax representation in a particular model.

module _ {{_ : Model}} where
  reifyʳ : ∀ {A Π} → Π ⊩ A → Π [⊢] A
  reifyʳ {α P}   s = syn s
  reifyʳ {A ▻ B} s = syn (s refl⊆²)
  reifyʳ {□ A}   s = syn (s refl⊆²)
  reifyʳ {A ∧ B} s = [app] ([app] [cpair] (reifyʳ {A} (π₁ s))) (reifyʳ {B} (π₂ s))
  reifyʳ {⊤}    s = [tt]

  reifyʳ⋆ : ∀ {Ξ Π} → Π ⊩⋆ Ξ → Π [⊢]⋆ Ξ
  reifyʳ⋆ {∅}     ∙        = ∙
  reifyʳ⋆ {Ξ , A} (ts , t) = reifyʳ⋆ ts , reifyʳ t


-- Useful theorems in functional form.

module _ {{_ : Model}} where
  [mmulticut] : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ [⊢]⋆ □⋆ Ξ → Γ ⁏ Ξ [⊢] A → Γ ⁏ Δ [⊢] A
  [mmulticut] {∅}     ∙        u = mono²[⊢] (refl⊆ , bot⊆) u
  [mmulticut] {Ξ , B} (ts , t) u = [app] ([mmulticut] ts ([mlam] u)) t


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B Π} → Π ⊩ A ▻ B → Π ⊩ A → Π ⊩ B
  s ⟪$⟫ a = sem (s refl⊆²) a

  ⟪K⟫ : ∀ {A B Π} → Π ⊩ A → Π ⊩ B ▻ A
  ⟪K⟫ {A} a ψ = let a′ = mono²⊩ {A} ψ a
                in  [app] [ck] (reifyʳ a′) ⅋ K a′

  ⟪S⟫ : ∀ {A B C Π} → Π ⊩ A ▻ B ▻ C → Π ⊩ A ▻ B → Π ⊩ A → Π ⊩ C
  ⟪S⟫ s₁ s₂ a = (s₁ ⟪$⟫ a) ⟪$⟫ (s₂ ⟪$⟫ a)

  ⟪S⟫′ : ∀ {A B C Π} → Π ⊩ A ▻ B ▻ C → Π ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} s₁ ψ = let s₁′ = mono²⊩ {A ▻ B ▻ C} ψ s₁
                              t   = syn (s₁′ refl⊆²)
                          in  [app] [cs] t ⅋ λ s₂ ψ′ →
                              let s₁″ = mono²⊩ {A ▻ B ▻ C} (trans⊆² ψ ψ′) s₁
                                  s₂′ = mono²⊩ {A ▻ B} ψ′ s₂
                                  t′  = syn (s₁″ refl⊆²)
                                  u   = syn (s₂′ refl⊆²)
                              in  [app] ([app] [cs] t′) u ⅋ ⟪S⟫ s₁″ s₂′

  _⟪D⟫_ : ∀ {A B Π} → Π ⊩ □ (A ▻ B) → Π ⊩ □ A → Π ⊩ □ B
  (s₁ ⟪D⟫ s₂) ψ = let t ⅋ s₁′ = s₁ ψ
                      u ⅋ a   = s₂ ψ
                  in  [app] ([app] [cdist] t) u ⅋ s₁′ ⟪$⟫ a

  _⟪D⟫′_ : ∀ {A B Π} → Π ⊩ □ (A ▻ B) → Π ⊩ □ A ▻ □ B
  _⟪D⟫′_ {A} {B} s₁ ψ = let s₁′ = mono²⊩ {□ (A ▻ B)} ψ s₁
                        in  [app] [cdist] (reifyʳ (λ {_} ψ′ → s₁′ ψ′)) ⅋ _⟪D⟫_ s₁′

  ⟪↑⟫ : ∀ {A Π} → Π ⊩ □ A → Π ⊩ □ □ A
  ⟪↑⟫ {A} s ψ = [app] [cup] (syn (s ψ)) ⅋ λ ψ′ → s (trans⊆² ψ ψ′)

  ⟪↓⟫ : ∀ {A Π} → Π ⊩ □ A → Π ⊩ A
  ⟪↓⟫ s = sem (s refl⊆²)

  _⟪,⟫′_ : ∀ {A B Π} → Π ⊩ A → Π ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} a ψ = let a′ = mono²⊩ {A} ψ a
                   in  [app] [cpair] (reifyʳ a′) ⅋ _,_ a′


-- Forcing in a particular world of a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⊩_⇒_
  _⊩_⇒_ : Cx² Ty Ty → Cx² Ty Ty → Ty → Set
  Π ⊩ Γ ⁏ Δ ⇒ A = Π ⊩⋆ Γ → Π ⊩⋆ □⋆ Δ → Π ⊩ A

  infix 3 _⊩_⇒⋆_
  _⊩_⇒⋆_ : Cx² Ty Ty → Cx² Ty Ty → Cx Ty → Set
  Π ⊩ Γ ⁏ Δ ⇒⋆ Ξ = Π ⊩⋆ Γ → Π ⊩⋆ □⋆ Δ → Π ⊩⋆ Ξ


-- Entailment, or forcing in all worlds of all models, for sequents.

infix 3 _⊨_
_⊨_ : Cx² Ty Ty → Ty → Set₁
Π ⊨ A = ∀ {{_ : Model}} {w : Cx² Ty Ty} → w ⊩ Π ⇒ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx² Ty Ty → Cx Ty → Set₁
Π ⊨⋆ Ξ = ∀ {{_ : Model}} {w : Cx² Ty Ty} → w ⊩ Π ⇒⋆ Ξ


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩⋆ Γ → w ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  mlookup : ∀ {A Δ w} → A ∈ Δ → w ⊩⋆ □⋆ Δ → w ⊩ A
  mlookup top     (γ , s) = sem (s refl⊆²)
  mlookup (pop i) (γ , s) = mlookup i γ

  -- TODO: More equipment.
