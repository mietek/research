-- Tarski-style semantics with context pairs as concrete worlds, and glueing for □ only.
-- Gentzen-style syntax.

module BasicIS4.Semantics.TarskiDyadic2 where

open import Common.ContextPair public
open import BasicIS4.Syntax.Common public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⁏_⊩ᵅ_ _⁏_[⊢]_
  field
    -- Forcing for atomic propositions; monotonic.
    _⁏_⊩ᵅ_  : Cx Ty → Cx Ty → Atom → Set
    mono⊩ᵅ  : ∀ {P Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩ᵅ P → Γ′ ⁏ Δ ⊩ᵅ P

    -- Gentzen-style syntax representation; monotonic.
    _⁏_[⊢]_ : Cx Ty → Cx Ty → Ty → Set
    mono[⊢] : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ [⊢] A → Γ′ ⁏ Δ [⊢] A
    [var]    : ∀ {A Γ Δ}    → A ∈ Γ → Γ ⁏ Δ [⊢] A
    [lam]    : ∀ {A B Γ Δ}  → Γ , A ⁏ Δ [⊢] B → Γ ⁏ Δ [⊢] A ▻ B
    [app]    : ∀ {A B Γ Δ}  → Γ ⁏ Δ [⊢] A ▻ B → Γ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] B
    [mvar]   : ∀ {A Γ Δ}    → A ∈ Δ → Γ ⁏ Δ [⊢] A
    [box]    : ∀ {A Γ Δ}    → ⌀ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] □ A
    [unbox]  : ∀ {A C Γ Δ}  → Γ ⁏ Δ [⊢] □ A → Γ ⁏ Δ , A [⊢] C → Γ ⁏ Δ [⊢] C
    [pair]   : ∀ {A B Γ Δ}  → Γ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] B → Γ ⁏ Δ [⊢] A ∧ B
    [fst]    : ∀ {A B Γ Δ}  → Γ ⁏ Δ [⊢] A ∧ B → Γ ⁏ Δ [⊢] A
    [snd]    : ∀ {A B Γ Δ}  → Γ ⁏ Δ [⊢] A ∧ B → Γ ⁏ Δ [⊢] B
    [tt]     : ∀ {Γ Δ}      → Γ ⁏ Δ [⊢] ⊤

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 _⁏_⊩_
  _⁏_⊩_ : Cx Ty → Cx Ty → Ty → Set
  Γ ⁏ Δ ⊩ α P   = Γ ⁏ Δ ⊩ᵅ P
  Γ ⁏ Δ ⊩ A ▻ B = ∀ {Γ′} → Γ ⊆ Γ′ → Γ′ ⁏ Δ ⊩ A → Γ′ ⁏ Δ ⊩ B
  Γ ⁏ Δ ⊩ □ A   = ∀ {Γ′} → Γ ⊆ Γ′ → Γ′ ⁏ Δ [⊢] □ A × Γ′ ⁏ Δ ⊩ A
  Γ ⁏ Δ ⊩ A ∧ B = Γ ⁏ Δ ⊩ A × Γ ⁏ Δ ⊩ B
  Γ ⁏ Δ ⊩ ⊤    = 𝟙

  infix 3 _⁏_⊩⋆_
  _⁏_⊩⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
  Γ ⁏ Δ ⊩⋆ ⌀     = 𝟙
  Γ ⁏ Δ ⊩⋆ Π , A = Γ ⁏ Δ ⊩⋆ Π × Γ ⁏ Δ ⊩ A


-- Monotonicity with respect to context inclusion.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩ A → Γ′ ⁏ Δ ⊩ A
  mono⊩ {α P}   η s       = mono⊩ᵅ η s
  mono⊩ {A ▻ B} η s       = λ η′ → s (trans⊆ η η′)
  mono⊩ {□ A}   η s       = λ η′ → s (trans⊆ η η′)
  mono⊩ {A ∧ B} η (a , b) = mono⊩ {A} η a , mono⊩ {B} η b
  mono⊩ {⊤}    η ∙       = ∙

  mono⊩⋆ : ∀ {Π Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩⋆ Π → Γ′ ⁏ Δ ⊩⋆ Π
  mono⊩⋆ {⌀}     η ∙        = ∙
  mono⊩⋆ {Π , A} η (ts , t) = mono⊩⋆ {Π} η ts , mono⊩ {A} η t


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B
  f ⟪$⟫ a = f refl⊆ a

  ⟪K⟫ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B ▻ A
  ⟪K⟫ {A} a η = K (mono⊩ {A} η a)

  ⟪S⟫′ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B ▻ C → Γ ⁏ Δ ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} f η g η′ a = let f′ = mono⊩ {A ▻ B ▻ C} (trans⊆ η η′) f
                                    g′ = mono⊩ {A ▻ B} η′ g
                                in  (f′ refl⊆ a) refl⊆ (g′ refl⊆ a)

  ⟪S⟫ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B ▻ C → Γ ⁏ Δ ⊩ A ▻ B → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ C
  ⟪S⟫ {A} {B} {C} f g a = ⟪S⟫′ {A} {B} {C} f refl⊆ g refl⊆ a

  ⟪↓⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ A
  ⟪↓⟫ s = let p , a = s refl⊆
          in  a

  _⟪,⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} {B} a η b = let a′ = mono⊩ {A} η a
                         in  a′ , b

  _⟪,⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B → Γ ⁏ Δ ⊩ A ∧ B
  _⟪,⟫_ {A} {B} a b = _⟪,⟫′_ {A} {B} a refl⊆ b


-- Forcing in a particular world of a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⁏_⊩_⇒_
  _⁏_⊩_⇒_ : Cx Ty → Cx Ty → Cx Ty → Ty → Set
  Γ₀ ⁏ Δ ⊩ Γ ⇒ A = Γ₀ ⁏ Δ ⊩⋆ Γ → Γ₀ ⁏ Δ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ ⊩ A

  infix 3 _⁏_⊩_⇒⋆_
  _⁏_⊩_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Cx Ty → Set
  Γ₀ ⁏ Δ ⊩ Γ ⇒⋆ Π = Γ₀ ⁏ Δ ⊩⋆ Γ → Γ₀ ⁏ Δ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ ⊩⋆ Π


-- Entailment, or forcing in all worlds of all models, for sequents.

infix 3 _⁏_⊨_
_⁏_⊨_ : Cx Ty → Cx Ty → Ty → Set₁
Γ ⁏ Δ ⊨ A = ∀ {{_ : Model}} {Γ₀ : Cx Ty} → Γ₀ ⁏ Δ ⊩ Γ ⇒ A

infix 3 _⁏_⊨⋆_
_⁏_⊨⋆_ : Cx Ty → Cx Ty → Cx Ty → Set₁
Γ ⁏ Δ ⊨⋆ Π = ∀ {{_ : Model}} {Γ₀ : Cx Ty} → Γ₀ ⁏ Δ ⊩ Γ ⇒⋆ Π


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ Γ₀ Δ₀} → A ∈ Γ → Γ₀ ⁏ Δ₀ ⊩⋆ Γ → Γ₀ ⁏ Δ₀ ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  mlookup : ∀ {A Δ Γ₀ Δ₀} → A ∈ Δ → Γ₀ ⁏ Δ₀ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊩ A
  mlookup top     (γ , s) = let t , a = s refl⊆ in a
  mlookup (pop i) (γ , s) = mlookup i γ

  -- TODO: More equipment.
