-- Tarski-style denotational semantics with embedded Hilbert-style syntax, after Coquand-Dybjer.

module BasicIPC.Semantics.TarskiCoquandDybjerMk3 where

open import BasicIPC.Syntax.Common public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⊨ᵅ_
  field
    -- Satisfaction for atomic propositions; monotonic.
    _⊨ᵅ_   : Cx Ty → Atom → Set
    mono⊨ᵅ : ∀ {P Γ Γ′} → Γ ⊆ Γ′ → Γ ⊨ᵅ P → Γ′ ⊨ᵅ P

    -- Embedded Hilbert-style syntax; monotonic.
    [_⊢_]   : Cx Ty → Ty → Set
    [mono⊢] : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → [ Γ ⊢ A ] → [ Γ′ ⊢ A ]
    [app]    : ∀ {A B Γ}   → [ Γ ⊢ A ▻ B ] → [ Γ ⊢ A ] → [ Γ ⊢ B ]
    [ci]     : ∀ {A Γ}     → [ Γ ⊢ A ▻ A ]
    [ck]     : ∀ {A B Γ}   → [ Γ ⊢ A ▻ B ▻ A ]
    [cs]     : ∀ {A B C Γ} → [ Γ ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C ]
    [cpair]  : ∀ {A B Γ}   → [ Γ ⊢ A ▻ B ▻ A ∧ B ]
    [cfst]   : ∀ {A B Γ}   → [ Γ ⊢ A ∧ B ▻ A ]
    [csnd]   : ∀ {A B Γ}   → [ Γ ⊢ A ∧ B ▻ B ]
    [tt]     : ∀ {Γ}       → [ Γ ⊢ ⊤ ]

  [_⊢⋆_] : Cx Ty → Cx Ty → Set
  [ Γ ⊢⋆ ⌀ ]     = 𝟙
  [ Γ ⊢⋆ Π , A ] = [ Γ ⊢⋆ Π ] × [ Γ ⊢ A ]

open Model {{…}} public


-- Satisfaction in a particular model.

module _ {{_ : Model}} where
  infix 3 _⊨_
  _⊨_ : Cx Ty → Ty → Set
  Γ ⊨ α P   = [ Γ ⊢ α P ] × Γ ⊨ᵅ P
  Γ ⊨ A ▻ B = ∀ {Γ′} → Γ ⊆ Γ′ → [ Γ′ ⊢ A ▻ B ] × (Γ′ ⊨ A → Γ′ ⊨ B)
  Γ ⊨ A ∧ B = Γ ⊨ A × Γ ⊨ B
  Γ ⊨ ⊤    = 𝟙

  infix 3 _⊨⋆_
  _⊨⋆_ : Cx Ty → Cx Ty → Set
  Γ ⊨⋆ ⌀     = 𝟙
  Γ ⊨⋆ Π , A = Γ ⊨⋆ Π × Γ ⊨ A


-- Monotonicity with respect to context inclusion.

module _ {{_ : Model}} where
  mono⊨ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊨ A → Γ′ ⊨ A
  mono⊨ {α P}   η (t , s) = [mono⊢] η t , mono⊨ᵅ η s
  mono⊨ {A ▻ B} η s       = λ η′ → s (trans⊆ η η′)
  mono⊨ {A ∧ B} η (a , b) = mono⊨ {A} η a , mono⊨ {B} η b
  mono⊨ {⊤}    η ∙       = ∙

  mono⊨⋆ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊨⋆ Π → Γ′ ⊨⋆ Π
  mono⊨⋆ {⌀}     η ∙        = ∙
  mono⊨⋆ {Π , A} η (ts , t) = mono⊨⋆ {Π} η ts , mono⊨ {A} η t


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B Γ} → Γ ⊨ A ▻ B → Γ ⊨ A → Γ ⊨ B
  s ⟪$⟫ a = let t , f = s refl⊆ in f a

  ⟪ap⟫ : ∀ {A B C Γ} → Γ ⊨ A ▻ B ▻ C → Γ ⊨ A ▻ B → Γ ⊨ A → Γ ⊨ C
  ⟪ap⟫ s s′ a = let t , f = s refl⊆
                    u , g = s′ refl⊆
                    _ , h = (f a) refl⊆
                in  h (g a)


-- Satisfaction in a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⊨_⇒_
  _⊨_⇒_ : Cx Ty → Cx Ty → Ty → Set
  Γ₀ ⊨ Γ ⇒ A = Γ₀ ⊨⋆ Γ → Γ₀ ⊨ A

  infix 3 _⊨_⇒⋆_
  _⊨_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
  Γ₀ ⊨ Γ ⇒⋆ Π = Γ₀ ⊨⋆ Γ → Γ₀ ⊨⋆ Π


-- Satisfaction in all models, for sequents.

∀ᴹ⊨_⇒_ : Cx Ty → Ty → Set₁
∀ᴹ⊨ Γ ⇒ A = ∀ {{_ : Model}} {Γ₀ : Cx Ty} → Γ₀ ⊨ Γ ⇒ A

∀ᴹ⊨_⇒⋆_ : Cx Ty → Cx Ty → Set₁
∀ᴹ⊨ Γ ⇒⋆ Π = ∀ {{_ : Model}} {Γ₀ : Cx Ty} → Γ₀ ⊨ Γ ⇒⋆ Π


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ Γ₀} → A ∈ Γ → Γ₀ ⊨ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

-- ⟦λ⟧ : ∀ {A B Γ} → [ A ▻ B ] → ⊨ Γ , A ⇒ B → ⊨ Γ ⇒ A ▻ B
-- ⟦λ⟧ t f γ = t , λ a → f (γ , a)

  _⟦$⟧_ : ∀ {A B Γ Γ₀} → Γ₀ ⊨ Γ ⇒ A ▻ B → Γ₀ ⊨ Γ ⇒ A → Γ₀ ⊨ Γ ⇒ B
  (f ⟦$⟧ g) γ = f γ ⟪$⟫ g γ

  ⟦ap⟧ : ∀ {A B C Γ Γ₀} → Γ₀ ⊨ Γ ⇒ A ▻ B ▻ C → Γ₀ ⊨ Γ ⇒ A ▻ B → Γ₀ ⊨ Γ ⇒ A → Γ₀ ⊨ Γ ⇒ C
  ⟦ap⟧ f g a γ = ⟪ap⟫ (f γ) (g γ) (a γ)

  _⟦,⟧_ : ∀ {A B Γ Γ₀} → Γ₀ ⊨ Γ ⇒ A → Γ₀ ⊨ Γ ⇒ B → Γ₀ ⊨ Γ ⇒ A ∧ B
  (a ⟦,⟧ b) γ = a γ , b γ

  ⟦π₁⟧ : ∀ {A B Γ Γ₀} → Γ₀ ⊨ Γ ⇒ A ∧ B → Γ₀ ⊨ Γ ⇒ A
  ⟦π₁⟧ s γ = π₁ (s γ)

  ⟦π₂⟧ : ∀ {A B Γ Γ₀} → Γ₀ ⊨ Γ ⇒ A ∧ B → Γ₀ ⊨ Γ ⇒ B
  ⟦π₂⟧ s γ = π₂ (s γ)
