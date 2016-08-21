-- Tarski-style semantics with a Gentzen-style syntax representation.

module BasicIPC.Semantics.TarskiGentzen where

open import BasicIPC.Syntax.Common public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_   : Cx Ty → Atom → Set
    mono⊩ᵅ : ∀ {P Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩ᵅ P → Γ′ ⊩ᵅ P

    -- Gentzen-style syntax representation; monotonic.
    [_⊢_]   : Cx Ty → Ty → Set
    mono[⊢] : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → [ Γ ⊢ A ] → [ Γ′ ⊢ A ]
    [var]    : ∀ {A Γ}    → A ∈ Γ → [ Γ ⊢ A ]
    [lam]    : ∀ {A B Γ}  → [ Γ , A ⊢ B ] → [ Γ ⊢ A ▻ B ]
    [app]    : ∀ {A B Γ}  → [ Γ ⊢ A ▻ B ] → [ Γ ⊢ A ] → [ Γ ⊢ B ]
    [pair]   : ∀ {A B Γ}  → [ Γ ⊢ A ] → [ Γ ⊢ B ] → [ Γ ⊢ A ∧ B ]
    [fst]    : ∀ {A B Γ}  → [ Γ ⊢ A ∧ B ] → [ Γ ⊢ A ]
    [snd]    : ∀ {A B Γ}  → [ Γ ⊢ A ∧ B ] → [ Γ ⊢ B ]
    [tt]     : ∀ {Γ}      → [ Γ ⊢ ⊤ ]

  [_⊢_]⋆ : Cx Ty → Cx Ty → Set
  [ Γ ⊢ ⌀ ]⋆     = 𝟙
  [ Γ ⊢ Π , A ]⋆ = [ Γ ⊢ Π ]⋆ × [ Γ ⊢ A ]

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : Cx Ty → Ty → Set
  Γ ⊩ α P   = [ Γ ⊢ α P ] × Γ ⊩ᵅ P
  Γ ⊩ A ▻ B = ∀ {Γ′} → Γ ⊆ Γ′ → [ Γ′ ⊢ A ▻ B ] × (Γ′ ⊩ A → Γ′ ⊩ B)
  Γ ⊩ A ∧ B = Γ ⊩ A × Γ ⊩ B
  Γ ⊩ ⊤    = 𝟙

  infix 3 _⊩⋆_
  _⊩⋆_ : Cx Ty → Cx Ty → Set
  Γ ⊩⋆ ⌀     = 𝟙
  Γ ⊩⋆ Π , A = Γ ⊩⋆ Π × Γ ⊩ A


-- Monotonicity with respect to context inclusion.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩ A → Γ′ ⊩ A
  mono⊩ {α P}   η (t , s) = mono[⊢] η t , mono⊩ᵅ η s
  mono⊩ {A ▻ B} η s       = λ η′ → s (trans⊆ η η′)
  mono⊩ {A ∧ B} η (a , b) = mono⊩ {A} η a , mono⊩ {B} η b
  mono⊩ {⊤}    η ∙       = ∙

  mono⊩⋆ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩⋆ Π → Γ′ ⊩⋆ Π
  mono⊩⋆ {⌀}     η ∙        = ∙
  mono⊩⋆ {Π , A} η (ts , t) = mono⊩⋆ {Π} η ts , mono⊩ {A} η t


-- Completeness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  reifyʳ : ∀ {A Γ} → Γ ⊩ A → [ Γ ⊢ A ]
  reifyʳ {α P}   (t , s) = t
  reifyʳ {A ▻ B} s       = let t , f = s refl⊆ in t
  reifyʳ {A ∧ B} (a , b) = [pair] (reifyʳ {A} a) (reifyʳ {B} b)
  reifyʳ {⊤}    ∙       = [tt]

  reifyʳ⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → [ Γ ⊢ Π ]⋆
  reifyʳ⋆ {⌀}     ∙        = ∙
  reifyʳ⋆ {Π , A} (ts , t) = reifyʳ⋆ ts , reifyʳ t


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B Γ} → Γ ⊩ A ▻ B → Γ ⊩ A → Γ ⊩ B
  s ⟪$⟫ a = let t , f = s refl⊆ in f a

  ⟪ap⟫ : ∀ {A B C Γ} → Γ ⊩ A ▻ B ▻ C → Γ ⊩ A ▻ B → Γ ⊩ A → Γ ⊩ C
  ⟪ap⟫ s₁ s₂ a = let t , f = s₁ refl⊆
                     u , g = s₂ refl⊆
                     _ , h = (f a) refl⊆
                 in  h (g a)


-- Forcing in a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⊩_⇒_
  _⊩_⇒_ : Cx Ty → Cx Ty → Ty → Set
  Γ₀ ⊩ Γ ⇒ A = Γ₀ ⊩⋆ Γ → Γ₀ ⊩ A

  infix 3 _⊩_⇒⋆_
  _⊩_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
  Γ₀ ⊩ Γ ⇒⋆ Π = Γ₀ ⊩⋆ Γ → Γ₀ ⊩⋆ Π


-- Forcing in all models, for sequents.

_⊨_ : Cx Ty → Ty → Set₁
Γ ⊨ A = ∀ {{_ : Model}} {Γ₀ : Cx Ty} → Γ₀ ⊩ Γ ⇒ A

_⊨⋆_ : Cx Ty → Cx Ty → Set₁
Γ ⊨⋆ Π = ∀ {{_ : Model}} {Γ₀ : Cx Ty} → Γ₀ ⊩ Γ ⇒⋆ Π


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ Γ₀} → A ∈ Γ → Γ₀ ⊩ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  -- TODO: ⟦λ⟧

  _⟦$⟧_ : ∀ {A B Γ Γ₀} → Γ₀ ⊩ Γ ⇒ A ▻ B → Γ₀ ⊩ Γ ⇒ A → Γ₀ ⊩ Γ ⇒ B
  (f ⟦$⟧ g) γ = f γ ⟪$⟫ g γ

  ⟦ap⟧ : ∀ {A B C Γ Γ₀} → Γ₀ ⊩ Γ ⇒ A ▻ B ▻ C → Γ₀ ⊩ Γ ⇒ A ▻ B → Γ₀ ⊩ Γ ⇒ A → Γ₀ ⊩ Γ ⇒ C
  ⟦ap⟧ f g a γ = ⟪ap⟫ (f γ) (g γ) (a γ)

  _⟦,⟧_ : ∀ {A B Γ Γ₀} → Γ₀ ⊩ Γ ⇒ A → Γ₀ ⊩ Γ ⇒ B → Γ₀ ⊩ Γ ⇒ A ∧ B
  (a ⟦,⟧ b) γ = a γ , b γ

  ⟦π₁⟧ : ∀ {A B Γ Γ₀} → Γ₀ ⊩ Γ ⇒ A ∧ B → Γ₀ ⊩ Γ ⇒ A
  ⟦π₁⟧ s γ = π₁ (s γ)

  ⟦π₂⟧ : ∀ {A B Γ Γ₀} → Γ₀ ⊩ Γ ⇒ A ∧ B → Γ₀ ⊩ Γ ⇒ B
  ⟦π₂⟧ s γ = π₂ (s γ)
