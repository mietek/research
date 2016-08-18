-- Tarski-style semantics with a Gentzen-style syntax representation and a separate modal context.

module BasicIS4.Semantics.TarskiDyadicGentzen where

open import Common.ContextPair public
open import BasicIS4.Syntax.Common public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⁏_⊩ᵅ_
  field
    -- Forcing for atomic propositions; monotonic.
    _⁏_⊩ᵅ_  : Cx Ty → Cx Ty → Atom → Set
    mono⊩ᵅ  : ∀ {P Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩ᵅ P → Γ′ ⁏ Δ ⊩ᵅ P
    mmono⊩ᵅ : ∀ {P Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊩ᵅ P → Γ ⁏ Δ′ ⊩ᵅ P

    -- Gentzen-style syntax representation; monotonic.
    [_⁏_⊢_]  : Cx Ty → Cx Ty → Ty → Set
    mono[⊢]  : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → [ Γ ⁏ Δ ⊢ A ] → [ Γ′ ⁏ Δ ⊢ A ]
    mmono[⊢] : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → [ Γ ⁏ Δ ⊢ A ] → [ Γ ⁏ Δ′ ⊢ A ]
    [var]     : ∀ {A Γ Δ}    → A ∈ Γ → [ Γ ⁏ Δ ⊢ A ]
    [lam]     : ∀ {A B Γ Δ}  → [ Γ , A ⁏ Δ ⊢ B ] → [ Γ ⁏ Δ ⊢ A ▻ B ]
    [app]     : ∀ {A B Γ Δ}  → [ Γ ⁏ Δ ⊢ A ▻ B ] → [ Γ ⁏ Δ ⊢ A ] → [ Γ ⁏ Δ ⊢ B ]
    [mvar]    : ∀ {A Γ Δ}    → A ∈ Δ → [ Γ ⁏ Δ ⊢ A ]
    [box]     : ∀ {A Γ Δ}    → [ ⌀ ⁏ Δ ⊢ A ] → [ Γ ⁏ Δ ⊢ □ A ]
    [unbox]   : ∀ {A C Γ Δ}  → [ Γ ⁏ Δ ⊢ □ A ] → [ Γ ⁏ Δ , A ⊢ C ] → [ Γ ⁏ Δ ⊢ C ]
    [pair]    : ∀ {A B Γ Δ}  → [ Γ ⁏ Δ ⊢ A ] → [ Γ ⁏ Δ ⊢ B ] → [ Γ ⁏ Δ ⊢ A ∧ B ]
    [fst]     : ∀ {A B Γ Δ}  → [ Γ ⁏ Δ ⊢ A ∧ B ] → [ Γ ⁏ Δ ⊢ A ]
    [snd]     : ∀ {A B Γ Δ}  → [ Γ ⁏ Δ ⊢ A ∧ B ] → [ Γ ⁏ Δ ⊢ B ]
    [tt]      : ∀ {Γ Δ}      → [ Γ ⁏ Δ ⊢ ⊤ ]

  [_⁏_⊢_]⋆ : Cx Ty → Cx Ty → Cx Ty → Set
  [ Γ ⁏ Δ ⊢ ⌀ ]⋆     = 𝟙
  [ Γ ⁏ Δ ⊢ Π , A ]⋆ = [ Γ ⁏ Δ ⊢ Π ]⋆ × [ Γ ⁏ Δ ⊢ A ]

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 _⁏_⊩_
  _⁏_⊩_ : Cx Ty → Cx Ty → Ty → Set
  Γ ⁏ Δ ⊩ α P   = [ Γ ⁏ Δ ⊢ α P ] × Γ ⁏ Δ ⊩ᵅ P
  Γ ⁏ Δ ⊩ A ▻ B = ∀ {Γ′ Δ′} → Γ ⊆ Γ′ → Δ ⊆ Δ′ → [ Γ′ ⁏ Δ′ ⊢ A ▻ B ] × (Γ′ ⁏ Δ′ ⊩ A → Γ′ ⁏ Δ′ ⊩ B)
  Γ ⁏ Δ ⊩ □ A   = ∀ {Γ′ Δ′} → Γ ⊆ Γ′ → Δ ⊆ Δ′ → [ Γ′ ⁏ Δ′ ⊢ □ A ] × Γ′ ⁏ Δ′ ⊩ A
  Γ ⁏ Δ ⊩ A ∧ B = Γ ⁏ Δ ⊩ A × Γ ⁏ Δ ⊩ B
  Γ ⁏ Δ ⊩ ⊤    = 𝟙

  infix 3 _⁏_⊩⋆_
  _⁏_⊩⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
  Γ ⁏ Δ ⊩⋆ ⌀     = 𝟙
  Γ ⁏ Δ ⊩⋆ Π , A = Γ ⁏ Δ ⊩⋆ Π × Γ ⁏ Δ ⊩ A


-- Monotonicity with respect to context inclusion.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩ A → Γ′ ⁏ Δ ⊩ A
  mono⊩ {α P}   η (t , s) = mono[⊢] η t , mono⊩ᵅ η s
  mono⊩ {A ▻ B} η s       = λ η′ θ → s (trans⊆ η η′) θ
  mono⊩ {□ A}   η s       = λ η′ θ → s (trans⊆ η η′) θ
  mono⊩ {A ∧ B} η (a , b) = mono⊩ {A} η a , mono⊩ {B} η b
  mono⊩ {⊤}    η ∙       = ∙

  mono⊩⋆ : ∀ {Π Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩⋆ Π → Γ′ ⁏ Δ ⊩⋆ Π
  mono⊩⋆ {⌀}     η ∙        = ∙
  mono⊩⋆ {Π , A} η (ts , t) = mono⊩⋆ {Π} η ts , mono⊩ {A} η t


-- Monotonicity with respect to modal context inclusion.

module _ {{_ : Model}} where
  mmono⊩ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ′ ⊩ A
  mmono⊩ {α P}   θ (t , s) = mmono[⊢] θ t , mmono⊩ᵅ θ s
  mmono⊩ {A ▻ B} θ s       = λ η θ′ → s η (trans⊆ θ θ′)
  mmono⊩ {□ A}   θ s       = λ η θ′ → s η (trans⊆ θ θ′)
  mmono⊩ {A ∧ B} θ (a , b) = mmono⊩ {A} θ a , mmono⊩ {B} θ b
  mmono⊩ {⊤}    θ ∙       = ∙

  mmono⊩⋆ : ∀ {Π Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊩⋆ Π → Γ ⁏ Δ′ ⊩⋆ Π
  mmono⊩⋆ {⌀}     η ∙        = ∙
  mmono⊩⋆ {Π , A} η (ts , t) = mmono⊩⋆ {Π} η ts , mmono⊩ {A} η t


-- Combined monotonicity.

module _ {{_ : Model}} where
  mono²⊩ : ∀ {A Γ Γ′ Δ Δ′} → Γ ⊆ Γ′ × Δ ⊆ Δ′ → Γ ⁏ Δ ⊩ A → Γ′ ⁏ Δ′ ⊩ A
  mono²⊩ {A} (η , θ) = mono⊩ {A} η ∘ mmono⊩ {A} θ

  mono²⊩⋆ : ∀ {Π Γ Γ′ Δ Δ′} → Γ ⊆ Γ′ × Δ ⊆ Δ′ → Γ ⁏ Δ ⊩⋆ Π → Γ′ ⁏ Δ′ ⊩⋆ Π
  mono²⊩⋆ {Π} (η , θ) = mono⊩⋆ {Π} η ∘ mmono⊩⋆ {Π} θ


-- Completeness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  reify[] : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → [ Γ ⁏ Δ ⊢ A ]
  reify[] {α P}   (t , s) = t
  reify[] {A ▻ B} s       = let t , f = s refl⊆ refl⊆ in t
  reify[] {□ A}   s       = let t , f = s refl⊆ refl⊆ in t
  reify[] {A ∧ B} (a , b) = [pair] (reify[] {A} a) (reify[] {B} b)
  reify[] {⊤}    ∙       = [tt]

  reify[]⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊩⋆ Π → [ Γ ⁏ Δ ⊢ Π ]⋆
  reify[]⋆ {⌀}     ∙        = ∙
  reify[]⋆ {Π , A} (ts , t) = reify[]⋆ ts , reify[] t


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B
  s ⟪$⟫ a = let t , f = s refl⊆ refl⊆ in f a

  ⟪⇓⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ A
  ⟪⇓⟫ s = let p , a = s refl⊆ refl⊆ in a


-- Forcing in a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⁏_⊩_⁏_⇒_
  _⁏_⊩_⁏_⇒_ : Cx Ty → Cx Ty → Cx Ty → Cx Ty → Ty → Set
  Γ₀ ⁏ Δ₀ ⊩ Γ ⁏ Δ ⇒ A = Γ₀ ⁏ Δ₀ ⊩⋆ Γ → Γ₀ ⁏ Δ₀ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊩ A

  infix 3 _⁏_⊩_⁏_⇒⋆_
  _⁏_⊩_⁏_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Cx Ty → Cx Ty → Set
  Γ₀ ⁏ Δ₀ ⊩ Γ ⁏ Δ ⇒⋆ Π = Γ₀ ⁏ Δ₀ ⊩⋆ Γ → Γ₀ ⁏ Δ₀ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊩⋆ Π


-- Forcing in all models, for sequents.

_⁏_⊨_ : Cx Ty → Cx Ty → Ty → Set₁
Γ ⁏ Δ ⊨ A = ∀ {{_ : Model}} {Γ₀ Δ₀ : Cx Ty} → Γ₀ ⁏ Δ₀ ⊩ Γ ⁏ Δ ⇒ A

_⁏_⊨⋆_ : Cx Ty → Cx Ty → Cx Ty → Set₁
Γ ⁏ Δ ⊨⋆ Π = ∀ {{_ : Model}} {Γ₀ Δ₀ : Cx Ty} → Γ₀ ⁏ Δ₀ ⊩ Γ ⁏ Δ ⇒⋆ Π


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ Γ₀ Δ₀} → A ∈ Γ → Γ₀ ⁏ Δ₀ ⊩⋆ Γ → Γ₀ ⁏ Δ₀ ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  mlookup : ∀ {A Δ Γ₀ Δ₀} → A ∈ Δ → Γ₀ ⁏ Δ₀ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊩ A
  mlookup top     (γ , s) = let t , a = s refl⊆ refl⊆ in a
  mlookup (pop i) (γ , s) = mlookup i γ

  -- TODO: More equipment.
