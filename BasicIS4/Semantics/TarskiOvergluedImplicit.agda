-- Tarski-style semantics with contexts as concrete worlds, and glueing for α, ▻, and □.
-- Implicit syntax.

module BasicIS4.Semantics.TarskiOvergluedImplicit where

open import BasicIS4.Syntax.Common public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_   : Cx Ty → Atom → Set
    mono⊩ᵅ : ∀ {P Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩ᵅ P → Γ′ ⊩ᵅ P

open Model {{…}} public




module ImplicitSyntax
    (_[⊢]_   : Cx Ty → Ty → Set)
    (mono[⊢] : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ [⊢] A → Γ′ [⊢] A)
  where


  -- Forcing in a particular model.

  module _ {{_ : Model}} where
    infix 3 _⊩_
    _⊩_ : Cx Ty → Ty → Set
    Γ ⊩ α P   = Γ [⊢] (α P) × Γ ⊩ᵅ P
    Γ ⊩ A ▻ B = ∀ {Γ′} → Γ ⊆ Γ′ → Γ′ [⊢] (A ▻ B) × (Γ′ ⊩ A → Γ′ ⊩ B)
    Γ ⊩ □ A   = ∀ {Γ′} → Γ ⊆ Γ′ → Γ′ [⊢] (□ A) × Γ′ ⊩ A
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
    mono⊩ {□ A}   η s       = λ η′ → s (trans⊆ η η′)
    mono⊩ {A ∧ B} η (a , b) = mono⊩ {A} η a , mono⊩ {B} η b
    mono⊩ {⊤}    η ∙       = ∙

    mono⊩⋆ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩⋆ Π → Γ′ ⊩⋆ Π
    mono⊩⋆ {⌀}     η ∙        = ∙
    mono⊩⋆ {Π , A} η (ts , t) = mono⊩⋆ {Π} η ts , mono⊩ {A} η t


  -- Additional useful equipment.

  module _ {{_ : Model}} where
    _⟪$⟫_ : ∀ {A B Γ} → Γ ⊩ A ▻ B → Γ ⊩ A → Γ ⊩ B
    s ⟪$⟫ a = let t , f = s refl⊆
              in  f a

    ⟪S⟫ : ∀ {A B C Γ} → Γ ⊩ A ▻ B ▻ C → Γ ⊩ A ▻ B → Γ ⊩ A → Γ ⊩ C
    ⟪S⟫ s s′ a = let t , f = s refl⊆
                     u , g = s′ refl⊆
                     _ , h = (f a) refl⊆
                 in  h (g a)

    ⟪↓⟫ : ∀ {A Γ} → Γ ⊩ □ A → Γ ⊩ A
    ⟪↓⟫ s = let p , a = s refl⊆
            in  a


  -- Forcing in a particular world of a particular model, for sequents.

  module _ {{_ : Model}} where
    infix 3 _⊩_⇒_
    _⊩_⇒_ : Cx Ty → Cx Ty → Ty → Set
    w ⊩ Γ ⇒ A = w ⊩⋆ Γ → w ⊩ A

    infix 3 _⊩_⇒⋆_
    _⊩_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
    w ⊩ Γ ⇒⋆ Π = w ⊩⋆ Γ → w ⊩⋆ Π


  -- Entailment, or forcing in all worlds of all models, for sequents.

  infix 3 _⊨_
  _⊨_ : Cx Ty → Ty → Set₁
  Γ ⊨ A = ∀ {{_ : Model}} {w : Cx Ty} → w ⊩ Γ ⇒ A

  infix 3 _⊨⋆_
  _⊨⋆_ : Cx Ty → Cx Ty → Set₁
  Γ ⊨⋆ Π = ∀ {{_ : Model}} {w : Cx Ty} → w ⊩ Γ ⇒⋆ Π


  -- Additional useful equipment, for sequents.

  module _ {{_ : Model}} where
    lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩ Γ ⇒ A
    lookup top     (γ , a) = a
    lookup (pop i) (γ , b) = lookup i γ

    -- TODO: ⟦λ⟧

    _⟦$⟧_ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B
    (f ⟦$⟧ g) γ = f γ ⟪$⟫ g γ

    ⟦S⟧ : ∀ {A B C Γ w} → w ⊩ Γ ⇒ A ▻ B ▻ C → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ C
    ⟦S⟧ f g a γ = ⟪S⟫ (f γ) (g γ) (a γ)

    ⟦↓⟧ : ∀ {A Γ w} → w ⊩ Γ ⇒ □ A → w ⊩ Γ ⇒ A
    ⟦↓⟧ s γ = ⟪↓⟫ (s γ)

    _⟦,⟧_ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B → w ⊩ Γ ⇒ A ∧ B
    (a ⟦,⟧ b) γ = a γ , b γ

    ⟦π₁⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ∧ B → w ⊩ Γ ⇒ A
    ⟦π₁⟧ s γ = π₁ (s γ)

    ⟦π₂⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ∧ B → w ⊩ Γ ⇒ B
    ⟦π₂⟧ s γ = π₂ (s γ)
