-- Tarski-style semantics with a Hilbert-style closed syntax representation.

module BasicIS4.Semantics.TarskiClosedHilbert where

open import BasicIS4.Syntax.Common public


-- Tarski models.

record Model : Set₁ where
  infix 3 ⊩ᵅ_
  field
    -- Forcing for atomic propositions.
    ⊩ᵅ_ : Atom → Set

    -- Hilbert-style closed syntax representation.
    [_]     : Ty → Set
    [app]   : ∀ {A B}   → [ A ▻ B ] → [ A ] → [ B ]
    [ci]    : ∀ {A}     → [ A ▻ A ]
    [ck]    : ∀ {A B}   → [ A ▻ B ▻ A ]
    [cs]    : ∀ {A B C} → [ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C ]
    [box]   : ∀ {A}     → [ A ] → [ □ A ]
    [cdist] : ∀ {A B}   → [ □ (A ▻ B) ▻ □ A ▻ □ B ]
    [cup]   : ∀ {A}     → [ □ A ▻ □ □ A ]
    [cdown] : ∀ {A}     → [ □ A ▻ A ]
    [cpair] : ∀ {A B}   → [ A ▻ B ▻ A ∧ B ]
    [cfst]  : ∀ {A B}   → [ A ∧ B ▻ A ]
    [csnd]  : ∀ {A B}   → [ A ∧ B ▻ B ]
    [tt]    : [ ⊤ ]

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 ⊩_
  ⊩_ : Ty → Set
  ⊩ α P   = [ α P ] × ⊩ᵅ P
  ⊩ A ▻ B = [ A ▻ B ] × (⊩ A → ⊩ B)
  ⊩ □ A   = [ □ A ] × ⊩ A
  ⊩ A ∧ B = ⊩ A × ⊩ B
  ⊩ ⊤    = 𝟙

  infix 3 ⊩⋆_
  ⊩⋆_ : Cx Ty → Set
  ⊩⋆ ⌀     = 𝟙
  ⊩⋆ Π , A = ⊩⋆ Π × ⊩ A


-- Forcing in all models.

infix 3 ⊨_
⊨_ : Ty → Set₁
⊨ A = ∀ {{_ : Model}} → ⊩ A


-- Completeness with respect to the syntax representation in a particular model.

reify[] : ∀ {{_ : Model}} {A} → ⊩ A → [ A ]
reify[] {α P}   (t , s) = t
reify[] {A ▻ B} (t , f) = t
reify[] {□ A}   (t , a) = t
reify[] {A ∧ B} (a , b) = [app] ([app] [cpair] (reify[] {A} a)) (reify[] {B} b)
reify[] {⊤}    ∙       = [tt]


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B} → ⊩ A ▻ B → ⊩ A → ⊩ B
  (t , f) ⟪$⟫ a = f a

  ⟪const⟫ : ∀ {A B} → ⊩ A → ⊩ B ▻ A
  ⟪const⟫ a = [app] [ck] (reify[] a) , const a

  ⟪ap⟫ : ∀ {A B C} → ⊩ A ▻ B ▻ C → ⊩ A ▻ B → ⊩ A → ⊩ C
  ⟪ap⟫ (t , f) (u , g) a = let (_ , h) = f a in h (g a)

  ⟪ap⟫′ : ∀ {A B C} → ⊩ A ▻ B ▻ C → ⊩ (A ▻ B) ▻ A ▻ C
  ⟪ap⟫′ f = [app] [cs] (reify[] f) , λ g →
              [app] ([app] [cs] (reify[] f)) (reify[] g) , ⟪ap⟫ f g

  _⟪◎⟫_ : ∀ {A B} → ⊩ □ (A ▻ B) → ⊩ □ A → ⊩ □ B
  (t , f) ⟪◎⟫ (u , a) = [app] ([app] [cdist] t) u , f ⟪$⟫ a

  _⟪◎⟫′_ : ∀ {A B} → ⊩ □ (A ▻ B) → ⊩ □ A ▻ □ B
  _⟪◎⟫′_ s = [app] [cdist] (reify[] s) , _⟪◎⟫_ s

  ⟪⇑⟫ : ∀ {A} → ⊩ □ A → ⊩ □ □ A
  ⟪⇑⟫ (t , a) = [box] t , (t , a)

  ⟪⇓⟫ : ∀ {A} → ⊩ □ A → ⊩ A
  ⟪⇓⟫ (t , a) = a

  _⟪,⟫′_ : ∀ {A B} → ⊩ A → ⊩ B ▻ A ∧ B
  _⟪,⟫′_ a = [app] [cpair] (reify[] a) , _,_ a


-- Forcing in a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 ⊩_⇒_
  ⊩_⇒_ : Cx Ty → Ty → Set
  ⊩ Γ ⇒ A = ⊩⋆ Γ → ⊩ A

  infix 3 ⊩_⇒⋆_
  ⊩_⇒⋆_ : Cx Ty → Cx Ty → Set
  ⊩ Γ ⇒⋆ Π = ⊩⋆ Γ → ⊩⋆ Π


-- Forcing in all models, for sequents.

infix 3 _⊨_
_⊨_ : Cx Ty → Ty → Set₁
Γ ⊨ A = ∀ {{_ : Model}} → ⊩ Γ ⇒ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx Ty → Cx Ty → Set₁
Γ ⊨⋆ Π = ∀ {{_ : Model}} → ⊩ Γ ⇒⋆ Π


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ} → A ∈ Γ → ⊩ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  ⟦λ⟧ : ∀ {A B Γ} → [ A ▻ B ] → ⊩ Γ , A ⇒ B → ⊩ Γ ⇒ A ▻ B
  ⟦λ⟧ t f γ = t , λ a → f (γ , a)

  _⟦$⟧_ : ∀ {A B Γ} → ⊩ Γ ⇒ A ▻ B → ⊩ Γ ⇒ A → ⊩ Γ ⇒ B
  (f ⟦$⟧ g) γ = f γ ⟪$⟫ g γ

  ⟦ap⟧ : ∀ {A B C Γ} → ⊩ Γ ⇒ A ▻ B ▻ C → ⊩ Γ ⇒ A ▻ B → ⊩ Γ ⇒ A → ⊩ Γ ⇒ C
  ⟦ap⟧ f g a γ = ⟪ap⟫ (f γ) (g γ) (a γ)

  _⟦◎⟧_ : ∀ {A B Γ} → ⊩ Γ ⇒ □ (A ▻ B) → ⊩ Γ ⇒ □ A → ⊩ Γ ⇒ □ B
  (s₁ ⟦◎⟧ s₂) γ = (s₁ γ) ⟪◎⟫ (s₂ γ)

  ⟦⇑⟧ : ∀ {A Γ} → ⊩ Γ ⇒ □ A → ⊩ Γ ⇒ □ □ A
  ⟦⇑⟧ s γ = ⟪⇑⟫ (s γ)

  ⟦⇓⟧ : ∀ {A Γ} → ⊩ Γ ⇒ □ A → ⊩ Γ ⇒ A
  ⟦⇓⟧ s γ = ⟪⇓⟫ (s γ)

  _⟦,⟧_ : ∀ {A B Γ} → ⊩ Γ ⇒ A → ⊩ Γ ⇒ B → ⊩ Γ ⇒ A ∧ B
  (a ⟦,⟧ b) γ = a γ , b γ

  ⟦π₁⟧ : ∀ {A B Γ} → ⊩ Γ ⇒ A ∧ B → ⊩ Γ ⇒ A
  ⟦π₁⟧ s γ = π₁ (s γ)

  ⟦π₂⟧ : ∀ {A B Γ} → ⊩ Γ ⇒ A ∧ B → ⊩ Γ ⇒ B
  ⟦π₂⟧ s γ = π₂ (s γ)
