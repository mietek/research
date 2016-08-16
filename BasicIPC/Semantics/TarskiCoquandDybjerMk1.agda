-- Tarski-style denotational semantics with embedded Hilbert-style syntax, after Coquand-Dybjer.

module BasicIPC.Semantics.TarskiCoquandDybjerMk1 where

open import BasicIPC.Syntax.Common public


-- Tarski models.

record Model : Set₁ where
  infix 3 ⊨ᵅ_
  field
    -- Satisfaction for atomic propositions.
    ⊨ᵅ_ : Atom → Set

    -- Hilbert-style syntax.
    [_]     : Ty → Set
    [app]   : ∀ {A B}   → [ A ▻ B ] → [ A ] → [ B ]
    [ci]    : ∀ {A}     → [ A ▻ A ]
    [ck]    : ∀ {A B}   → [ A ▻ B ▻ A ]
    [cs]    : ∀ {A B C} → [ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C ]
    [cpair] : ∀ {A B}   → [ A ▻ B ▻ A ∧ B ]
    [cfst]  : ∀ {A B}   → [ A ∧ B ▻ A ]
    [csnd]  : ∀ {A B}   → [ A ∧ B ▻ B ]
    [tt]    : [ ⊤ ]

open Model {{…}} public


-- Satisfaction in a particular model, for closed syntax.

module _ {{_ : Model}} where
  infix 3 ⊨_
  ⊨_ : Ty → Set
  ⊨ α P   = [ α P ] × ⊨ᵅ P
  ⊨ A ▻ B = [ A ▻ B ] × (⊨ A → ⊨ B)
  ⊨ A ∧ B = ⊨ A × ⊨ B
  ⊨ ⊤    = 𝟙

  infix 3 ⊨⋆_
  ⊨⋆_ : Cx Ty → Set
  ⊨⋆ ⌀     = 𝟙
  ⊨⋆ Γ , A = ⊨⋆ Γ × ⊨ A


-- Satisfaction in all models, for closed syntax.

∀ᴹ⊨_ : Ty → Set₁
∀ᴹ⊨ A = ∀ {{_ : Model}} → ⊨ A


-- Additional useful equipment, for closed syntax.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B} → ⊨ A ▻ B → ⊨ A → ⊨ B
  (t , f) ⟪$⟫ a = f a

  ⟪ap⟫ : ∀ {A B C} → ⊨ A ▻ B ▻ C → ⊨ A ▻ B → ⊨ A → ⊨ C
  ⟪ap⟫ (t , f) (u , g) a = let (_ , h) = f a in  h (g a)


-- Satisfaction in a particular model, for open syntax.

module _ {{_ : Model}} where
  infix 3 ⊨_⇒_
  ⊨_⇒_ : Cx Ty → Ty → Set
  ⊨ Γ ⇒ A = ⊨⋆ Γ → ⊨ A

  infix 3 ⊨_⇒⋆_
  ⊨_⇒⋆_ : Cx Ty → Cx Ty → Set
  ⊨ Γ ⇒⋆ Π = ⊨⋆ Γ → ⊨⋆ Π


-- Satisfaction in all models, for open syntax.

∀ᴹ⊨_⇒_ : Cx Ty → Ty → Set₁
∀ᴹ⊨ Γ ⇒ A = ∀ {{_ : Model}} → ⊨ Γ ⇒ A

∀ᴹ⊨_⇒⋆_ : Cx Ty → Cx Ty → Set₁
∀ᴹ⊨ Γ ⇒⋆ Π = ∀ {{_ : Model}} → ⊨ Γ ⇒⋆ Π


-- Additional useful equipment, for open syntax.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ} → A ∈ Γ → ⊨ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  ⟦λ⟧ : ∀ {A B Γ} → [ A ▻ B ] → ⊨ Γ , A ⇒ B → ⊨ Γ ⇒ A ▻ B
  ⟦λ⟧ t f γ = t , λ a → f (γ , a)

  _⟦$⟧_ : ∀ {A B Γ} → ⊨ Γ ⇒ A ▻ B → ⊨ Γ ⇒ A → ⊨ Γ ⇒ B
  (f ⟦$⟧ g) γ = f γ ⟪$⟫ g γ

  ⟦ap⟧ : ∀ {A B C Γ} → ⊨ Γ ⇒ A ▻ B ▻ C → ⊨ Γ ⇒ A ▻ B → ⊨ Γ ⇒ A → ⊨ Γ ⇒ C
  ⟦ap⟧ f g a γ = ⟪ap⟫ (f γ) (g γ) (a γ)

  _⟦,⟧_ : ∀ {A B Γ} → ⊨ Γ ⇒ A → ⊨ Γ ⇒ B → ⊨ Γ ⇒ A ∧ B
  (a ⟦,⟧ b) γ = a γ , b γ

  ⟦π₁⟧ : ∀ {A B Γ} → ⊨ Γ ⇒ A ∧ B → ⊨ Γ ⇒ A
  ⟦π₁⟧ s γ = π₁ (s γ)

  ⟦π₂⟧ : ∀ {A B Γ} → ⊨ Γ ⇒ A ∧ B → ⊨ Γ ⇒ B
  ⟦π₂⟧ s γ = π₂ (s γ)
