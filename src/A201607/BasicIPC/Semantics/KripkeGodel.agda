{-# OPTIONS --sized-types #-}

-- Basic intuitionistic propositional calculus, without ∨ or ⊥.
-- Kripke-style semantics with abstract worlds.
-- Gödel embedding.

module A201607.BasicIPC.Semantics.KripkeGodel where

open import A201607.BasicIPC.Syntax.Common public


-- Kripke models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    World : Set

    -- Intuitionistic accessibility; preorder.
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    -- Forcing for atomic propositions.
    _⊩ᵅ_ : World → Atom → Set

open Model {{…}} public


-- Forcing in a particular world of a particular model, based on the Gödel embedding of IPC in S4.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Ty → Set
  w ⊩ α P   = ∀ {w′ : World} → w ≤ w′ → w′ ⊩ᵅ P
  w ⊩ A ▻ B = ∀ {w′ : World} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ A ∧ B = ∀ {w′ : World} → w ≤ w′ → w′ ⊩ A × w′ ⊩ B
  w ⊩ ⊤    = ∀ {w′ : World} → w ≤ w′ → 𝟙

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ∅     = 𝟙
  w ⊩⋆ Ξ , A = w ⊩⋆ Ξ × w ⊩ A


-- Monotonicity with respect to intuitionistic accessibility.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A} {w w′ : World} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}   ξ s = λ ξ′ → s (trans≤ ξ ξ′)
  mono⊩ {A ▻ B} ξ s = λ ξ′ → s (trans≤ ξ ξ′)
  mono⊩ {A ∧ B} ξ s = λ ξ′ → s (trans≤ ξ ξ′)
  mono⊩ {⊤}    ξ s = λ ξ′ → ∙

  mono⊩⋆ : ∀ {Ξ} {w w′ : World} → w ≤ w′ → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ {∅}     ξ ∙       = ∙
  mono⊩⋆ {Ξ , A} ξ (γ , a) = mono⊩⋆ {Ξ} ξ γ , mono⊩ {A} ξ a


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B} {w : World} → w ⊩ A ▻ B → w ⊩ A → w ⊩ B
  s ⟪$⟫ a = s refl≤ a

  ⟪K⟫ : ∀ {A B} {w : World} → w ⊩ A → w ⊩ B ▻ A
  ⟪K⟫ {A} a ξ = K (mono⊩ {A} ξ a)

  ⟪S⟫ : ∀ {A B C} {w : World} → w ⊩ A ▻ B ▻ C → w ⊩ A ▻ B → w ⊩ A → w ⊩ C
  ⟪S⟫ {A} {B} {C} s₁ s₂ a = _⟪$⟫_ {B} {C} (_⟪$⟫_ {A} {B ▻ C} s₁ a) (_⟪$⟫_ {A} {B} s₂ a)

  ⟪S⟫′ : ∀ {A B C} {w : World} → w ⊩ A ▻ B ▻ C → w ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} s₁ ξ s₂ ξ′ a = let s₁′ = mono⊩ {A ▻ B ▻ C} (trans≤ ξ ξ′) s₁
                                      s₂′ = mono⊩ {A ▻ B} ξ′ s₂
                                  in  ⟪S⟫ {A} {B} {C} s₁′ s₂′ a

  _⟪,⟫_ : ∀ {A B} {w : World} → w ⊩ A → w ⊩ B → w ⊩ A ∧ B
  _⟪,⟫_ {A} {B} a b ξ = mono⊩ {A} ξ a , mono⊩ {B} ξ b

  _⟪,⟫′_ : ∀ {A B} {w : World} → w ⊩ A → w ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} {B} a ξ = _⟪,⟫_ {A} {B} (mono⊩ {A} ξ a)

  ⟪π₁⟫ : ∀ {A B} {w : World} → w ⊩ A ∧ B → w ⊩ A
  ⟪π₁⟫ s = π₁ (s refl≤)

  ⟪π₂⟫ : ∀ {A B} {w : World} → w ⊩ A ∧ B → w ⊩ B
  ⟪π₂⟫ s = π₂ (s refl≤)


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
  lookup : ∀ {A Γ} {w : World} → A ∈ Γ → w ⊩ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  ⟦λ⟧ : ∀ {A B Γ} {w : World} → (∀ {w′ : World} → w′ ⊩ Γ , A ⇒ B) → w ⊩ Γ ⇒ A ▻ B
  ⟦λ⟧ s γ = λ ξ a → s (mono⊩⋆ ξ γ , a)

  _⟦$⟧_ : ∀ {A B Γ} {w : World} → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B
  _⟦$⟧_ {A} {B} s₁ s₂ γ = _⟪$⟫_ {A} {B} (s₁ γ) (s₂ γ)

  ⟦K⟧ : ∀ {A B Γ} {w : World} → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B ▻ A
  ⟦K⟧ {A} {B} a γ = ⟪K⟫ {A} {B} (a γ)

  ⟦S⟧ : ∀ {A B C Γ} {w : World} → w ⊩ Γ ⇒ A ▻ B ▻ C → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ C
  ⟦S⟧ {A} {B} {C} s₁ s₂ a γ = ⟪S⟫ {A} {B} {C} (s₁ γ) (s₂ γ) (a γ)

  _⟦,⟧_ : ∀ {A B Γ} {w : World} → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B → w ⊩ Γ ⇒ A ∧ B
  _⟦,⟧_ {A} {B} a b γ = _⟪,⟫_ {A} {B} (a γ) (b γ)

  ⟦π₁⟧ : ∀ {A B Γ} {w : World} → w ⊩ Γ ⇒ A ∧ B → w ⊩ Γ ⇒ A
  ⟦π₁⟧ {A} {B} s γ = ⟪π₁⟫ {A} {B} (s γ)

  ⟦π₂⟧ : ∀ {A B Γ} {w : World} → w ⊩ Γ ⇒ A ∧ B → w ⊩ Γ ⇒ B
  ⟦π₂⟧ {A} {B} s γ = ⟪π₂⟫ {A} {B} (s γ)
