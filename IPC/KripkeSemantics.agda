module IPC.KripkeSemantics where

open import IPC public




-- Continuation-passing style (CPS) forcing, following Ilik.

module IlikSemantics where


  -- Intuitionistic Kripke-CPS models, with exploding worlds.

  record Model : Set₁ where
    infix 3 _⊪ᵅ_
    field
      World : Set

      -- Intuitionistic accessibility; preorder.
      _≤_    : World → World → Set
      refl≤  : ∀ {w} → w ≤ w
      trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

      -- Strong forcing for atomic propositions; monotonic.
      _⊪ᵅ_   : World → Atom → Set
      mono⊪ᵅ : ∀ {P w w′} → w ≤ w′ → w ⊪ᵅ P → w′ ⊪ᵅ P

      -- Exploding.
      _‼_ : World → Ty → Set

  open Model {{…}} public


  -- Strong forcing and forcing, both in a particular model.

  mutual
    infix 3 _⊪_
    _⊪_ : ∀ {{_ : Model}} → World → Ty → Set
    w ⊪ α P   = w ⊪ᵅ P
    w ⊪ A ▻ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
    w ⊪ A ∧ B = w ⊩ A × w ⊩ B
    w ⊪ ⊤    = 𝟙
    w ⊪ ⊥    = 𝟘
    w ⊪ A ∨ B = w ⊩ A ⊎ w ⊩ B

    infix 3 _⊩_
    _⊩_ : ∀ {{_ : Model}} → World → Ty → Set
    w ⊩ A = ∀ {C w′} → w ≤ w′ → (∀ {w″} → w′ ≤ w″ → w″ ⊪ A → w″ ‼ C) → w′ ‼ C

  infix 3 _⊩⋆_
  _⊩⋆_ : ∀ {{_ : Model}} → World → Cx Ty → Set
  w ⊩⋆ ∅     = 𝟙
  w ⊩⋆ Ξ , A = w ⊩⋆ Ξ × w ⊩ A


  -- Monotonicity with respect to intuitionistic accessibility.

  mutual
    mono⊪ : ∀ {{_ : Model}} {A w w′} → w ≤ w′ → w ⊪ A → w′ ⊪ A
    mono⊪ {α P}   ξ s       = mono⊪ᵅ ξ s
    mono⊪ {A ▻ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
    mono⊪ {A ∧ B} ξ (a , b) = mono⊩ {A} ξ a , mono⊩ {B} ξ b
    mono⊪ {⊤}    ξ ∙       = ∙
    mono⊪ {⊥}    ξ ()
    mono⊪ {A ∨ B} ξ (ι₁ a)  = ι₁ (mono⊩ {A} ξ a)
    mono⊪ {A ∨ B} ξ (ι₂ b)  = ι₂ (mono⊩ {B} ξ b)

    mono⊩ : ∀ {{_ : Model}} {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
    mono⊩ ξ a = λ ξ′ k′ → a (trans≤ ξ ξ′) k′

  mono⊩⋆ : ∀ {{_ : Model}} {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono⊩⋆ {∅}     ξ ∙       = ∙
  mono⊩⋆ {Γ , A} ξ (γ , a) = mono⊩⋆ {Γ} ξ γ , mono⊩ {A} ξ a


  -- The CPS monad.

  return : ∀ {{_ : Model}} {A w} → w ⊪ A → w ⊩ A
  return {A} a = λ ξ k → k refl≤ (mono⊪ {A} ξ a)

  bind : ∀ {{_ : Model}} {A B w} → w ⊩ A → (∀ {w′} → w ≤ w′ → w′ ⊪ A → w′ ⊩ B) → w ⊩ B
  bind a k = λ ξ k′ → a ξ (λ ξ′ a′ → k (trans≤ ξ ξ′) a′ refl≤ (λ ξ″ a″ → k′ (trans≤ ξ′ ξ″) a″))


  -- Forcing in all models.

  infix 3 _ᴹ⊩_
  _ᴹ⊩_ : Cx Ty → Ty → Set₁
  Γ ᴹ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩ A

  infix 3 _ᴹ⊩⋆_
  _ᴹ⊩⋆_ : Cx Ty → Cx Ty → Set₁
  Γ ᴹ⊩⋆ Ξ = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩⋆ Ξ


  -- Additional useful equipment.

  lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ
