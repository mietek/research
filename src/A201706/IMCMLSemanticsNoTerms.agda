{-# OPTIONS --rewriting #-}

module A201706.IMCMLSemanticsNoTerms where

open import A201706.IMCMLSyntaxNoTerms public


-- Introspective Kripke models.

record Model : Set₁ where
  infix 3 _⊒_
  infix 3 _Я_
  field
    World  : Set
    _⊒_    : World → World → Set
    refl⊒  : ∀ {w} → w ⊒ w
    trans⊒ : ∀ {w w′ w″} → w″ ⊒ w′ → w′ ⊒ w → w″ ⊒ w
    _Я_    : World → World → Set
    reflЯ  : ∀ {w} → w Я w
    transЯ : ∀ {w w′ w″} → w″ Я w′ → w′ Я w → w″ Я w
    G      : World → Set
    monoG  : ∀ {w w′} → w′ ⊒ w → G w → G w′
    ⊒→Я   : ∀ {w w′} → w′ ⊒ w → w′ Я w
    peek   : World → Cx
open Model {{…}} public


-- Values.

mutual
  infix 3 _⊪_
  _⊪_ : ∀ {{_ : Model}} → World → Ty → Set
  w ⊪ •       = G w
  w ⊪ A ⇒ B  = ∀ {w′ : World} → w′ ⊒ w → w′ ⊩ A → w′ ⊩ B
  w ⊪ [ Φ ] A = ∀ {w′ : World} → w′ Я w → w′ ⟪⊢⟫ [ Φ ] A ∧ w′ ⟪⊩⟫ [ Φ ] A

  infix 3 _⟪⊢⟫_
  _⟪⊢⟫_ : ∀ {{_ : Model}} → World → BoxTy → Set
  w ⟪⊢⟫ [ Φ ] A = π₁ (peek w) ⟨⊢⟩ [ Φ ] A

  infix 3 _⟪⊩⟫_
  _⟪⊩⟫_ : ∀ {{_ : Model}} → World → BoxTy → Set
  w ⟪⊩⟫ [ Φ ] A = ∀ {w′ : World} → w′ Я w → w′ ⟪⊢⟫⋆ ⌈ Φ ⌉ → w′ ⊩ A

  infix 3 _⊩_
  _⊩_ : ∀ {{_ : Model}} → World → Ty → Set
  w ⊩ A = ∀ {C} {w′ : World} → w′ ⊒ w →
             (∀ {w″ : World} → w″ ⊒ w′ → w″ ⊪ A → peek w″ ⊢ⁿᶠ C) →
             peek w′ ⊢ⁿᶠ C

  infix 3 _⟪⊢⟫⋆_
  _⟪⊢⟫⋆_ : ∀ {{_ : Model}} → World → BoxTy⋆ → Set
  w ⟪⊢⟫⋆ Ξ = All (w ⟪⊢⟫_) Ξ

  infix 3 _⊩⋆_
  _⊩⋆_ : ∀ {{_ : Model}} → World → Ty⋆ → Set
  w ⊩⋆ ∅       = ⊤
  w ⊩⋆ (Ξ , A) = w ⊩⋆ Ξ ∧ w ⊩ A
  -- NOTE: Equivalent, but does not pass termination check.
  -- w ⊩⋆ Ξ = All (w ⊩_) Ξ

mutual
  mono⊪ : ∀ {{_ : Model}} {A} {w w′ : World} → w′ ⊒ w → w ⊪ A → w′ ⊪ A
  mono⊪ {•}       θ a = monoG θ a
  mono⊪ {A ⇒ B}  θ f = λ θ′ a → f (trans⊒ θ′ θ) a
  mono⊪ {[ Φ ] A} θ q = λ ζ → q (transЯ ζ (⊒→Я θ))

  mono⊩ : ∀ {{_ : Model}} {A} {w w′ : World} → w′ ⊒ w → w ⊩ A → w′ ⊩ A
  mono⊩ θ f = λ θ′ κ → f (trans⊒ θ′ θ) κ


-- Lists of values.

mono⊩⋆ : ∀ {{_ : Model}} {Ξ} {w w′ : World} → w′ ⊒ w → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
mono⊩⋆ {∅}     θ ∅       = ∅
mono⊩⋆ {Ξ , A} θ (ξ , a) = mono⊩⋆ θ ξ , mono⊩ {A} θ a

lookup⊩ : ∀ {{_ : Model}} {w : World} {Ξ A} → w ⊩⋆ Ξ → Ξ ∋ A → w ⊩ A
lookup⊩ (ξ , a) zero    = a
lookup⊩ (ξ , b) (suc 𝒾) = lookup⊩ ξ 𝒾


-- TODO: Needs a name.

mlookup⟪⊢⟫ : ∀ {{_ : Model}} {w : World} {Ξ Φ A} → w ⟪⊢⟫⋆ Ξ → Ξ ∋ [ Φ ] A → w ⟪⊢⟫ [ Φ ] A
mlookup⟪⊢⟫ ξ 𝒾 = lookupAll ξ 𝒾


-- TODO: Needs a name.

infix 3 _⟪⊩⟫⋆_
_⟪⊩⟫⋆_ : ∀ {{_ : Model}} → World → BoxTy⋆ → Set
w ⟪⊩⟫⋆ Ξ = All (w ⟪⊩⟫_) Ξ

mlookup⟪⊩⟫ : ∀ {{_ : Model}} {w : World} {Ξ Φ A} → w ⟪⊩⟫⋆ Ξ → Ξ ∋ [ Φ ] A → w ⟪⊩⟫ [ Φ ] A
mlookup⟪⊩⟫ ξ 𝒾 = lookupAll ξ 𝒾

mono⟪⊩⟫ : ∀ {{_ : Model}} {A} {w w′ : World} {Φ} → w′ ⊒ w → w ⟪⊩⟫ [ Φ ] A → w′ ⟪⊩⟫ [ Φ ] A
mono⟪⊩⟫ {A} θ q = λ ζ φ → q (transЯ ζ (⊒→Я θ)) φ

mono⟪⊩⟫⋆ : ∀ {{_ : Model}} {Ξ} {w w′ : World} → w′ ⊒ w → w ⟪⊩⟫⋆ Ξ → w′ ⟪⊩⟫⋆ Ξ
mono⟪⊩⟫⋆ θ ξ = mapAll (λ { {[ Φ ] A} → mono⟪⊩⟫ {A} θ }) ξ


-- Continuations.

return : ∀ {{_ : Model}} {A} {w : World} → w ⊪ A → w ⊩ A
return {A} a = λ θ κ → κ refl⊒ (mono⊪ {A} θ a)

bind : ∀ {{_ : Model}} {A B} {w : World} → w ⊩ A →
         (∀ {w′ : World} → w′ ⊒ w → w′ ⊪ A → w′ ⊩ B) →
         w ⊩ B
bind f κ = λ θ κ′ → f θ
             λ θ′ a → κ (trans⊒ θ′ θ) a refl⊒
               λ θ″ b → κ′ (trans⊒ θ″ θ′) b
