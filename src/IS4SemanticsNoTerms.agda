module IS4SemanticsNoTerms where

open import IS4SyntaxNoTerms public


-- Introspective Kripke models.

record Model : Set₁ where
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
  infix 3 _[⊩₁]_
  _[⊩₁]_ : ∀ {{_ : Model}} → World → BoxTy → Set
  w [⊩₁] □ A = peek w [⊢] □ A

  infix 3 _[⊩₂]_
  _[⊩₂]_ : ∀ {{_ : Model}} → World → BoxTy → Set
  w [⊩₂] □ A = w ⊩ A

  infix 3 _⊪_
  _⊪_ : ∀ {{_ : Model}} → World → Ty → Set
  w ⊪ •      = G w
  w ⊪ A ⇒ B = ∀ {w′} → w′ ⊒ w → w′ ⊩ A → w′ ⊩ B
  w ⊪ □ A    = ∀ {w′} → w′ Я w → w′ [⊩₁] □ A ∧ w′ [⊩₂] □ A

  infix 3 _⊩_
  _⊩_ : ∀ {{_ : Model}} → World → Ty → Set
  w ⊩ A = ∀ {C w′} → w′ ⊒ w →
             (∀ {w″} → w″ ⊒ w′ → w″ ⊪ A → peek w″ ⊢ⁿᶠ C) →
             peek w′ ⊢ⁿᶠ C

mutual
  mono⊪ : ∀ {{_ : Model}} {A w w′} → w′ ⊒ w → w ⊪ A → w′ ⊪ A
  mono⊪ {•}      θ a = monoG θ a
  mono⊪ {A ⇒ B} θ f = λ θ′ a → f (trans⊒ θ′ θ) a
  mono⊪ {□ A}    θ q = λ ζ → q (transЯ ζ (⊒→Я θ))

  mono⊩ : ∀ {{_ : Model}} {A w w′} → w′ ⊒ w → w ⊩ A → w′ ⊩ A
  mono⊩ θ f = λ θ′ κ → f (trans⊒ θ′ θ) κ


-- Lists of values.

infix 3 _⊩⋆_
_⊩⋆_ : ∀ {{_ : Model}} → World → Ty⋆ → Set
w ⊩⋆ Ξ = All (w ⊩_) Ξ

mono⊩⋆ : ∀ {{_ : Model}} {w w′ Ξ} → w′ ⊒ w → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
mono⊩⋆ θ ξ = mapAll (λ {A} → mono⊩ {A} θ) ξ

lookup⊩ : ∀ {{_ : Model}} {w Ξ A} → w ⊩⋆ Ξ → Ξ ∋ A → w ⊩ A
lookup⊩ ξ 𝒾 = lookupAll ξ 𝒾


-- TODO: Needs a name.

infix 3 _[⊩₁]⋆_
_[⊩₁]⋆_ : ∀ {{_ : Model}} → World → BoxTy⋆ → Set
w [⊩₁]⋆ Ξ = All (w [⊩₁]_) Ξ

mlookup[⊩₁] : ∀ {{_ : Model}} {w Ξ A} → w [⊩₁]⋆ Ξ → Ξ ∋ □ A → w [⊩₁] □ A
mlookup[⊩₁] ξ 𝒾 = lookupAll ξ 𝒾


-- TODO: Needs a name.

infix 3 _[⊩₂]⋆_
_[⊩₂]⋆_ : ∀ {{_ : Model}} → World → BoxTy⋆ → Set
w [⊩₂]⋆ Ξ = All (w [⊩₂]_) Ξ

mlookup[⊩₂] : ∀ {{_ : Model}} {w Ξ A} → w [⊩₂]⋆ Ξ → Ξ ∋ □ A → w [⊩₂] □ A
mlookup[⊩₂] ξ 𝒾 = lookupAll ξ 𝒾


-- Continuations.

return : ∀ {{_ : Model}} {A w} → w ⊪ A → w ⊩ A
return {A} a = λ θ κ → κ refl⊒ (mono⊪ {A} θ a)

bind : ∀ {{_ : Model}} {A B w} → w ⊩ A →
         (∀ {w′} → w′ ⊒ w → w′ ⊪ A → w′ ⊩ B) →
         w ⊩ B
bind f κ = λ θ κ′ → f θ
             λ θ′ a → κ (trans⊒ θ′ θ) a refl⊒
               λ θ″ b → κ′ (trans⊒ θ″ θ′) b
