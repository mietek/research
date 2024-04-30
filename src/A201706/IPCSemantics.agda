module A201706.IPCSemantics where

open import A201706.IPC public


-- Intuitionistic Kripke models.

record Model : Set₁ where
  infix 3 _⊒_
  field
    World  : Set
    _⊒_    : World → World → Set
    refl⊒  : ∀ {w} → w ⊒ w
    trans⊒ : ∀ {w w′ w″} → w″ ⊒ w′ → w′ ⊒ w → w″ ⊒ w
    G      : World → Set
    monoG  : ∀ {w w′} → w′ ⊒ w → G w → G w′
open Model {{…}} public


-- Values.

infix 3 _⊩_
_⊩_ : ∀ {{_ : Model}} → World → Ty → Set
w ⊩ •      = G w
w ⊩ A ⇒ B = ∀ {w′ : World} → w′ ⊒ w → w′ ⊩ A → w′ ⊩ B

mono⊩ : ∀ {{_ : Model}} {A} {w w′ : World} → w′ ⊒ w → w ⊩ A → w′ ⊩ A
mono⊩ {•}      η a = monoG η a
mono⊩ {A ⇒ B} η f = λ η′ a → f (trans⊒ η′ η) a


-- Lists of values.

module IPCSemanticsList where
  open IPCList public

  infix 3 _⊩⋆_
  _⊩⋆_ : ∀ {{_ : Model}} → World → Ty⋆ → Set
  w ⊩⋆ Ξ = All (w ⊩_) Ξ

  mono⊩⋆ : ∀ {{_ : Model}} {w w′ : World} {Ξ} → w′ ⊒ w → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ η ξ = mapAll (λ {A} → mono⊩ {A} η) ξ

  lookup⊩ : ∀ {{_ : Model}} {w : World} {Ξ A} → w ⊩⋆ Ξ → Ξ ∋ A → w ⊩ A
  lookup⊩ ξ 𝒾 = lookupAll ξ 𝒾


-- Vectors of values.

module IPCSemanticsVec where
  open IPCVec public

  infix 3 _⊩⋆_
  _⊩⋆_ : ∀ {{_ : Model}} {n} → World → Ty⋆ n → Set
  w ⊩⋆ Ξ = All (w ⊩_) Ξ

  mono⊩⋆ : ∀ {{_ : Model}} {w w′ : World} {n} {Ξ : Ty⋆ n} →
              w′ ⊒ w → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ η ξ = mapAll (λ {A} → mono⊩ {A} η) ξ

  lookup⊩ : ∀ {{_ : Model}} {w : World} {n} {Ξ : Ty⋆ n} {A i} →
               w ⊩⋆ Ξ → Ξ ∋⟨ i ⟩ A → w ⊩ A
  lookup⊩ ξ 𝒾 = lookupAll ξ 𝒾
