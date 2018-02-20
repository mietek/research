module Subset where

open import Prelude
open import Category


Pred : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
Pred {ℓ} X = X → Set ℓ


module One {X : Set}
  where
    infix 4 _∈_
    _∈_ : X → Pred X → Set
    A ∈ P = P A

    ∅ : Pred X
    ∅ _ = ⊥

    𝒰 : Pred X
    𝒰 _ = ⊤

    bot∈ : ∀ {X} → ¬ (X ∈ ∅)
    bot∈ = elim⊥

    top∈ : ∀ {X} → X ∈ 𝒰
    top∈ = ∙

    infix 4 _⊆_
    _⊆_ : Pred X → Pred X → Set
    P ⊆ Q = ∀ {A} → A ∈ P → A ∈ Q

    refl⊆ : ∀ {P} → P ⊆ P
    refl⊆ = id

    trans⊆ : ∀ {P Q R} → Q ⊆ R → P ⊆ Q → P ⊆ R
    trans⊆ η₁ η₂ = η₁ ∘ η₂

    bot⊆ : ∀ {P} → ∅ ⊆ P
    bot⊆ = elim⊥

    top⊆ : ∀ {P} → P ⊆ 𝒰
    top⊆ _ = ∙


module Two {X : Set}
  where
    open import List

    data All (P : Pred X) : Pred (List X) where
      ∙   : All P ∙
      _,_ : ∀ {A Ξ} → All P Ξ → P A → All P (Ξ , A)

    data Any (P : Pred X) : Pred (List X) where
      zero : ∀ {A Ξ} → P A → Any P (Ξ , A)
      suc  : ∀ {A Ξ} → Any P Ξ → Any P (Ξ , A)

    infix 4 _∈_
    _∈_ : X → Pred (List X)
    A ∈ Ξ = Any (_≡ A) Ξ

    bot∈ : ∀ {A} → ¬ (A ∈ ∙)
    bot∈ ()

    get : ∀ {Ξ P} → All P Ξ → (∀ {A} → A ∈ Ξ → P A)
    get (ξ , a) (zero refl) = a
    get (ξ , b) (suc i)     = get ξ i

    put : ∀ {Ξ P} → (∀ {A} → A ∈ Ξ → P A) → All P Ξ
    put {∙}     f = ∙
    put {Ξ , A} f = put (f ∘ suc) , f (zero refl)

    infix 4 _⊆_
    _⊆_ : List X → Pred (List X)
    Ξ ⊆ Ξ′ = ∀ {A} → A ∈ Ξ → A ∈ Ξ′

    drop⊆ : ∀ {A Ξ Ξ′} → Ξ ⊆ Ξ′ → Ξ ⊆ Ξ′ , A
    drop⊆ η = suc ∘ η

    keep⊆ : ∀ {A Ξ Ξ′} → Ξ ⊆ Ξ′ → Ξ , A ⊆ Ξ′ , A
    keep⊆ η (zero refl) = zero refl
    keep⊆ η (suc i)     = suc (η i)

    refl⊆ : ∀ {Ξ} → Ξ ⊆ Ξ
    refl⊆ = id

    trans⊆ : ∀ {Ξ Ξ′ Ξ″} → Ξ′ ⊆ Ξ″ → Ξ ⊆ Ξ′ → Ξ ⊆ Ξ″
    trans⊆ η₁ η₂ = η₁ ∘ η₂

    bot⊆ : ∀ {Ξ} → ∙ ⊆ Ξ
    bot⊆ ()
