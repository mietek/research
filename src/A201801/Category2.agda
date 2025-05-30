{-# OPTIONS --irrelevant-projections #-}

module A201801.Category2 where

open import Agda.Primitive public
  using (_⊔_)

open import Agda.Builtin.Equality public
  using (_≡_ ; refl)


--------------------------------------------------------------------------------


record Category {ℓ ℓ′} (X : Set ℓ) (_▻_ : X → X → Set ℓ′)
                     : Set (ℓ ⊔ ℓ′)
  where
    field
      id : ∀ {x} → x ▻ x

      _∘_ : ∀ {x y z} → y ▻ x → z ▻ y
                      → z ▻ x

      lid∘ : ∀ {x y} → (f : y ▻ x)
                     → id ∘ f ≡ f

      rid∘ : ∀ {x y} → (f : y ▻ x)
                     → f ∘ id ≡ f

      assoc∘ : ∀ {x y z a} → (f : y ▻ x) (g : z ▻ y) (h : a ▻ z)
                           → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

open Category {{...}} public


record Squash {ℓ} (X : Set ℓ) : Set ℓ
  where
    constructor squash
    field
      .unsquash : X

open Squash public


--------------------------------------------------------------------------------


module Attempt1
  where
    record Proset {ℓ ℓ′} (X : Set ℓ) (_≥_ : X → X → Set ℓ′)
                       : Set (ℓ ⊔ ℓ′)
      where
        field
          refl≥ : ∀ {x} → x ≥ x

          trans≥ : ∀ {x y z} → y ≥ x → z ≥ y
                             → z ≥ x

    open Proset {{...}} public


    category : ∀ {ℓ ℓ′} → {X : Set ℓ} {_≥_ : X → X → Set ℓ′}
                        → Proset X _≥_
                        → Category X (\ x y → Squash (x ≥ y))
    category P = record
                   { id     = squash refl≥
                   ; _∘_    = \ f g → squash (trans≥ (unsquash f) (unsquash g))
                   ; lid∘   = \ f → refl
                   ; rid∘   = \ f → refl
                   ; assoc∘ = \ f g h → refl
                   }
      where
        instance _ = P


--------------------------------------------------------------------------------


module Attempt2
  where
    record Proset {ℓ ℓ′} (X : Set ℓ) (_≥_ : X → X → Set ℓ′)
                       : Set (ℓ ⊔ ℓ′)
      where
        _⌊≥⌋_ : X → X → Set ℓ′
        _⌊≥⌋_ = \ x y → Squash (x ≥ y)

        field
          refl⌊≥⌋ : ∀ {x} → x ⌊≥⌋ x

          trans⌊≥⌋ : ∀ {x y z} → y ⌊≥⌋ x → z ⌊≥⌋ y
                               → z ⌊≥⌋ x

    open Proset {{...}} public


    category : ∀ {ℓ ℓ′} → {X : Set ℓ} {_≥_ : X → X → Set ℓ′}
                        → Proset X _≥_
                        → Category X (\ x y → Squash (x ≥ y))
    category P = record
                   { id     = refl⌊≥⌋
                   ; _∘_    = trans⌊≥⌋
                   ; lid∘   = \ f → refl
                   ; rid∘   = \ f → refl
                   ; assoc∘ = \ f g h → refl
                   }
      where
        instance _ = P


--------------------------------------------------------------------------------


module Attempt3
  where
    record Proset {ℓ ℓ′} (X : Set ℓ) (_≥_ : X → X → Set ℓ′)
                       : Set (ℓ ⊔ ℓ′)
      where
        field
          refl≥ : ∀ {x} → x ≥ x

          trans≥ : ∀ {x y z} → y ≥ x → z ≥ y
                             → z ≥ x

          uniq≥ : ∀ {x y} → (η₁ η₂ : x ≥ y)
                          → η₁ ≡ η₂

    open Proset {{...}} public


    category : ∀ {ℓ ℓ′} → {X : Set ℓ} {_≥_ : X → X → Set ℓ′}
                        → Proset X _≥_
                        → Category X _≥_
    category P = record
                   { id     = refl≥
                   ; _∘_    = trans≥
                   ; lid∘   = \ f → uniq≥ (trans≥ refl≥ f) f
                   ; rid∘   = \ f → uniq≥ (trans≥ f refl≥) f
                   ; assoc∘ = \ f g h → uniq≥ (trans≥ (trans≥ f g) h) (trans≥ f (trans≥ g h))
                   }
      where
        instance _ = P


--------------------------------------------------------------------------------
