{-# OPTIONS --rewriting #-}

module Prelude where

open import Agda.Primitive public
  using (_⊔_)

open import Agda.Builtin.Equality public
  using (_≡_ ; refl)

{-# BUILTIN REWRITE _≡_ #-}

open import Agda.Builtin.Nat public
  using (Nat ; zero ; suc)

open import Agda.Builtin.Unit public
  using (⊤ ; tt)


id : ∀ {ℓ} → {X : Set ℓ} → X → X
id x = x

flip : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″}
                   → (X → Y → Z) → Y → X
                   → Z
flip f y x = f x y

_∘_ : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {P : X → Set ℓ′} {Q : ∀ {x} → P x → Set ℓ″}
                  → (g : ∀ {x} → (y : P x) → Q y) (f : (x : X) → P x) (x : X)
                  → Q (f x)
(g ∘ f) x = g (f x)


data ⊥ : Set
  where

elim⊥ : ∀ {ℓ} → {X : Set ℓ} → ⊥ → X
elim⊥ ()

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ X = X → ⊥

_↯_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} → X → ¬ X → Y
p ↯ ¬p = elim⊥ (¬p p)

infix 4 _≢_
_≢_ : ∀ {ℓ} → {X : Set ℓ} → X → X → Set ℓ
x ≢ x′ = ¬ (x ≡ x′)


_⁻¹≡ : ∀ {ℓ} → {X : Set ℓ} {x₁ x₂ : X}
             → x₁ ≡ x₂ → x₂ ≡ x₁
refl ⁻¹≡ = refl

_⦙≡_ : ∀ {ℓ} → {X : Set ℓ} {x₁ x₂ x₃ : X}
             → x₁ ≡ x₂ → x₂ ≡ x₃ → x₁ ≡ x₃
refl ⦙≡ refl = refl


record PER {ℓ} (X : Set ℓ) (_≈_ : X → X → Set ℓ) : Set ℓ
  where
    infix  9 _⁻¹
    infixr 4 _⦙_
    field
      _⁻¹ : ∀ {x₁ x₂} → x₁ ≈ x₂
                      → x₂ ≈ x₁

      _⦙_ : ∀ {x₁ x₂ x₃} → x₁ ≈ x₂ → x₂ ≈ x₃
                         → x₁ ≈ x₃

open PER {{...}} public

instance
  per≡ : ∀ {ℓ} {X : Set ℓ} → PER X _≡_
  per≡ =
    record
      { _⁻¹ = _⁻¹≡
      ; _⦙_ = _⦙≡_
      }


infixl 9 _&_
_&_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {x₁ x₂ : X}
               → (f : X → Y) → x₁ ≡ x₂
               → f x₁ ≡ f x₂
f & refl = refl

infixl 8 _⊗_
_⊗_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {f₁ f₂ : X → Y} {x₁ x₂ : X}
               → f₁ ≡ f₂ → x₁ ≡ x₂
               → f₁ x₁ ≡ f₂ x₂
refl ⊗ refl = refl

coe : ∀ {ℓ} → {X Y : Set ℓ}
            → X ≡ Y → X → Y
coe refl x = x


module ≡-Reasoning {ℓ} {X : Set ℓ} where
  infix 1 begin_
  begin_ : ∀ {x x′ : X} → x ≡ x′ → x ≡ x′
  begin p = p

  infixr 2 _≡⟨⟩_
  _≡⟨⟩_ : ∀ (x {x′} : X) → x ≡ x′ → x ≡ x′
  x ≡⟨⟩ p = p

  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ : ∀ (x {x′ x″} : X) → x ≡ x′ → x′ ≡ x″ → x ≡ x″
  x ≡⟨ p ⟩ q = p ⦙ q

  infix 3 _∎
  _∎ : ∀ (x : X) → x ≡ x
  x ∎ = refl


data Dec {ℓ} (X : Set ℓ) : Set ℓ
  where
    yes : X → Dec X
    no  : ¬ X → Dec X


infixl 6 _,_
record Σ {ℓ ℓ′} (X : Set ℓ) (P : X → Set ℓ′) : Set (ℓ ⊔ ℓ′)
  where
    instance constructor _,_
    field
      proj₁ : X
      proj₂ : P proj₁

open Σ public

infixl 2 _×_
_×_ : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
X × Y = Σ X (λ x → Y)
