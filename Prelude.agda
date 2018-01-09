{-# OPTIONS --rewriting #-}

module Prelude where

open import Agda.Primitive public
  using (Level ; lzero ; lsuc ; _⊔_)

open import Agda.Builtin.Equality public
  using (_≡_ ; refl)

open import Agda.Builtin.Nat public
  using (Nat ; zero ; suc)

open import Agda.Builtin.Unit public
  using (⊤)
  renaming (tt to ∙)


--------------------------------------------------------------------------------


Π : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
Π X Y = X → Y


_∘′_ : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {P : X → Set ℓ′} {Q : ∀ {x} → P x → Set ℓ″}
                   → (f : ∀ {x} → (y : P x) → Q y) (g : ∀ x → P x) (x : X)
                   → Q (g x)
(f ∘′ g) x = f (g x)


flip : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″}
                   → (X → Y → Z) → Y → X
                   → Z
flip f y x = f x y


--------------------------------------------------------------------------------


data ⊥ : Set
  where


elim⊥ : ∀ {ℓ} → {X : Set ℓ} → ⊥ → X
elim⊥ ()


¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ X = X → ⊥


_↯_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} → X → ¬ X → Y
x ↯ f = elim⊥ (f x)


--------------------------------------------------------------------------------


{-# BUILTIN REWRITE _≡_ #-}


infix 4 _≢_
_≢_ : ∀ {ℓ} → {X : Set ℓ} → X → X → Set ℓ
x ≢ x′ = ¬ (x ≡ x′)


_⁻¹≡ : ∀ {ℓ} → {X : Set ℓ} {x y : X} → x ≡ y → y ≡ x
refl ⁻¹≡ = refl


_⋮≡_ : ∀ {ℓ} → {X : Set ℓ} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
refl ⋮≡ refl = refl


--------------------------------------------------------------------------------


record PER {ℓ} (X : Set ℓ) (_≈_ : X → X → Set ℓ) : Set ℓ
  where
    infix 9 _⁻¹
    infixr 4 _⋮_
    field
      _⁻¹ : ∀ {x y} → x ≈ y → y ≈ x
      _⋮_ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

open PER {{...}} public


instance
  per≡ : ∀ {ℓ} {X : Set ℓ} → PER X _≡_
  per≡ = record
           { _⁻¹ = _⁻¹≡
           ; _⋮_ = _⋮≡_
           }


--------------------------------------------------------------------------------


infixl 9 _&_
_&_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {x y : X}
               → (f : X → Y) → x ≡ y
               → f x ≡ f y
f & refl = refl


infixl 8 _⊗_
_⊗_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {f g : X → Y} {x y : X}
               → f ≡ g → x ≡ y
               → f x ≡ g y
refl ⊗ refl = refl


coerce : ∀ {ℓ} → {X Y : Set ℓ}
               → X → X ≡ Y
               → Y
coerce x refl = x


postulate
  funext! : ∀ {ℓ ℓ′} → {X : Set ℓ} {P : X → Set ℓ′} {f g : ∀ x → P x}
                     → (∀ x → f x ≡ g x)
                     → f ≡ g

postulate
  funext!′ : ∀ {ℓ ℓ′} → {X : Set ℓ} {P : X → Set ℓ′} {f g : ∀ {x} → P x}
                      → (∀ x → f {x} ≡ g {x})
                      → (\ {x} → f {x}) ≡ (\ {x} → g {x})


--------------------------------------------------------------------------------


module ≡-Reasoning {ℓ} {X : Set ℓ}
  where
    infix 1 begin_
    begin_ : ∀ {x y : X} → x ≡ y → x ≡ y
    begin p = p

    infixr 2 _≡⟨⟩_
    _≡⟨⟩_ : ∀ (x {y} : X) → x ≡ y → x ≡ y
    x ≡⟨⟩ p = p

    infixr 2 _≡⟨_⟩_
    _≡⟨_⟩_ : ∀ (x {y z} : X) → x ≡ y → y ≡ z → x ≡ z
    x ≡⟨ p ⟩ q = p ⋮ q

    infix 3 _∎
    _∎ : ∀ (x : X) → x ≡ x
    x ∎ = refl


--------------------------------------------------------------------------------


suc-inj : ∀ {n m} → suc n ≡ suc m
                  → n ≡ m
suc-inj refl = refl


data Dec {ℓ} (X : Set ℓ) : Set ℓ
  where
    instance
      yes : X → Dec X
      no  : ¬ X → Dec X


module Inspect
  where
    record Reveal_$_is_ {ℓ ℓ′} {X : Set ℓ} {P : X → Set ℓ′}
                               (f : ∀ x → P x) (x : X) (y : P x)
                             : Set (ℓ ⊔ ℓ′)
      where
        constructor [_]
        field
          eq : f x ≡ y


    inspect : ∀ {ℓ ℓ′} → {X : Set ℓ} {P : X → Set ℓ′}
                       → (f : ∀ x → P x) (x : X)
                       → Reveal f $ x is f x
    inspect f x = [ refl ]


--------------------------------------------------------------------------------


infixl 6 _,_
record Σ {ℓ ℓ′} (X : Set ℓ) (P : X → Set ℓ′) : Set (ℓ ⊔ ℓ′)
  where
    instance
      constructor _,_
    field
      proj₁ : X
      proj₂ : P proj₁

open Σ public


infixl 2 _×_
_×_ : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
X × Y = Σ X (\ x → Y)


--------------------------------------------------------------------------------
