module A202103.Prelude where

open import Data.Empty public
  using ()
  renaming (⊥ to 𝟘)

open import Data.Product public
  using (Σ ; _,_ ; _×_) renaming (proj₁ to π₁ ; proj₂ to π₂)

open import Data.Sum public
  using (_⊎_) renaming (inj₁ to ι₁ ; inj₂ to ι₂)

open import Data.Unit public
  using ()
  renaming (⊤ to 𝟙 ; tt to ·)

import Function
open Function public
  using (_∘_ ; flip ; id)

open import Level public
  using (Level ; _⊔_)
  renaming (zero to lzero ; suc to lsuc)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; refl)

open import Relation.Nullary public
  using (¬_)

open import Relation.Nullary.Negation public
  using ()
  renaming (contradiction to _↯_)

------------------------------------------------------------------------------

atType = Function._∋_

syntax atType A x = x ⦂ A

Π : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Π A B = A → B

infix 9 _⁻¹
_⁻¹ : ∀ {a} {A : Set a} {x y : A} →
      x ≡ y → y ≡ x
refl ⁻¹ = refl

infixr 4 _⋮_
_⋮_ : ∀ {a} {A : Set a} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
refl ⋮ refl = refl

infixl 9 _&_
_&_ : ∀ {a b} {A : Set a} {B : Set b} {x y : A} →
      (f : A → B) → x ≡ y → f x ≡ f y
f & refl = refl

infixl 8 _⊗_
_⊗_ : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} {x y : A} →
      f ≡ g → x ≡ y → f x ≡ g y
refl ⊗ refl = refl

cast : ∀ {a} {A B : Set a} → A → A ≡ B → B
cast x refl = x

postulate
  fu : ∀ {a b} {A : Set a} {B : A → Set b} {f g : ∀ x → B x} →
       (∀ x → f x ≡ g x) → f ≡ g

postulate
  fu′ : ∀ {a b} {A : Set a} {B : A → Set b} {f g : ∀ {x} → B x} →
        (∀ {x} → f {x} ≡ g {x}) →
        (λ {x} → f {x}) ≡ (λ {x} → g {x})

ha : ∀ {a b} {A : Set a} {B : A → Set b} {f g : ∀ x → B x} →
     f ≡ g → (∀ x → f x ≡ g x)
ha refl x = refl

ha′ : ∀ {a b} {A : Set a} {B : A → Set b} {f g : ∀ {x} → B x} →
      (λ {x} → f {x}) ≡ (λ {x} → g {x}) →
      (∀ {x} → f {x} ≡ g {x})
ha′ refl = refl

postulate
  Atom : Set

------------------------------------------------------------------------------
