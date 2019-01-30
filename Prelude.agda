---------------------------------------------------------------------------------------------------------------

module Prelude where

open import Data.Empty public
  using (⊥ ; ⊥-elim)

open import Data.List public
  using (List ; [] ; _∷_)

open import Data.Nat public
  using (_≤_ ; _<_ ; _+_ ; _⊔_ ; s≤s ; suc ; z≤n ; zero)
  renaming (ℕ to Nat)

open import Data.Nat.Properties public
  using (module ≤-Reasoning ; ≤-refl ; ≤-step ; ≤-trans
    ; +-comm ; +-mono-≤ ; +-monoˡ-≤ ; m≤m+n ; n≤m+n
    ; m≤m⊔n ; n≤m⊔n)
open ≤-Reasoning public

open import Data.Product public
  using (_×_ ; _,_ ; Σ ; ∃ ; proj₁ ; proj₂)

open import Data.Sum public
  using (_⊎_ ; inj₁ ; inj₂)

open import Data.Unit public
  using (⊤ ; tt)

open import Function public
  using (case_of_)

open import Level public
  using ()
  renaming (_⊔_ to _⊔ᴸ_ ; 0ℓ to 0ᴸ)

open import Relation.Binary public
  using (Decidable ; DecSetoid ; Reflexive ; Rel ; Transitive)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; _≢_ ; refl ; subst)
  renaming (cong to _&_ ; sym to _⁻¹ ; isEquivalence to ≡-isEquivalence)

import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
open Star public
  using ()
  renaming (Star to _* ; ε to [] ; _◅_ to _∷_ ; _◅◅_ to _++_)

open import Relation.Nullary public
  using (¬_ ; Dec ; no ; yes)

open import Relation.Nullary.Negation public
  using (contraposition)
  renaming (contradiction to _↯_)

open import Relation.Unary public
  using (Pred)


---------------------------------------------------------------------------------------------------------------

_↔_ : ∀ {a b} → Set a → Set b → Set (a ⊔ᴸ b)
A ↔ B = (A → B) × (B → A)

infixl 8 _⊗_
_⊗_ : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} {x y : A} →
      f ≡ g → x ≡ y → f x ≡ g y
refl ⊗ refl = refl

coerce : ∀ {ℓ} {A B : Set ℓ} → A → A ≡ B → B
coerce x refl = x

Pred₀ : ∀ {a} → Set a → Set _
Pred₀ A = Pred A 0ᴸ

Rel₀ : ∀ {a} → Set a → Set _
Rel₀ A = Rel A 0ᴸ

pattern _∷⟨_⟩_ r y rs = _∷_ {_} {y} {_} r rs

_∷ʳ_ : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} →
       ∀ {x y z} → (R *) x y → R y z → (R *) x z
R*xy ∷ʳ Ryz = R*xy ++ (Ryz ∷ [])

map : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} {f : A → A} →
      (∀ {x y} → R x y → R (f x) (f y)) →
      ∀ {x y} → (R *) x y → (R *) (f x) (f y)
map {f = f} = Star.gmap f


---------------------------------------------------------------------------------------------------------------
