module Common.Core where

open import Agda.Builtin.Size public
  using (Size ; Size<_)
  renaming (ω to ∞)

open import Data.Empty public
  using (⊥)
  renaming (⊥-elim to elim⊥)

open import Data.Product public
  using (Σ ; _×_ ; proj₁ ; proj₂)
  renaming (_,_ to _∙_)

open import Data.Sum public
  using (_⊎_ ; inj₁ ; inj₂)
  renaming ([_,_] to [_∣_]_)

open import Data.Unit public
  using (⊤ ; tt)

open import Function public
  using (_∘_ ; _$_ ; id ; const)
  renaming (_ˢ_ to ap)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; _≢_ ; refl ; trans ; sym ; cong ; cong₂)

open import Relation.Nullary public
  using (¬_)

open import Relation.Nullary.Negation public
  using ()
  renaming (contradiction to _↯_)


-- Atoms, for propositional variables.

postulate
  Atom : Set


-- Miscellaneous.

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x x′ y y′ z z′} → x ≡ x′ → y ≡ y′ → z ≡ z′
        → f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl
