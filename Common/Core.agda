module Common.Core where

open import Agda.Builtin.Size public
  using (Size ; Size<_)
  renaming (ω to ∞)

open import Data.Bool public
  using ()
  renaming (_∧_ to _ᴮ∧_ ; _∨_ to _ᴮ∨_ ; not to ᴮ¬_)

open import Data.Empty public
  using ()
  renaming (⊥ to ᴬ⊥ ; ⊥-elim to ᴬboom)

open import Data.Product public
  using (Σ)
  renaming (_×_ to _ᴬ∧_ ; _,_ to ᴬpair ; proj₁ to ᴬfst ; proj₂ to ᴬsnd)

open import Data.Sum public
  using ()
  renaming (_⊎_ to _ᴬ∨_ ; inj₁ to ᴬinl ; inj₂ to ᴬinr)

open import Data.Unit public
  using ()
  renaming (⊤ to ᴬ⊤ ; tt to ᴬtt)

open import Function public
  using (_∘_ ; _$_)
  renaming (id to ᴬid ; const to ᴬconst ; _ˢ_ to ᴬap)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; _≢_ ; refl ; trans ; sym ; cong ; cong₂)

open import Relation.Nullary public
  using ()
  renaming (¬_ to ᴬ¬_)

open import Relation.Nullary.Negation public
  using ()
  renaming (contradiction to _ᴬ↯_)


-- Atoms, for propositional variables.

postulate
  Atom : Set


-- Miscellaneous.

ᴬcase : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
        → A ᴬ∨ B → (A → C) → (B → C) → C
ᴬcase (ᴬinl x) f g = f x
ᴬcase (ᴬinr y) f g = g y

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x x′ y y′ z z′}
        → x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl
