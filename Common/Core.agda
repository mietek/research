module Common.Core where

open import Agda.Builtin.Size public
  using (Size ; Size<_)
  renaming (ω to ∞)

open import Data.Bool public
  using ()
  renaming (_∧_ to _ᴮ∧_ ; _∨_ to _ᴮ∨_ ; not to ᴮ¬_)

open import Data.Empty public
  using ()
  renaming (⊥ to ᴬᵍ⊥ ; ⊥-elim to ᴬᵍboom)

open import Data.Product public
  using (Σ)
  renaming (_×_ to _ᴬᵍ∧_ ; _,_ to ᴬᵍpair ; proj₁ to ᴬᵍfst ; proj₂ to ᴬᵍsnd)

open import Data.Sum public
  using ()
  renaming (_⊎_ to _ᴬᵍ∨_ ; inj₁ to ᴬᵍinl ; inj₂ to ᴬᵍinr)

open import Data.Unit public
  using ()
  renaming (⊤ to ᴬᵍ⊤ ; tt to ᴬᵍtt)

open import Function public
  using (_∘_ ; _$_)
  renaming (id to ᴬᵍid ; const to ᴬᵍconst ; _ˢ_ to ᴬᵍap)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; _≢_ ; refl ; trans ; sym ; cong ; cong₂ ; subst)

open import Relation.Nullary public
  using ()
  renaming (¬_ to ᴬᵍ¬_)

open import Relation.Nullary.Negation public
  using ()
  renaming (contradiction to _ᴬᵍ↯_)


-- Atoms, for propositional variables.

postulate
  Atom : Set


-- Miscellaneous.

ᴬᵍcase : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
         → A ᴬᵍ∨ B → (A → C) → (B → C) → C
ᴬᵍcase (ᴬᵍinl x) f g = f x
ᴬᵍcase (ᴬᵍinr y) f g = g y

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x x′ y y′ z z′}
        → x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl
