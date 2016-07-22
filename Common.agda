module Common where

open import Agda.Builtin.Size public
  using (Size ; Size<_)
  renaming (ω to ∞)

open import Data.Bool public
  using ()
  renaming (_∧_ to _∧ᴮ_ ; _∨_ to _∨ᴮ_ ; not to ¬ᴮ_)

open import Data.Empty public
  using ()
  renaming (⊥ to Bot ; ⊥-elim to elimBot)

open import Data.Nat public
  using (ℕ ; zero ; suc)

open import Data.Product public
  using (Σ ; ∃ ; _×_ ; _,_)
  renaming (proj₁ to π₁ ; proj₂ to π₂)

open import Data.Sum public
  using (_⊎_)
  renaming (inj₁ to ι₁ ; inj₂ to ι₂)

open import Data.Unit public
  using ()
  renaming (⊤ to Top ; tt to ∙)

open import Function public
  using (_∘_ ; _$_ ; id ; const)
  renaming (_ˢ_ to ap)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; _≢_ ; refl ; trans ; sym ; cong ; cong₂ ; subst)

open import Relation.Nullary public
  using ()
  renaming (¬_ to Not)

open import Relation.Nullary.Negation public
  using ()
  renaming (contradiction to _↯_)


-- Atoms, for propositional variables.

postulate
  Atom : Set


-- Miscellaneous.

κ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    → A ⊎ B → (A → C) → (B → C) → C
κ (ι₁ x) f g = f x
κ (ι₂ y) f g = g y

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x x′ y y′ z z′}
        → x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl

module _ {W : Set} where
  _⨾_ : (W → W → Set) → (W → W → Set) → (W → W → Set)
  _P_ ⨾ _R_ = λ a b → ∃ (λ z → a P z × z R b)
