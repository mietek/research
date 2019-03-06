---------------------------------------------------------------------------------------------------------------

module 1-0-Prelude where

open import Data.Fin public
  using (Fin ; zero ; suc)

open import Data.Nat public
  using (zero ; suc)
  renaming (ℕ to Nat)

open import Data.Product public
  using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂ ; uncurry)

open import Data.Sum public
  using (_⊎_ ; inj₁ ; inj₂)

open import Function public
  using (_∘_ ; case_of_ ; id)

open import Level public
  using (_⊔_)
  renaming (suc to sucᴸ)

open import Relation.Binary public
  using (Rel ; REL ; Reflexive ; Transitive)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; _≢_ ; refl)
  renaming (cong to _&_ ; sym to _⁻¹)

open import Relation.Nullary public
  using (¬_ ; Dec ; yes ; no)

open import Relation.Nullary.Negation public
  using ()
  renaming (contradiction to _↯_)

open import Relation.Unary public
  using (Pred)

open import Size public
  using (Size ; Size<_ ; ↑_ ; ∞)


---------------------------------------------------------------------------------------------------------------
--
-- Miscellaneous

infix 1 _↔_
_↔_ : ∀ {a b} → Set a → Set b → Set _
A ↔ B = (A → B) × (B → A)

infixl 8 _⊗_
_⊗_ : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} {x y : A} →
      f ≡ g → x ≡ y → f x ≡ g y
refl ⊗ refl = refl

coerce : ∀ {ℓ} {A B : Set ℓ} → A → A ≡ B → B
coerce x refl = x

Pred₀ : Set₀ → Set₁
Pred₀ A = Pred A _

Rel₀ : Set₀ → Set₁
Rel₀ A = Rel A _

REL₀ : Set₀ → Set₀ → Set₁
REL₀ A B = REL A B _


---------------------------------------------------------------------------------------------------------------
--
-- Data.Product extras

∃² : ∀ {a b c} {A : Set a} {B : Set b} → (A → B → Set c) → Set (a ⊔ b ⊔ c)
∃² f = Σ (_ × _) (uncurry f)

∃³ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} → (A → B → C → Set d) → Set (a ⊔ b ⊔ c ⊔ d)
∃³ f = Σ (_ × _ × _) λ { (x , y , z) → f x y z }


---------------------------------------------------------------------------------------------------------------
--
-- Sized Data.Star replacement

infixr 5 _◅_
data _*⟨_⟩ {a ℓ} {A : Set a} (R : Rel A ℓ) (i : Size) : Rel A (a ⊔ ℓ) where
  ε   : Reflexive (R *⟨ i ⟩)
  _◅_ : ∀ {j : Size< i} {x y z} → R x y → (R *⟨ j ⟩) y z → (R *⟨ i ⟩) x z

_* : ∀ {a ℓ} {A : Set a} (R : Rel A ℓ) → Rel A (a ⊔ ℓ)
R * = R *⟨ ∞ ⟩

{-# DISPLAY _*⟨_⟩ R ∞ = R * #-}

infixr 5 _◅◅_
_◅◅_ : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} → Transitive (R *)
ε        ◅◅ rs′ = rs′
(r ◅ rs) ◅◅ rs′ = r ◅ (rs ◅◅ rs′)

map : ∀ {a b ℓ₁ ℓ₂ i} {A : Set a} {B : Set b} {R₁ : Rel A ℓ₁} {R₂ : Rel B ℓ₂} {f : A → B} →
      (∀ {x y} → R₁ x y → R₂ (f x) (f y)) →
      ∀ {x y} → (R₁ *⟨ i ⟩) x y → (R₂ *⟨ i ⟩) (f x) (f y)
map g ε        = ε
map g (r ◅ rs) = g r ◅ map g rs


---------------------------------------------------------------------------------------------------------------
