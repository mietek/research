{-# OPTIONS --guardedness --sized-types #-}

---------------------------------------------------------------------------------------------------------------

module A201903.0-1-Prelude where

open import Axiom.Extensionality.Propositional public
  using (Extensionality)

open import Codata.Musical.Costring public
  using (Costring)

open import Codata.Musical.Notation public
  using (♯_ ; ♭)

open import Codata.Sized.Colist public
  using (Colist ; [] ; _∷_)

open import Codata.Sized.Thunk public
  using (Thunk ; force)

open import Data.Char public
  using (Char)

open import Data.Empty public
  renaming (⊥-elim to abort)

open import Data.Fin public
  using (Fin ; zero ; suc)

open import Data.List public
  using (List ; [] ; _∷_)

open import Data.List.NonEmpty public
  using (List⁺ ; _∷_)

open import Data.Maybe public
  using (Maybe ; nothing ; just)

open import Data.Nat public
  using (zero ; suc)
  renaming (ℕ to Nat)

open import Data.Product public
  using (Σ ; ∃ ; _×_ ; _,_ ; uncurry)

open import Data.String public
  using (String ; _++_)

open import Data.Unit public
  using (⊤)

open import Data.String.Properties public
  using (_≟_)

open import Data.Sum public
  using (_⊎_ ; inj₁ ; inj₂)

open import Data.Vec public
  using (Vec ; [] ; _∷_ ; _[_]=_ ; here ; there)

open import Effect.Monad public
  using (module RawMonad)

open import Function public
  using (_∘_ ; case_of_ ; flip)

open import Level public
  using (Lift ; _⊔_)
  renaming (0ℓ to 0ᴸ)

open import Relation.Binary public
  using (REL ; Rel ; Reflexive ; Transitive)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; _≢_ ; refl ; inspect)
  renaming (cong to _&_ ; sym to _⁻¹ ; [_] to _ⁱ)

open import Relation.Nullary public
  using (¬_ ; Dec ; yes ; no)

open import Relation.Nullary.Negation public
  using ()
  renaming (contradiction to _↯_)

open import Relation.Unary public
  using (Pred)

open import Size public
  using (Size ; Size<_ ; ∞)


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

Pred₀ : Set₀ → Set₁
Pred₀ A = Pred A _

REL₀ : Set₀ → Set₀ → Set₁
REL₀ A B = REL A B _

Rel₀ : Set₀ → Set₁
Rel₀ A = Rel A _


---------------------------------------------------------------------------------------------------------------
--
-- Codata.Colist extras

splitAt : ∀ {a} {A : Set a} → Nat → Colist A ∞ → List A × Colist A ∞
splitAt zero    xs       = [] , xs
splitAt (suc n) []       = [] , []
splitAt (suc n) (x ∷ xs) with splitAt n (xs .force)
... | xs′ , xs″          = x ∷ xs′ , xs″


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

map* : ∀ {a b ℓ₁ ℓ₂ i} {A : Set a} {B : Set b} {R₁ : Rel A ℓ₁} {R₂ : Rel B ℓ₂} {f : A → B} →
       (∀ {x y} → R₁ x y → R₂ (f x) (f y)) →
       ∀ {x y} → (R₁ *⟨ i ⟩) x y → (R₂ *⟨ i ⟩) (f x) (f y)
map* g ε        = ε
map* g (r ◅ rs) = g r ◅ map* g rs


---------------------------------------------------------------------------------------------------------------
--
-- Properties of relations

module Relations where
  module Unary where
    open Relation.Unary public
      using (Decidable)

    Unique : ∀ {a ℓ} {A : Set a} → Pred (Pred A ℓ) (a ⊔ ℓ)
    Unique P = ∀ {e} (p p′ : P e) → p ≡ p′

  module Binary where
    Unique : ∀ {a ℓ} {A : Set a} → Pred (Rel A ℓ) (a ⊔ ℓ)
    Unique R = ∀ {e e′} (r r′ : R e e′) → r ≡ r′

    Deterministic : ∀ {a ℓ} {A : Set a} → Pred (Rel A ℓ) (a ⊔ ℓ)
    Deterministic R = ∀ {e e′ e″} → R e e′ → R e e″ → e′ ≡ e″

    Confluent : ∀ {a ℓ} {A : Set a} → Pred (Rel A ℓ) (a ⊔ ℓ)
    Confluent R = ∀ {e e′ e″} → (R *) e e′ → (R *) e e″ → (∃ λ e‴ → (R *) e′ e‴ × (R *) e″ e‴)


---------------------------------------------------------------------------------------------------------------
