---------------------------------------------------------------------------------------------------------------

module 0-1-Prelude where

open import Category.Monad public
  using (module RawMonad)

import Codata.Colist as Colist
open Colist public
  using (Colist ; [] ; _∷_)

open import Codata.Musical.Costring public
  using (Costring)

open import Codata.Musical.Notation public
  using (♯_ ; ♭)

open import Codata.Thunk public
  using (Thunk ; force)

open import Data.Char public
  using (Char)

open import Data.Empty public
  renaming (⊥-elim to abort)

open import Data.Fin public
  using (Fin ; zero ; suc)

import Data.List as List
open List public
  using (List ; [] ; _∷_)

open import Data.Maybe public
  using (Maybe ; nothing ; just)

open import Data.Maybe.Categorical public
  using ()
  renaming (monad to monad-Maybe)

open import Data.Nat public
  using (zero ; suc)
  renaming (ℕ to Nat)

open import Data.Product public
  using (Σ ; ∃ ; _×_ ; _,_ ; uncurry)

import Data.String as String
open String public
  using (String ; _++_)

open import Data.Unit public
  using (⊤)

open import Data.String.Unsafe public
  using (_≟_)

open import Data.Sum public
  using (_⊎_ ; inj₁ ; inj₂)

open import Data.Vec public
  using (Vec ; [] ; _∷_ ; _[_]=_ ; here ; there)

open import Function public
  using (_∘_ ; case_of_ ; flip)

import IO

open import Level public
  using (Lift ; _⊔_)
  renaming (0ℓ to 0ᴸ)

open import Relation.Binary public
  using (REL ; Rel ; Reflexive ; Transitive)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; _≢_ ; refl ; Extensionality)
  renaming (cong to _&_ ; sym to _⁻¹)

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
--
-- Stuttering colists

module Cocolist where
  open IO using (IO ; _>>=_ ; _>>_ ; return)
  open Size using (∞)

  data Cocolist {a} (A : Set a) (i : Size) : Set a where
    []  : Cocolist A i
    -∷_ : Thunk (Cocolist A) i → Cocolist A i
    _∷_ : A → Thunk (Cocolist A) i → Cocolist A i

  fromColist : ∀ {a i} {A : Set a} → Colist A i → Cocolist A i
  fromColist []       = []
  fromColist (x ∷ xs) = x ∷ λ where .force → fromColist (xs .force)

  fromCostring : Costring → Cocolist Char ∞
  fromCostring = fromColist ∘ Colist.fromMusical

  fromList : ∀ {a} {A : Set a} → List A → Cocolist A ∞
  fromList []       = []
  fromList (x ∷ xs) = x ∷ λ where .force → fromList xs

  fromString : String → Cocolist Char ∞
  fromString = fromList ∘ String.toList

  toList : ∀ {a} {A : Set a} → Nat → Cocolist A ∞ → List A
  toList zero    xs       = []
  toList (suc n) []       = []
  toList (suc n) (-∷ xs)  = toList n (xs .force)
  toList (suc n) (x ∷ xs) = x ∷ toList n (xs .force)

  map : ∀ {a b i} {A : Set a} {B : Set b} (f : A → B) → Cocolist A i → Cocolist B i
  map f []       = []
  map f (-∷ xs)  = -∷ λ where .force → map f (xs .force)
  map f (x ∷ xs) = f x ∷ λ where .force → map f (xs .force)

  sequence : ∀ {a} {A : Set a} → Cocolist (IO A) ∞ → IO (Cocolist A ∞)
  sequence []       = return []
  sequence (-∷ as)  = do xs ← ♯ sequence (as .force)
                         ♯ return xs
  sequence (a ∷ as) = do x ← ♯ a
                         ♯ (do xs ← ♯ sequence (as .force)
                               ♯ return (x ∷ λ where .force → xs))

  sequence′ : ∀ {a} {A : Set a} → Cocolist (IO A) ∞ → IO (Lift a ⊤)
  sequence′ []       = return _
  sequence′ (-∷ as)  = do ♯ sequence (as .force)
                          ♯ return _
  sequence′ (a ∷ as) = do ♯ a
                          ♯ (do ♯ sequence′ (as .force)
                                ♯ return _)

  mapM : ∀ {a b} {A : Set a} {B : Set b} → (A → IO B) → Cocolist A ∞ → IO (Cocolist B ∞)
  mapM f = sequence ∘ map f

  mapM′ : ∀ {a b} {A : Set a} {B : Set b} → (A → IO B) → Cocolist A ∞ → IO (Lift b ⊤)
  mapM′ f = sequence′ ∘ map f


---------------------------------------------------------------------------------------------------------------
