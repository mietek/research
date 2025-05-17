-- 2025-03-21
-- Friedman’s A-Translation
-- https://www.mscs.dal.ca/~selinger/papers/friedman.pdf
-- thanks to roconnor, ncf, drvink, and ames
-- first-order predicate logic with one sort (naturals) and one predicate (equality)
-- variant with first-order structures for renaming and substitution

-- {-# OPTIONS --rewriting #-}

module Selinger92 where

-- open import Agda.Builtin.Equality.Rewrite

open import Agda.Builtin.FromNat public
  using (Number ; fromNat)

open import Agda.Primitive public
  using (Level ; _⊔_ ; lzero ; lsuc ; Setω)

open import Data.Empty public
  using (⊥)

import Data.Fin as Fin
open Fin public
  using (Fin ; zero ; suc)

import Data.Nat as Nat
open Nat public
  using (zero ; suc ; pred)
  renaming (ℕ to Nat)

open import Data.Product public
  using (Σ)
  renaming (_×_ to _∧_ ; _,_ to sig ; proj₁ to fst ; proj₂ to snd)

open import Data.Sum public
  using ()
  renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)

open import Data.Unit public
  using (⊤ ; tt)

open import Function public
  using (_∘_ ; _$_ ; const ; flip ; id)

import Relation.Binary.PropositionalEquality as Id
open Id public
  using (_≡_ ; refl ; subst ; module ≡-Reasoning)

open import Relation.Nullary public
  using (Dec ; yes ; no ; ¬_)
  renaming (contradiction to _↯_)

open import Relation.Nullary.Decidable public
  using (True)


----------------------------------------------------------------------------------------------------

-- 0.0. missing things

infix 9 _⁻¹
_⁻¹ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} → x ≡ x′ → x′ ≡ x
refl ⁻¹ = refl

infixr 4 _⋮_
_⋮_ : ∀ {𝓍} {X : Set 𝓍} {x x′ x″ : X} → x ≡ x′ → x′ ≡ x″ → x ≡ x″
refl ⋮ refl = refl

infixl 9 _&_
_&_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (f : X → Y) {x x′} → x ≡ x′ → f x ≡ f x′
f & refl = refl

infixl 8 _⊗_
_⊗_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {f g : X → Y} {x x′} → f ≡ g → x ≡ x′ → f x ≡ g x′
refl ⊗ refl = refl

-- NOTE: literals for naturals
instance
  literalNat : Number Nat
  literalNat = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ n → n
    }

-- NOTE: literals for bounded naturals, and for standalone term variables
instance
  literalFin : ∀ {n} → Number (Fin n)
  literalFin {n} = record
    { Constraint = λ m → True (m Nat.<? n)
    ; fromNat    = λ m {{p}} → (Fin.# m) {n} {p}
    }


----------------------------------------------------------------------------------------------------

-- 0.1. heterogeneous equality
-- TODO: uniform notation with _⁻¹ and _⋮_?

infix 4 _≅_
data _≅_ {𝓍} {X : Set 𝓍} (x : X) : ∀ {𝓎} {Y : Set 𝓎} → Y → Set 𝓍 where
   refl : x ≅ x

infix 9 _⁻¹′
_⁻¹′ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {x : X} {y : Y} → x ≅ y → y ≅ x
refl ⁻¹′ = refl

infixr 4 _⋮′_
_⋮′_ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : Set 𝓏} {x : X} {y : Y} {z : Z} →
         x ≅ y → y ≅ z → x ≅ z
refl ⋮′ refl = refl

infixl 9 _&′_
_&′_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} (f : ∀ x → Y x) {x x′} →
         x ≅ x′ → f x ≅ f x′
f &′ refl = refl

-- TODO: fix this so that it actually works
infixl 8 _⊗′_
_⊗′_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} {f g : ∀ x → X → Y x} {x x′} →
         f ≅ g → x ≅ x′ → f x ≅ g x′
refl ⊗′ refl = refl

≅→≡ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} → x ≅ x′ → x ≡ x′
≅→≡ refl = refl

≡→≅ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} → x ≡ x′ → x ≅ x′
≡→≅ refl = refl

module ≅-Reasoning where
  infix  3 _∎
  infixr 2 _≅⟨⟩_ _≅⟨_⟩_ _≅⟨_⟩⁻¹_ _≡⟨_⟩_ _≡⟨_⟩⁻¹_
  infix  1 begin_

  begin_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {x : X} {y : Y} → x ≅ y → x ≅ y
  begin p = p

  _≅⟨⟩_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (x : X) {y : Y} → x ≅ y → x ≅ y
  x ≅⟨⟩ p = p

  _≅⟨_⟩_ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : Set 𝓏} (x : X) {y : Y} {z : Z} →
             x ≅ y → y ≅ z → x ≅ z
  x ≅⟨ p ⟩ q = p ⋮′ q

  _≅⟨_⟩⁻¹_ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : Set 𝓏} (x : X) {y : Y} {z : Z} →
               y ≅ x → y ≅ z → x ≅ z
  x ≅⟨ p ⟩⁻¹ q = p ⁻¹′ ⋮′ q

  _≡⟨_⟩_ : ∀ {𝓍 𝓏} {X : Set 𝓍} {Z : Set 𝓏} (x : X) {x′} {z : Z} →
             x ≡ x′ → x′ ≅ z → x ≅ z
  x ≡⟨ p ⟩ q = ≡→≅ p ⋮′ q

  _≡⟨_⟩⁻¹_ : ∀ {𝓍 𝓏} {X : Set 𝓍} {Z : Set 𝓏} (x : X) {x′} {z : Z} →
               x′ ≡ x → x′ ≅ z → x ≅ z
  x ≡⟨ p ⟩⁻¹ q = ≡→≅ (p ⁻¹) ⋮′ q

  _∎ : ∀ {𝓍} {X : Set 𝓍} (x : X) → x ≅ x
  x ∎ = refl


----------------------------------------------------------------------------------------------------

-- 0.2. leftist lists and vectors

infixl 4 _,_
data List {𝓍} (X : Set 𝓍) : Set 𝓍 where
  ∙   : List X
  _,_ : ∀ (ξ : List X) (x : X) → List X

data Vec {𝓍} (X : Set 𝓍) : Nat → Set 𝓍 where
  ∙   : Vec X zero
  _,_ : ∀ {n} (ξ : Vec X n) (x : X) → Vec X (suc n)

peek : ∀ {𝓍} {X : Set 𝓍} {n} → Fin n → Vec X n → X
peek zero    (ξ , x) = x
peek (suc i) (ξ , x) = peek i ξ

poke : ∀ {𝓍} {X : Set 𝓍} {n} → Fin n → X → Vec X n → Vec X n
poke zero    x (ξ , y) = ξ , x
poke (suc i) x (ξ , y) = poke i x ξ , y

for : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {n} → Vec X n → (X → Y) → Vec Y n
for ∙       f = ∙
for (ξ , x) f = for ξ f , f x

tab : ∀ {𝓍} {X : Set 𝓍} {n} → (Fin n → X) → Vec X n
tab {n = zero}  f = ∙
tab {n = suc n} f = tab (f ∘ suc) , f zero


----------------------------------------------------------------------------------------------------

-- 0.3. primitive recursive n-ary functions on naturals
-- Troelstra (1973) §1.3.4

mutual
  data Prim : Nat → Set where
    zero : Prim 0
    suc  : Prim 1
    proj : ∀ {n} (i : Fin n) → Prim n
    comp : ∀ {n m} (g : Prim m) (φ : Prim§ n m) → Prim n
    rec  : ∀ {n} (f : Prim n) (g : Prim (suc (suc n))) → Prim (suc n)

  Prim§ : Nat → Nat → Set
  Prim§ n m = Vec (Prim n) m

Nat§ : Nat → Set
Nat§ n = Vec Nat n

Fun : Nat → Set
Fun n = Nat§ n → Nat

Fun§ : Nat → Nat → Set
Fun§ n m = Vec (Fun n) m

#zero : Fun 0
#zero ∙ = zero

#suc : Fun 1
#suc (∙ , x) = suc x

#proj : ∀ {n} → Fin n → Fun n
#proj i ξ = peek i ξ

#comp : ∀ {n m} → Fun m → Fun§ n m → Fun n
#comp g φ ξ = g (for φ (_$ ξ))

#rec : ∀ {n} → Fun n → Fun (suc (suc n)) → Fun (suc n)
#rec f g (ξ , zero)  = f ξ
#rec f g (ξ , suc x) = g (ξ , x , #rec f g (ξ , x))

mutual
  ⟦_⟧ : ∀ {n} → Prim n → Fun n
  ⟦ zero ⟧     = #zero
  ⟦ suc ⟧      = #suc
  ⟦ proj i ⟧   = #proj i
  ⟦ comp g φ ⟧ = #comp ⟦ g ⟧ ⟦ φ ⟧§
  ⟦ rec f g ⟧  = #rec ⟦ f ⟧ ⟦ g ⟧

  ⟦_⟧§ : ∀ {n m} → Prim§ n m → Fun§ n m
  ⟦ ∙ ⟧§     = ∙
  ⟦ φ , f ⟧§ = ⟦ φ ⟧§ , ⟦ f ⟧


----------------------------------------------------------------------------------------------------

-- 0.4. some primitive recursive n-ary functions on naturals
-- Troelstra and van Dalen (1988) §1.3

ƒconst : ∀ {n} → Nat → Prim n
ƒconst zero    = comp zero ∙
ƒconst (suc x) = comp suc (∙ , ƒconst x)

ok-const : ∀ x → ⟦ ƒconst x ⟧ ∙ ≡ const {B = Nat§ 0} x ∙
ok-const zero    = refl
ok-const (suc x) = suc & ok-const x

-- NOTE: for reference only
-- _+_ : Nat → Nat → Nat
-- zero  + y = y
-- suc x + y = suc (x + y)

ƒadd : Prim 2
ƒadd = rec (proj 0)
         (comp suc (∙ , proj 0))

ok-add : ∀ x y → ⟦ ƒadd ⟧ (∙ , y , x) ≡ x Nat.+ y
ok-add zero    y = refl
ok-add (suc x) y = suc & ok-add x y

-- NOTE: for reference only
-- _*_ : Nat → Nat → Nat
-- zero  * y = zero
-- suc x * y = y + x * y

ƒmul : Prim 2
ƒmul = rec (ƒconst 0)
         (comp ƒadd (∙ , proj 0 , proj 2))

ok-mul : ∀ x y → ⟦ ƒmul ⟧ (∙ , y , x) ≡ x Nat.* y
ok-mul zero    y = refl
ok-mul (suc x) y = ((⟦ ƒadd ⟧ ∘ (_, y)) ∘ (∙ ,_)) & ok-mul x y
                 ⋮ ok-add y (x Nat.* y)

-- NOTE: for reference only
-- pred : Nat → Nat
-- pred x = x ∸ 1

ƒpred : Prim 1
ƒpred = rec (ƒconst 0)
          (proj 1)

ok-pred : ∀ x → ⟦ ƒpred ⟧ (∙ , x) ≡ Nat.pred x
ok-pred zero    = refl
ok-pred (suc x) = refl

-- TODO: subtraction

-- NOTE: for reference only
-- _∸_ : Nat → Nat → Nat
-- x     ∸ zero  = x
-- zero  ∸ suc y = zero
-- suc x ∸ suc y = x ∸ y

-- NOTE: for reference only
-- _-_ : Nat → Nat → Nat
-- x - zero  = x
-- x - suc y = pred (x - y)


----------------------------------------------------------------------------------------------------

-- 0.5. untyped de Bruijn indices and order-preserving embeddings for term variables

-- NOTE: for reference only
-- data Fin : Nat → Set where
--   zero : Fin (suc n)
--   suc  : ∀ (i : Fin n) → Fin (suc n)

infix 3 _≤_
data _≤_ : Nat → Nat → Set where
  stop  : zero ≤ zero
  wk≤   : ∀ {k k′} (η : k ≤ k′) → k ≤ suc k′
  lift≤ : ∀ {k k′} (η : k ≤ k′) → suc k ≤ suc k′

id≤ : ∀ {k} → k ≤ k
id≤ {k = zero}  = stop
id≤ {k = suc k} = lift≤ id≤

infixr 9 _∘≤_
_∘≤_ : ∀ {k k′ k″} → k′ ≤ k″ → k ≤ k′ → k ≤ k″
stop     ∘≤ η       = η
wk≤ η′   ∘≤ η       = wk≤ (η′ ∘≤ η)
lift≤ η′ ∘≤ wk≤ η   = wk≤ (η′ ∘≤ η)
lift≤ η′ ∘≤ lift≤ η = lift≤ (η′ ∘≤ η)

lid≤ : ∀ {k k′} (η : k ≤ k′) → id≤ ∘≤ η ≡ η
lid≤ stop      = refl
lid≤ (wk≤ η)   = wk≤ & lid≤ η
lid≤ (lift≤ η) = lift≤ & lid≤ η

rid≤ : ∀ {k k′} (η : k ≤ k′) → η ∘≤ id≤ ≡ η
rid≤ stop      = refl
rid≤ (wk≤ η)   = wk≤ & rid≤ η
rid≤ (lift≤ η) = lift≤ & rid≤ η

ass≤ : ∀ {k k′ k″ k‴} (η″ : k″ ≤ k‴) (η′ : k′ ≤ k″) (η : k ≤ k′) →
         η″ ∘≤ (η′ ∘≤ η) ≡ (η″ ∘≤ η′) ∘≤ η
ass≤ stop       η′         η         = refl
ass≤ (wk≤ η″)   η′         η         = wk≤ & ass≤ η″ η′ η
ass≤ (lift≤ η″) (wk≤ η′)   η         = wk≤ & ass≤ η″ η′ η
ass≤ (lift≤ η″) (lift≤ η′) (wk≤ η)   = wk≤ & ass≤ η″ η′ η
ass≤ (lift≤ η″) (lift≤ η′) (lift≤ η) = lift≤ & ass≤ η″ η′ η

renFin : ∀ {k k′} → k ≤ k′ → Fin k → Fin k′
renFin stop      i       = i
renFin (wk≤ η)   i       = suc (renFin η i)
renFin (lift≤ η) zero    = zero
renFin (lift≤ η) (suc i) = renFin (wk≤ η) i

wkFin : ∀ {k} → Fin k → Fin (suc k)
wkFin i = renFin (wk≤ id≤) i

idrenFin : ∀ {k} (i : Fin k) → renFin id≤ i ≡ i
idrenFin zero    = refl
idrenFin (suc i) = suc & idrenFin i

comprenFin : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (i : Fin k) →
               renFin (η′ ∘≤ η) i ≡ (renFin η′ ∘ renFin η) i
comprenFin stop       η         i       = refl
comprenFin (wk≤ η′)   η         i       = suc & comprenFin η′ η i
comprenFin (lift≤ η′) (wk≤ η)   i       = suc & comprenFin η′ η i
comprenFin (lift≤ η′) (lift≤ η) zero    = refl
comprenFin (lift≤ η′) (lift≤ η) (suc i) = suc & comprenFin η′ η i


----------------------------------------------------------------------------------------------------

-- 0.6. typed de Bruijn indices and order-preserving embeddings for derivation variables

module _ {𝓍} {X : Set 𝓍} where
  infix 3 _∋_
  data _∋_ : List X → X → Set 𝓍 where
    zero : ∀ {Γ A} → Γ , A ∋ A
    suc  : ∀ {Γ A C} (i : Γ ∋ A) → Γ , C ∋ A

  -- NOTE: literals for standalone derivation variables
  infix 3 _∋⟨_⟩_
  data _∋⟨_⟩_ : List X → Nat → X → Set 𝓍 where
    instance
      zero : ∀ {Γ A} → Γ , A ∋⟨ zero ⟩ A
      suc  : ∀ {Γ m A C} {{i : Γ ∋⟨ m ⟩ A}} → Γ , C ∋⟨ suc m ⟩ A

  ∋#→∋ : ∀ {Γ m A} → Γ ∋⟨ m ⟩ A → Γ ∋ A
  ∋#→∋ zero        = zero
  ∋#→∋ (suc {{i}}) = suc (∋#→∋ i)

  instance
    number∋ : ∀ {Γ A} → Number (Γ ∋ A)
    number∋ {Γ} {A} = record
      { Constraint = λ m → Γ ∋⟨ m ⟩ A
      ; fromNat    = λ m {{p}} → ∋#→∋ p
      }

  infix 3 _⊑_
  data _⊑_ : List X → List X → Set 𝓍 where
    stop  : ∙ ⊑ ∙
    wk⊑   : ∀ {Γ Γ′ C} (η : Γ ⊑ Γ′) → Γ ⊑ Γ′ , C
    lift⊑ : ∀ {Γ Γ′ C} (η : Γ ⊑ Γ′) → Γ , C ⊑ Γ′ , C

  id⊑ : ∀ {Γ} → Γ ⊑ Γ
  id⊑ {Γ = ∙}     = stop
  id⊑ {Γ = Γ , A} = lift⊑ id⊑

  infixr 9 _∘⊑_
  _∘⊑_ : ∀ {Γ Γ′ Γ″} → Γ′ ⊑ Γ″ → Γ ⊑ Γ′ → Γ ⊑ Γ″
  stop     ∘⊑ η       = η
  wk⊑ η′   ∘⊑ η       = wk⊑ (η′ ∘⊑ η)
  lift⊑ η′ ∘⊑ wk⊑ η   = wk⊑ (η′ ∘⊑ η)
  lift⊑ η′ ∘⊑ lift⊑ η = lift⊑ (η′ ∘⊑ η)

  lid⊑ : ∀ {Γ Γ′} (η : Γ ⊑ Γ′) → id⊑ ∘⊑ η ≡ η
  lid⊑ stop      = refl
  lid⊑ (wk⊑ η)   = wk⊑ & lid⊑ η
  lid⊑ (lift⊑ η) = lift⊑ & lid⊑ η

  rid⊑ : ∀ {Γ Γ′} (η : Γ ⊑ Γ′) → η ∘⊑ id⊑ ≡ η
  rid⊑ stop      = refl
  rid⊑ (wk⊑ η)   = wk⊑ & rid⊑ η
  rid⊑ (lift⊑ η) = lift⊑ & rid⊑ η

  ass⊑ : ∀ {Γ Γ′ Γ″ Γ‴} (η″ : Γ″ ⊑ Γ‴) (η′ : Γ′ ⊑ Γ″) (η : Γ ⊑ Γ′) →
           η″ ∘⊑ (η′ ∘⊑ η) ≡ (η″ ∘⊑ η′) ∘⊑ η
  ass⊑ stop       η′         η         = refl
  ass⊑ (wk⊑ η″)   η′         η         = wk⊑ & ass⊑ η″ η′ η
  ass⊑ (lift⊑ η″) (wk⊑ η′)   η         = wk⊑ & ass⊑ η″ η′ η
  ass⊑ (lift⊑ η″) (lift⊑ η′) (wk⊑ η)   = wk⊑ & ass⊑ η″ η′ η
  ass⊑ (lift⊑ η″) (lift⊑ η′) (lift⊑ η) = lift⊑ & ass⊑ η″ η′ η

  ren∋ : ∀ {Γ Γ′ A} → Γ ⊑ Γ′ → Γ ∋ A → Γ′ ∋ A
  ren∋ stop      i       = i
  ren∋ (wk⊑ η)   i       = suc (ren∋ η i)
  ren∋ (lift⊑ η) zero    = zero
  ren∋ (lift⊑ η) (suc i) = suc (ren∋ η i)

  wk∋ : ∀ {Γ A C} → Γ ∋ A → Γ , C ∋ A
  wk∋ i = ren∋ (wk⊑ id⊑) i

  idren∋ : ∀ {Γ A} (i : Γ ∋ A) → ren∋ id⊑ i ≡ i
  idren∋ zero    = refl
  idren∋ (suc i) = suc & idren∋ i

  compren∋ : ∀ {Γ Γ′ Γ″ A} (η′ : Γ′ ⊑ Γ″) (η : Γ ⊑ Γ′) (i : Γ ∋ A) →
               ren∋ (η′ ∘⊑ η) i ≡ (ren∋ η′ ∘ ren∋ η) i
  compren∋ stop       η         i       = refl
  compren∋ (wk⊑ η′)   η         i       = suc & compren∋ η′ η i
  compren∋ (lift⊑ η′) (wk⊑ η)   i       = suc & compren∋ η′ η i
  compren∋ (lift⊑ η′) (lift⊑ η) zero    = refl
  compren∋ (lift⊑ η′) (lift⊑ η) (suc i) = suc & compren∋ η′ η i


----------------------------------------------------------------------------------------------------

-- 0.7. meta-level continuation/double negation monad/applicative/functor
-- TODO: laws?
-- TODO: delete?
-- module ContinuationMonad where
--   return : ∀ {𝓍} {A : Set 𝓍} → A → ¬ ¬ A
--   return x = λ k → k x
--
--   infixl 1 _>>=_
--   _>>=_ : ∀ {𝓍 𝓎} {A : Set 𝓍} {B : Set 𝓎} → ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B
--   mx >>= f = λ k → mx (λ x → f x k)
--
--   join : ∀ {𝓍} {A : Set 𝓍} → ¬ ¬ ¬ ¬ A → ¬ ¬ A
--   join mmx = mmx >>= λ mx → mx
--
--   infixl 4 _⊛_
--   _⊛_ : ∀ {𝓍 𝓎} {A : Set 𝓍} {B : Set 𝓎} → ¬ ¬ (A → B) → ¬ ¬ A → ¬ ¬ B
--   mf ⊛ mx = mf >>= λ f → mx >>= λ x → return (f x)
--
--   infixl 4 _<$>_
--   _<$>_ : ∀ {𝓍 𝓎} {A : Set 𝓍} {B : Set 𝓎} → (A → B) → ¬ ¬ A → ¬ ¬ B
--   f <$> mx = return f ⊛ mx
--
--   dnem : ∀ {𝓍} {A : Set 𝓍} → ¬ ¬ (A ∨ ¬ A)
--   dnem = λ k → k (right λ k′ → k (left k′))


----------------------------------------------------------------------------------------------------

-- 1.0. terms, indexed by number of term variables

mutual
  data Tm (k : Nat) : Set where
    ‵tvar : ∀ (i : Fin k) → Tm k -- i-th term variable
    ‵fun  : ∀ {n} (f : Prim n) (τ : Tm§ k n) → Tm k

  Tm§ : Nat → Nat → Set
  Tm§ k n = Vec (Tm k) n

-- NOTE: literals for term variables in terms
-- TODO: delete?
-- instance
--   numberTm : ∀ {k} → Number (Tm k)
--   numberTm {k} = record
--     { Constraint = λ m → True (m Nat.<? k)
--     ; fromNat    = λ m {{p}} → ‵var ((Fin.# m) {k} {p})
--     }

𝟘 : ∀ {k} → Tm k
𝟘 = ‵fun zero ∙

𝕊 : ∀ {k} → Tm k → Tm k
𝕊 t = ‵fun suc (∙ , t)

-- NOTE: literals for naturals encoded as object-level primitive recursive functions
-- TODO: delete?
-- natTm : ∀ {k} → Nat → Tm k
-- natTm zero    = 𝟘
-- natTm (suc m) = 𝕊 (natTm m)
--
-- instance
--   numberTm : ∀ {k} → Number (Tm k)
--   numberTm {k} = record
--     { Constraint = λ _ → ⊤
--     ; fromNat    = λ m → natTm m
--     }


----------------------------------------------------------------------------------------------------

-- 1.1. terms: renaming

mutual
  renTm : ∀ {k k′} → k ≤ k′ → Tm k → Tm k′
  renTm η (‵tvar i)  = ‵tvar (renFin η i)
  renTm η (‵fun f τ) = ‵fun f (renTm§ η τ)

  renTm§ : ∀ {k k′ n} → k ≤ k′ → Tm§ k n → Tm§ k′ n
  renTm§ η ∙       = ∙
  renTm§ η (τ , t) = renTm§ η τ , renTm η t


----------------------------------------------------------------------------------------------------

-- 1.2. terms: generic lemmas from RenKit

wkTm : ∀ {k} → Tm k → Tm (suc k)
wkTm t = renTm (wk≤ id≤) t

wkTm§ : ∀ {k n} → Tm§ k n → Tm§ (suc k) n
wkTm§ τ = renTm§ (wk≤ id≤) τ

liftTm§ : ∀ {k n} → Tm§ k n → Tm§ (suc k) (suc n)
liftTm§ τ = wkTm§ τ , ‵tvar zero

varTm§ : ∀ {k k′} → k ≤ k′ → Tm§ k′ k
varTm§ stop      = ∙
varTm§ (wk≤ η)   = wkTm§ (varTm§ η)
varTm§ (lift≤ η) = liftTm§ (varTm§ η)

-- TODO: check if changing this affects anything
idTm§ : ∀ {k} → Tm§ k k
-- idTm§ {k = zero}  = ∙
-- idTm§ {k = suc k} = liftTm§ idTm§
idTm§ = varTm§ id≤

subFin : ∀ {k m} → Tm§ m k → Fin k → Tm m
subFin (σ , s) zero    = s
subFin (σ , s) (suc i) = subFin σ i


----------------------------------------------------------------------------------------------------

-- 1.3. terms: substitution

mutual
  subTm : ∀ {k m} → Tm§ m k → Tm k → Tm m
  subTm σ (‵tvar i)  = subFin σ i
  subTm σ (‵fun f τ) = ‵fun f (subTm§ σ τ)

  subTm§ : ∀ {k m n} → Tm§ m k → Tm§ k n → Tm§ m n
  subTm§ σ ∙       = ∙
  subTm§ σ (τ , t) = subTm§ σ τ , subTm σ t


----------------------------------------------------------------------------------------------------

-- 1.4. terms: generic lemmas from SubKit

_[_/0]Tm : ∀ {k} → Tm (suc k) → Tm k → Tm k
t [ s /0]Tm = subTm (idTm§ , s) t

_[_/1]Tm : ∀ {k} → Tm (suc (suc k)) → Tm (suc k) → Tm (suc k)
t [ s /1]Tm = subTm (wkTm§ idTm§ , s , ‵tvar zero) t

getTm§ : ∀ {k n n′} → n ≤ n′ → Tm§ k n′ → Tm§ k n
getTm§ stop      τ       = τ
getTm§ (wk≤ η)   (τ , t) = getTm§ η τ
getTm§ (lift≤ η) (τ , t) = getTm§ η τ , t


----------------------------------------------------------------------------------------------------

-- 1.5. terms: fundamental renaming lemmas

mutual
  lidrenTm : ∀ {k} (t : Tm k) → renTm id≤ t ≡ t
  lidrenTm (‵tvar i)  = ‵tvar & idrenFin i
  lidrenTm (‵fun f τ) = ‵fun f & lidrenTm§ τ

  lidrenTm§ : ∀ {k n} (τ : Tm§ k n) → renTm§ id≤ τ ≡ τ
  lidrenTm§ ∙       = refl
  lidrenTm§ (τ , t) = _,_ & lidrenTm§ τ ⊗ lidrenTm t

mutual
  comprenTm : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (t : Tm k) →
                renTm (η′ ∘≤ η) t ≡ (renTm η′ ∘ renTm η) t
  comprenTm η′ η (‵tvar i)  = ‵tvar & comprenFin η′ η i
  comprenTm η′ η (‵fun f τ) = ‵fun f & comprenTm§ η′ η τ

  comprenTm§ : ∀ {k k′ k″ n} (η′ : k′ ≤ k″) (η : k ≤ k′) (τ : Tm§ k n) →
                 renTm§ (η′ ∘≤ η) τ ≡ (renTm§ η′ ∘ renTm§ η) τ
  comprenTm§ η′ η ∙       = refl
  comprenTm§ η′ η (τ , t) = _,_ & comprenTm§ η′ η τ ⊗ comprenTm η′ η t

ridrenTm : ∀ {k k′} (η : k ≤ k′) (i : Fin k) → (renTm η ∘ ‵tvar) i ≡ (‵tvar ∘ renFin η) i
ridrenTm η i = refl

ridsubTm : ∀ {k m} (σ : Tm§ m k) (i : Fin k) → (subTm σ ∘ ‵tvar) i ≡ subFin σ i
ridsubTm σ i = refl


----------------------------------------------------------------------------------------------------

-- 1.6. terms: generic lemmas from RenSubKit1

eqwkrenTm : ∀ {k k′} (η : k ≤ k′) (t : Tm k) →
              (renTm (lift≤ η) ∘ wkTm) t ≡ (wkTm ∘ renTm η) t
eqwkrenTm η t = comprenTm (lift≤ η) (wk≤ id≤) t ⁻¹
              ⋮ (flip renTm t ∘ wk≤)
                  & ( rid≤ η
                    ⋮ lid≤ η ⁻¹
                    )
              ⋮ comprenTm (wk≤ id≤) η t

eqwkrenTm§ : ∀ {k k′ n} (η : k ≤ k′) (τ : Tm§ k n) →
               (renTm§ (lift≤ η) ∘ wkTm§) τ ≡ (wkTm§ ∘ renTm§ η) τ
eqwkrenTm§ η ∙       = refl
eqwkrenTm§ η (τ , t) = _,_ & eqwkrenTm§ η τ ⊗ eqwkrenTm η t

eqliftrenTm§ : ∀ {k k′ n} (η : k ≤ k′) (τ : Tm§ k n) →
                 (renTm§ (lift≤ η) ∘ liftTm§) τ ≡ (liftTm§ ∘ renTm§ η) τ
eqliftrenTm§ η τ = _,_ & eqwkrenTm§ η τ ⊗ ridrenTm (lift≤ η) zero

ridrenTm§ : ∀ {k k′} (η : k ≤ k′) → renTm§ η idTm§ ≡ varTm§ η
ridrenTm§ stop      = refl
ridrenTm§ (wk≤ η)   = (flip renTm§ idTm§ ∘ wk≤) & lid≤ η ⁻¹
                    ⋮ comprenTm§ (wk≤ id≤) η idTm§
                    ⋮ wkTm§ & ridrenTm§ η
ridrenTm§ (lift≤ η) = _,_
                        & ( eqwkrenTm§ η idTm§
                          ⋮ wkTm§ & ridrenTm§ η
                          )
                        ⊗ ridrenTm (lift≤ η) zero

eqrensubFin : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (i : Fin k) →
                subFin (renTm§ η σ) i ≡ (renTm η ∘ subFin σ) i
eqrensubFin η (σ , s) zero    = refl
eqrensubFin η (σ , s) (suc i) = eqrensubFin η σ i

eqsubrenFin : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (i : Fin k) →
                subFin (getTm§ η σ) i ≡ (subFin σ ∘ renFin η) i
eqsubrenFin ∙       stop      i       = refl
eqsubrenFin (σ , s) (wk≤ η)   i       = eqsubrenFin σ η i
eqsubrenFin (σ , s) (lift≤ η) zero    = refl
eqsubrenFin (σ , s) (lift≤ η) (suc i) = eqsubrenFin σ η i

idsubFin : ∀ {k} (i : Fin k) → subFin idTm§ i ≡ ‵tvar i
idsubFin zero    = refl
idsubFin (suc i) = eqrensubFin (wk≤ id≤) idTm§ i
                 ⋮ wkTm & idsubFin i
                 ⋮ ridrenTm (wk≤ id≤) i
                 ⋮ (‵tvar ∘ suc) & idrenFin i

compsubFin : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (i : Fin k) →
               subFin (subTm§ σ′ σ) i ≡ (subTm σ′ ∘ subFin σ) i
compsubFin σ′ (σ , s) zero    = refl
compsubFin σ′ (σ , s) (suc i) = compsubFin σ′ σ i

lidgetTm§ : ∀ {k n} (τ : Tm§ k n) → getTm§ id≤ τ ≡ τ
lidgetTm§ ∙       = refl
lidgetTm§ (τ , t) = (_, t) & lidgetTm§ τ

compgetTm§ : ∀ {k n n′ n″} (η : n ≤ n′) (η′ : n′ ≤ n″) (τ : Tm§ k n″) →
               getTm§ (η′ ∘≤ η) τ ≡ (getTm§ η ∘ getTm§ η′) τ
compgetTm§ η         stop       ∙       = refl
compgetTm§ η         (wk≤ η′)   (τ , t) = compgetTm§ η η′ τ
compgetTm§ (wk≤ η)   (lift≤ η′) (τ , t) = compgetTm§ η η′ τ
compgetTm§ (lift≤ η) (lift≤ η′) (τ , t) = (_, t) & compgetTm§ η η′ τ

eqrengetTm§ : ∀ {k k′ n n′} (η : k ≤ k′) (η′ : n ≤ n′) (τ : Tm§ k n′) →
                (getTm§ η′ ∘ renTm§ η) τ ≡ (renTm§ η ∘ getTm§ η′) τ
eqrengetTm§ η stop       ∙       = refl
eqrengetTm§ η (wk≤ η′)   (τ , t) = eqrengetTm§ η η′ τ
eqrengetTm§ η (lift≤ η′) (τ , t) = (_, renTm η t) & eqrengetTm§ η η′ τ

eqwkgetTm§ : ∀ {k n n′} (η : n ≤ n′) (τ : Tm§ k n′) →
               (getTm§ (wk≤ η) ∘ liftTm§) τ ≡ (wkTm§ ∘ getTm§ η) τ
eqwkgetTm§ η τ = eqrengetTm§ (wk≤ id≤) η τ

eqliftgetTm§ : ∀ {k n n′} (η : n ≤ n′) (τ : Tm§ k n′) →
                 (getTm§ (lift≤ η) ∘ liftTm§) τ ≡ (liftTm§ ∘ getTm§ η) τ
eqliftgetTm§ η τ = (_, ‵tvar zero) & eqwkgetTm§ η τ

ridgetTm§ : ∀ {k k′} (η : k ≤ k′) → getTm§ η idTm§ ≡ varTm§ η
ridgetTm§ stop      = refl
ridgetTm§ (wk≤ η)   = eqrengetTm§ (wk≤ id≤) η idTm§
                    ⋮ wkTm§ & ridgetTm§ η
ridgetTm§ (lift≤ η) = (_, ‵tvar zero)
                        & ( eqrengetTm§ (wk≤ id≤) η idTm§
                          ⋮ wkTm§ & ridgetTm§ η
                          )


----------------------------------------------------------------------------------------------------

-- 1.7. terms: fundamental substitution lemmas

mutual
  eqrensubTm : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (t : Tm k) →
                 subTm (renTm§ η σ) t ≡ (renTm η ∘ subTm σ) t
  eqrensubTm η σ (‵tvar i)  = eqrensubFin η σ i
  eqrensubTm η σ (‵fun f τ) = ‵fun f & eqrensubTm§ η σ τ

  eqrensubTm§ : ∀ {k m m′ n} (η : m ≤ m′) (σ : Tm§ m k) (τ : Tm§ k n) →
                  subTm§ (renTm§ η σ) τ ≡ (renTm§ η ∘ subTm§ σ) τ
  eqrensubTm§ η σ ∙       = refl
  eqrensubTm§ η σ (τ , t) = _,_ & eqrensubTm§ η σ τ ⊗ eqrensubTm η σ t

mutual
  eqsubrenTm : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (t : Tm k) →
                 subTm (getTm§ η σ) t ≡ (subTm σ ∘ renTm η) t
  eqsubrenTm σ η (‵tvar i)  = eqsubrenFin σ η i
  eqsubrenTm σ η (‵fun f τ) = ‵fun f & eqsubrenTm§ σ η τ

  eqsubrenTm§ : ∀ {k k′ m n} (σ : Tm§ m k′) (η : k ≤ k′) (τ : Tm§ k n) →
                  subTm§ (getTm§ η σ) τ ≡ (subTm§ σ ∘ renTm§ η) τ
  eqsubrenTm§ σ η ∙       = refl
  eqsubrenTm§ σ η (τ , t) = _,_ & eqsubrenTm§ σ η τ ⊗ eqsubrenTm σ η t

mutual
  lidsubTm : ∀ {k} (t : Tm k) → subTm idTm§ t ≡ t
  lidsubTm (‵tvar i)  = idsubFin i
  lidsubTm (‵fun f τ) = ‵fun f & lidsubTm§ τ

  lidsubTm§ : ∀ {k n} (τ : Tm§ k n) → subTm§ idTm§ τ ≡ τ
  lidsubTm§ ∙       = refl
  lidsubTm§ (τ , t) = _,_ & lidsubTm§ τ ⊗ lidsubTm t


----------------------------------------------------------------------------------------------------

-- 1.8. terms: generic lemmas from RenSubKit2

eqsubTm : ∀ {k m} (σ : Tm§ m k) (s : Tm m) (t : Tm k) →
            (subTm (σ , s) ∘ wkTm) t ≡ subTm σ t
eqsubTm σ s t = eqsubrenTm (σ , s) (wk≤ id≤) t ⁻¹
              ⋮ flip subTm t & lidgetTm§ σ

eqsubTm§ : ∀ {k m n} (σ : Tm§ m k) (s : Tm m) (τ : Tm§ k n) →
             (subTm§ (σ , s) ∘ wkTm§) τ ≡ subTm§ σ τ
eqsubTm§ σ s ∙       = refl
eqsubTm§ σ s (τ , t) = _,_ & eqsubTm§ σ s τ ⊗ eqsubTm σ s t

eqwksubTm : ∀ {k m} (σ : Tm§ m k) (t : Tm k) →
              (subTm (liftTm§ σ) ∘ wkTm) t ≡ (wkTm ∘ subTm σ) t
eqwksubTm σ t = eqsubrenTm (liftTm§ σ) (wk≤ id≤) t ⁻¹
              ⋮ flip subTm t
                  & ( eqwkgetTm§ id≤ σ
                    ⋮ wkTm§ & lidgetTm§ σ
                    )
              ⋮ eqrensubTm (wk≤ id≤) σ t

eqwksubTm§ : ∀ {k m n} (σ : Tm§ m k) (τ : Tm§ k n) →
               (subTm§ (liftTm§ σ) ∘ wkTm§) τ ≡ (wkTm§ ∘ subTm§ σ) τ
eqwksubTm§ σ ∙       = refl
eqwksubTm§ σ (τ , t) = _,_ & eqwksubTm§ σ τ ⊗ eqwksubTm σ t

eqliftsubTm§ : ∀ {k m n} (σ : Tm§ m k) (τ : Tm§ k n) →
                 (subTm§ (liftTm§ σ) ∘ liftTm§) τ ≡ (liftTm§ ∘ subTm§ σ) τ
eqliftsubTm§ σ τ = _,_ & eqwksubTm§ σ τ ⊗ ridsubTm (liftTm§ σ) zero

ridsubTm§ : ∀ {k m} (σ : Tm§ m k) → subTm§ σ idTm§ ≡ σ
ridsubTm§ ∙       = refl
ridsubTm§ (σ , s) = _,_
                      & ( eqsubTm§ σ s idTm§
                        ⋮ ridsubTm§ σ
                        )
                      ⊗ ridsubTm (σ , s) zero


----------------------------------------------------------------------------------------------------

-- 1.9. terms: more fundamental substitution lemmas

mutual
  compsubTm : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (t : Tm k) →
                subTm (subTm§ σ′ σ) t ≡ (subTm σ′ ∘ subTm σ) t
  compsubTm σ′ σ (‵tvar i)  = compsubFin σ′ σ i
  compsubTm σ′ σ (‵fun f τ) = ‵fun f & asssubTm§ σ′ σ τ

  asssubTm§ : ∀ {k m m′ n} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (τ : Tm§ k n) →
                subTm§ (subTm§ σ′ σ) τ ≡ (subTm§ σ′ ∘ subTm§ σ) τ
  asssubTm§ σ′ σ ∙       = refl
  asssubTm§ σ′ σ (τ , t) = _,_ & asssubTm§ σ′ σ τ ⊗ compsubTm σ′ σ t


----------------------------------------------------------------------------------------------------

-- 1.10. terms: generic lemmas from RenSubKit3

eqrencut0Tm : ∀ {k k′} (η : k ≤ k′) (t : Tm (suc k)) (s : Tm k) →
                renTm (lift≤ η) t [ renTm η s /0]Tm ≡ renTm η (t [ s /0]Tm)
eqrencut0Tm η t s = eqsubrenTm (idTm§ , renTm η s) (lift≤ η) t ⁻¹
                  ⋮ (flip subTm t ∘ (_, renTm η s))
                      & ( ridgetTm§ η
                        ⋮ ridrenTm§ η ⁻¹
                        )
                  ⋮ eqrensubTm η (idTm§ , s) t

eqsubcut0Tm : ∀ {k m} (σ : Tm§ m k) (t : Tm (suc k)) (s : Tm k) →
                subTm (liftTm§ σ) t [ subTm σ s /0]Tm ≡ subTm σ (t [ s /0]Tm)
eqsubcut0Tm σ t s = compsubTm (idTm§ , subTm σ s) (liftTm§ σ) t ⁻¹
                  ⋮ flip subTm t
                      & ( _,_
                            & ( eqsubrenTm§ (idTm§ , subTm σ s) (wk≤ id≤) σ ⁻¹
                              ⋮ flip subTm§ σ & lidgetTm§ idTm§
                              ⋮ lidsubTm§ σ
                              ⋮ ridsubTm§ σ ⁻¹
                              )
                            ⊗ ridsubTm (idTm§ , subTm σ s) zero
                        )
                  ⋮ compsubTm σ (idTm§ , s) t


----------------------------------------------------------------------------------------------------

-- 2.0. formulas, indexed by number of term variables

infix  19 _‵=_
infix  18 ‵∀_
infix  17 ‵∃_
infixl 16 _‵∧_
infixl 15 _‵∨_
infixr 14 _‵⊃_
data Fm (k : Nat) : Set where
  _‵⊃_ : ∀ (A B : Fm k) → Fm k
  _‵∧_ : ∀ (A B : Fm k) → Fm k
  _‵∨_ : ∀ (A B : Fm k) → Fm k
  ‵∀_  : ∀ (A : Fm (suc k)) → Fm k
  ‵∃_  : ∀ (A : Fm (suc k)) → Fm k
  ‵⊥  : Fm k
  _‵=_ : ∀ (t u : Tm k) → Fm k

Fm§ : Nat → Set
Fm§ k = List (Fm k)

infixr 13 _‵⫗_
_‵⫗_ : ∀ {k} → Fm k → Fm k → Fm k
A ‵⫗ B = (A ‵⊃ B) ‵∧ (B ‵⊃ A)

‵¬_ : ∀ {k} → Fm k → Fm k
‵¬ A = A ‵⊃ ‵⊥

infix 19 _‵≠_
_‵≠_ : ∀ {k} → Tm k → Tm k → Fm k
t ‵≠ u = ‵¬ (t ‵= u)


----------------------------------------------------------------------------------------------------

-- 2.1. formulas: renaming

renFm : ∀ {k k′} → k ≤ k′ → Fm k → Fm k′
renFm η (A ‵⊃ B) = renFm η A ‵⊃ renFm η B
renFm η (A ‵∧ B) = renFm η A ‵∧ renFm η B
renFm η (A ‵∨ B) = renFm η A ‵∨ renFm η B
renFm η (‵∀ A)   = ‵∀ renFm (lift≤ η) A
renFm η (‵∃ A)   = ‵∃ renFm (lift≤ η) A
renFm η ‵⊥      = ‵⊥
renFm η (t ‵= u) = renTm η t ‵= renTm η u

renFm§ : ∀ {k k′} → k ≤ k′ → Fm§ k → Fm§ k′
renFm§ η ∙       = ∙
renFm§ η (Γ , A) = renFm§ η Γ , renFm η A


----------------------------------------------------------------------------------------------------

-- 2.2. formulas: generic lemmas from RenKit

wkFm : ∀ {k} → Fm k → Fm (suc k)
wkFm A = renFm (wk≤ id≤) A

wkFm§ : ∀ {k} → Fm§ k → Fm§ (suc k)
wkFm§ Γ = renFm§ (wk≤ id≤) Γ


----------------------------------------------------------------------------------------------------

-- 2.3. formulas: substitution

subFm : ∀ {k m} → Tm§ m k → Fm k → Fm m
subFm σ (A ‵⊃ B) = subFm σ A ‵⊃ subFm σ B
subFm σ (A ‵∧ B) = subFm σ A ‵∧ subFm σ B
subFm σ (A ‵∨ B) = subFm σ A ‵∨ subFm σ B
subFm σ (‵∀ A)   = ‵∀ subFm (liftTm§ σ) A
subFm σ (‵∃ A)   = ‵∃ subFm (liftTm§ σ) A
subFm σ ‵⊥      = ‵⊥
subFm σ (t ‵= u) = subTm σ t ‵= subTm σ u

subFm§ : ∀ {k m} → Tm§ m k → Fm§ k → Fm§ m
subFm§ σ ∙       = ∙
subFm§ σ (Γ , A) = subFm§ σ Γ , subFm σ A


----------------------------------------------------------------------------------------------------

-- 2.4. formulas: generic lemmas from SubKit

_[_/0]Fm : ∀ {k} → Fm (suc k) → Tm k → Fm k
A [ s /0]Fm = subFm (idTm§ , s) A

_[_/1]Fm : ∀ {k} → Fm (suc (suc k)) → Tm (suc k) → Fm (suc k)
A [ s /1]Fm = subFm (wkTm§ idTm§ , s , ‵tvar zero) A


----------------------------------------------------------------------------------------------------

-- 2.5. formulas: fundamental renaming lemmas

lidrenFm : ∀ {k} (A : Fm k) → renFm id≤ A ≡ A
lidrenFm (A ‵⊃ B) = _‵⊃_ & lidrenFm A ⊗ lidrenFm B
lidrenFm (A ‵∧ B) = _‵∧_ & lidrenFm A ⊗ lidrenFm B
lidrenFm (A ‵∨ B) = _‵∨_ & lidrenFm A ⊗ lidrenFm B
lidrenFm (‵∀ A)   = ‵∀_ & lidrenFm A
lidrenFm (‵∃ A)   = ‵∃_ & lidrenFm A
lidrenFm ‵⊥      = refl
lidrenFm (t ‵= u) = _‵=_ & lidrenTm t ⊗ lidrenTm u

comprenFm : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (A : Fm k) →
              renFm (η′ ∘≤ η) A ≡ (renFm η′ ∘ renFm η) A
comprenFm η′ η (A ‵⊃ B) = _‵⊃_ & comprenFm η′ η A ⊗ comprenFm η′ η B
comprenFm η′ η (A ‵∧ B) = _‵∧_ & comprenFm η′ η A ⊗ comprenFm η′ η B
comprenFm η′ η (A ‵∨ B) = _‵∨_ & comprenFm η′ η A ⊗ comprenFm η′ η B
comprenFm η′ η (‵∀ A)   = ‵∀_ & comprenFm (lift≤ η′) (lift≤ η) A
comprenFm η′ η (‵∃ A)   = ‵∃_ & comprenFm (lift≤ η′) (lift≤ η) A
comprenFm η′ η ‵⊥      = refl
comprenFm η′ η (t ‵= u) = _‵=_ & comprenTm η′ η t ⊗ comprenTm η′ η u


----------------------------------------------------------------------------------------------------

-- 2.6. formulas: generic lemmas from RenSubKit1

lidrenFm§ : ∀ {k} (Γ : Fm§ k) → renFm§ id≤ Γ ≡ Γ
lidrenFm§ ∙       = refl
lidrenFm§ (Γ , A) = _,_ & lidrenFm§ Γ ⊗ lidrenFm A

comprenFm§ : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (Γ : Fm§ k) →
               renFm§ (η′ ∘≤ η) Γ ≡ (renFm§ η′ ∘ renFm§ η) Γ
comprenFm§ η′ η ∙       = refl
comprenFm§ η′ η (Γ , A) = _,_ & comprenFm§ η′ η Γ ⊗ comprenFm η′ η A

eqwkrenFm : ∀ {k k′} (η : k ≤ k′) (A : Fm k) →
              (renFm (lift≤ η) ∘ wkFm) A ≡ (wkFm ∘ renFm η) A
eqwkrenFm η A = comprenFm (lift≤ η) (wk≤ id≤) A ⁻¹
              ⋮ (flip renFm A ∘ wk≤)
                  & ( rid≤ η
                    ⋮ lid≤ η ⁻¹
                    )
              ⋮ comprenFm (wk≤ id≤) η A

eqwkrenFm§ : ∀ {k k′} (η : k ≤ k′) (Γ : Fm§ k) →
               (renFm§ (lift≤ η) ∘ wkFm§) Γ ≡ (wkFm§ ∘ renFm§ η) Γ
eqwkrenFm§ η ∙       = refl
eqwkrenFm§ η (Γ , A) = _,_ & eqwkrenFm§ η Γ ⊗ eqwkrenFm η A


----------------------------------------------------------------------------------------------------

-- 2.7. formulas: fundamental substitution lemmas

mutual
  eqrensubFm : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (A : Fm k) →
                 subFm (renTm§ η σ) A ≡ (renFm η ∘ subFm σ) A
  eqrensubFm η σ (A ‵⊃ B) = _‵⊃_ & eqrensubFm η σ A ⊗ eqrensubFm η σ B
  eqrensubFm η σ (A ‵∧ B) = _‵∧_ & eqrensubFm η σ A ⊗ eqrensubFm η σ B
  eqrensubFm η σ (A ‵∨ B) = _‵∨_ & eqrensubFm η σ A ⊗ eqrensubFm η σ B
  eqrensubFm η σ (‵∀ A)   = ‵∀_ & eqrensubliftFm η σ A
  eqrensubFm η σ (‵∃ A)   = ‵∃_ & eqrensubliftFm η σ A
  eqrensubFm η σ ‵⊥      = refl
  eqrensubFm η σ (t ‵= u) = _‵=_ & eqrensubTm η σ t ⊗ eqrensubTm η σ u

  eqrensubliftFm : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (A : Fm (suc k)) →
                     subFm (liftTm§ (renTm§ η σ)) A ≡ (renFm (lift≤ η) ∘ subFm (liftTm§ σ)) A
  eqrensubliftFm η σ A = flip subFm A & eqliftrenTm§ η σ ⁻¹
                       ⋮ eqrensubFm (lift≤ η) (liftTm§ σ) A

mutual
  eqsubrenFm : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (A : Fm k) →
                 subFm (getTm§ η σ) A ≡ (subFm σ ∘ renFm η) A
  eqsubrenFm σ η (A ‵⊃ B) = _‵⊃_ & eqsubrenFm σ η A ⊗ eqsubrenFm σ η B
  eqsubrenFm σ η (A ‵∧ B) = _‵∧_ & eqsubrenFm σ η A ⊗ eqsubrenFm σ η B
  eqsubrenFm σ η (A ‵∨ B) = _‵∨_ & eqsubrenFm σ η A ⊗ eqsubrenFm σ η B
  eqsubrenFm σ η (‵∀ A)   = ‵∀_ & eqsubrenliftFm σ η A
  eqsubrenFm σ η (‵∃ A)   = ‵∃_ & eqsubrenliftFm σ η A
  eqsubrenFm σ η ‵⊥      = refl
  eqsubrenFm σ η (t ‵= u) = _‵=_ & eqsubrenTm σ η t ⊗ eqsubrenTm σ η u

  eqsubrenliftFm : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (A : Fm (suc k)) →
                     subFm (liftTm§ (getTm§ η σ)) A ≡ (subFm (liftTm§ σ) ∘ renFm (lift≤ η)) A
  eqsubrenliftFm σ η A = flip subFm A & eqliftgetTm§ η σ ⁻¹
                       ⋮ eqsubrenFm (liftTm§ σ) (lift≤ η) A

lidsubFm : ∀ {k} (A : Fm k) → subFm idTm§ A ≡ A
lidsubFm (A ‵⊃ B) = _‵⊃_ & lidsubFm A ⊗ lidsubFm B
lidsubFm (A ‵∧ B) = _‵∧_ & lidsubFm A ⊗ lidsubFm B
lidsubFm (A ‵∨ B) = _‵∨_ & lidsubFm A ⊗ lidsubFm B
lidsubFm (‵∀ A)   = ‵∀_ & lidsubFm A
lidsubFm (‵∃ A)   = ‵∃_ & lidsubFm A
lidsubFm ‵⊥      = refl
lidsubFm (t ‵= u) = _‵=_ & lidsubTm t ⊗ lidsubTm u


----------------------------------------------------------------------------------------------------

-- 2.8. formulas: generic lemmas from RenSubKit2

eqrensubFm§ : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (Γ : Fm§ k) →
                subFm§ (renTm§ η σ) Γ ≡ (renFm§ η ∘ subFm§ σ) Γ
eqrensubFm§ η σ ∙       = refl
eqrensubFm§ η σ (Γ , A) = _,_ & eqrensubFm§ η σ Γ ⊗ eqrensubFm η σ A

eqsubrenFm§ : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (Γ : Fm§ k) →
                subFm§ (getTm§ η σ) Γ ≡ (subFm§ σ ∘ renFm§ η) Γ
eqsubrenFm§ σ η ∙       = refl
eqsubrenFm§ σ η (Γ , A) = _,_ & eqsubrenFm§ σ η Γ ⊗ eqsubrenFm σ η A

eqsubFm : ∀ {k m} (σ : Tm§ m k) (s : Tm m) (A : Fm k) →
            (subFm (σ , s) ∘ wkFm) A ≡ subFm σ A
eqsubFm σ s A = eqsubrenFm (σ , s) (wk≤ id≤) A ⁻¹
              ⋮ flip subFm A & lidgetTm§ σ

eqsubFm§ : ∀ {k m} (σ : Tm§ m k) (s : Tm m) (Γ : Fm§ k) →
             (subFm§ (σ , s) ∘ wkFm§) Γ ≡ subFm§ σ Γ
eqsubFm§ σ s ∙       = refl
eqsubFm§ σ s (Γ , A) = _,_ & eqsubFm§ σ s Γ ⊗ eqsubFm σ s A

eqwksubFm : ∀ {k m} (σ : Tm§ m k) (A : Fm k) →
              (subFm (liftTm§ σ) ∘ wkFm) A ≡ (wkFm ∘ subFm σ) A
eqwksubFm σ A = eqsubrenFm (liftTm§ σ) (wk≤ id≤) A ⁻¹
              ⋮ flip subFm A
                  & ( eqwkgetTm§ id≤ σ
                    ⋮ wkTm§ & lidgetTm§ σ
                    )
              ⋮ eqrensubFm (wk≤ id≤) σ A

eqwksubFm§ : ∀ {k m} (σ : Tm§ m k) (Γ : Fm§ k) →
               (subFm§ (liftTm§ σ) ∘ wkFm§) Γ ≡ (wkFm§ ∘ subFm§ σ) Γ
eqwksubFm§ σ ∙       = refl
eqwksubFm§ σ (Γ , A) = _,_ & eqwksubFm§ σ Γ ⊗ eqwksubFm σ A


----------------------------------------------------------------------------------------------------

-- 2.9. formulas: more fundamental substitution lemmas

mutual
  compsubFm : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (A : Fm k) →
                subFm (subTm§ σ′ σ) A ≡ (subFm σ′ ∘ subFm σ) A
  compsubFm σ′ σ (A ‵⊃ B) = _‵⊃_ & compsubFm σ′ σ A ⊗ compsubFm σ′ σ B
  compsubFm σ′ σ (A ‵∧ B) = _‵∧_ & compsubFm σ′ σ A ⊗ compsubFm σ′ σ B
  compsubFm σ′ σ (A ‵∨ B) = _‵∨_ & compsubFm σ′ σ A ⊗ compsubFm σ′ σ B
  compsubFm σ′ σ (‵∀ A)   = ‵∀_ & compsubliftFm σ′ σ A
  compsubFm σ′ σ (‵∃ A)   = ‵∃_ & compsubliftFm σ′ σ A
  compsubFm σ′ σ ‵⊥      = refl
  compsubFm σ′ σ (t ‵= u) = _‵=_ & compsubTm σ′ σ t ⊗ compsubTm σ′ σ u

  compsubliftFm : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (A : Fm (suc k)) →
                    subFm (liftTm§ (subTm§ σ′ σ)) A ≡ (subFm (liftTm§ σ′) ∘ subFm (liftTm§ σ)) A
  compsubliftFm σ′ σ A = flip subFm A & eqliftsubTm§ σ′ σ ⁻¹
                       ⋮ compsubFm (liftTm§ σ′) (liftTm§ σ) A


----------------------------------------------------------------------------------------------------

-- 2.10. formulas: generic lemmas from RenSubKit3

asssubFm§ : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (Γ : Fm§ k) →
              subFm§ (subTm§ σ′ σ) Γ ≡ (subFm§ σ′ ∘ subFm§ σ) Γ
asssubFm§ σ′ σ ∙       = refl
asssubFm§ σ′ σ (Γ , A) = _,_ & asssubFm§ σ′ σ Γ ⊗ compsubFm σ′ σ A

idcutFm : ∀ {k} {A : Fm (suc k)} → renFm (lift≤ (wk≤ id≤)) A [ ‵tvar zero /0]Fm ≡ A
idcutFm {A = A} = eqsubrenFm (idTm§ , ‵tvar zero) (lift≤ (wk≤ id≤)) A ⁻¹
                ⋮ (flip subFm A ∘ (_, ‵tvar zero)) & lidgetTm§ (wkTm§ idTm§)
                ⋮ lidsubFm A

eqrencut0Fm : ∀ {k k′} (η : k ≤ k′) (A : Fm (suc k)) (s : Tm k) →
                renFm (lift≤ η) A [ renTm η s /0]Fm ≡ renFm η (A [ s /0]Fm)
eqrencut0Fm η A s = eqsubrenFm (idTm§ , renTm η s) (lift≤ η) A ⁻¹
                  ⋮ (flip subFm A ∘ (_, renTm η s))
                      & ( ridgetTm§ η
                        ⋮ ridrenTm§ η ⁻¹
                        )
                  ⋮ eqrensubFm η (idTm§ , s) A

eqrencut1Fm : ∀ {k k′} (η : k ≤ k′) (A : Fm (suc k)) (s : Tm (suc k)) →
                wkFm (renFm (lift≤ η) A) [ renTm (lift≤ η) s /1]Fm ≡
                  renFm (lift≤ η) (wkFm A [ s /1]Fm)
eqrencut1Fm η A s = subFm (wkTm§ idTm§ , renTm (lift≤ η) s , ‵tvar zero)
                      & eqwkrenFm (lift≤ η) A ⁻¹
                  ⋮ eqsubrenFm (wkTm§ idTm§ , renTm (lift≤ η) s , ‵tvar zero)
                      (lift≤ (lift≤ η)) (wkFm A) ⁻¹
                  ⋮ (flip subFm (wkFm A) ∘ (λ x → (x , renTm (lift≤ η) s , ‵tvar zero)))
                      & ( eqwkgetTm§ η idTm§
                        ⋮ wkTm§
                            & ( ridgetTm§ η
                              ⋮ ridrenTm§ η ⁻¹
                              )
                        ⋮ eqwkrenTm§ η idTm§ ⁻¹
                        )
                  ⋮ eqrensubFm (lift≤ η) (wkTm§ idTm§ , s , ‵tvar zero) (wkFm A)

eqsubcut0Fm : ∀ {k m} (σ : Tm§ m k) (A : Fm (suc k)) (s : Tm k) →
                subFm (liftTm§ σ) A [ subTm σ s /0]Fm ≡ subFm σ (A [ s /0]Fm)
eqsubcut0Fm σ A s = compsubFm (idTm§ , subTm σ s) (liftTm§ σ) A ⁻¹
                  ⋮ flip subFm A
                      & ( _,_
                            & ( eqsubrenTm§ (idTm§ , subTm σ s) (wk≤ id≤) σ ⁻¹
                              ⋮ flip subTm§ σ & lidgetTm§ idTm§
                              ⋮ lidsubTm§ σ
                              ⋮ ridsubTm§ σ ⁻¹
                              )
                            ⊗ ridsubTm (idTm§ , subTm σ s) zero
                        )
                  ⋮ compsubFm σ (idTm§ , s) A


----------------------------------------------------------------------------------------------------

-- 3.0. derivations, indexed by list of derivation variables

-- Heyting and Peano arithmetic
data Theory : Set where
  HA : Theory
  PA : Theory

infixr 4 _‵$_
infix  3 _/_⊢_
data _/_⊢_ {k} : Theory → Fm§ k → Fm k → Set where
  ‵var    : ∀ {Þ Γ A} (i : Γ ∋ A) → Þ / Γ ⊢ A -- i-th derivation variable
  ‵lam    : ∀ {Þ Γ A B} (d : Þ / Γ , A ⊢ B) → Þ / Γ ⊢ A ‵⊃ B
  _‵$_    : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A ‵⊃ B) (e : Þ / Γ ⊢ A) → Þ / Γ ⊢ B
  ‵pair   : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A) (e : Þ / Γ ⊢ B) → Þ / Γ ⊢ A ‵∧ B
  ‵fst    : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A ‵∧ B) → Þ / Γ ⊢ A
  ‵snd    : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A ‵∧ B) → Þ / Γ ⊢ B
  ‵left   : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A) → Þ / Γ ⊢ A ‵∨ B
  ‵right  : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ B) → Þ / Γ ⊢ A ‵∨ B
  ‵either : ∀ {Þ Γ A B C} (c : Þ / Γ ⊢ A ‵∨ B) (d : Þ / Γ , A ⊢ C) (e : Þ / Γ , B ⊢ C) →
              Þ / Γ ⊢ C

  --     A(x₀)
  -- --------------
  --   ∀y.A[y/xₒ]
  ‵all    : ∀ {Þ Γ Γ′ A} (p : Γ′ ≡ wkFm§ Γ) (d : Þ / Γ′ ⊢ A) → Þ / Γ ⊢ ‵∀ A

  --   ∀y.A[y/x₀]
  -- --------------
  --    A[t/x₀]
  ‵unall  : ∀ {Þ Γ A A′} (t : Tm k) (p : A [ t /0]Fm ≡ A′) (d : Þ / Γ ⊢ ‵∀ A) → Þ / Γ ⊢ A′

  --    A[t/x₀]
  -- --------------
  --   ∃y.A[y/x₀]
  ‵ex     : ∀ {Þ Γ A A′} (t : Tm k) (p : A [ t /0]Fm ≡ A′) (d : Þ / Γ ⊢ A′) → Þ / Γ ⊢ ‵∃ A

  --                 A(x₀)
  --                   ⋮
  --   ∃y.A[y/x₀]      C
  -- -----------------------
  --           C
  ‵letex  : ∀ {Þ Γ Γ′ A C C′} (p : Γ′ ≡ wkFm§ Γ) (q : C′ ≡ wkFm C) (d : Þ / Γ ⊢ ‵∃ A)
              (e : Þ / Γ′ , A ⊢ C′) → Þ / Γ ⊢ C

  -- explosion (ex falso quodlibet) as primitive in Heyting arithmetic
  ‵abort  : ∀ {Γ C} (d : HA / Γ ⊢ ‵⊥) → HA / Γ ⊢ C

  -- double negation elimination (reductio ad absurdum) as primitive in Peano arithmetic
  ‵magic  : ∀ {Γ A} (d : PA / Γ , ‵¬ A ⊢ ‵⊥) → PA / Γ ⊢ A

  ‵refl   : ∀ {Þ Γ t} → Þ / Γ ⊢ t ‵= t
  ‵sym    : ∀ {Þ Γ t u} (d : Þ / Γ ⊢ t ‵= u) → Þ / Γ ⊢ u ‵= t
  ‵trans  : ∀ {Þ Γ s t u} (d : Þ / Γ ⊢ s ‵= t) (e : Þ / Γ ⊢ t ‵= u) → Þ / Γ ⊢ s ‵= u

  ‵cong   : ∀ {Þ Γ n τ τ′ t u} (f : Prim n) (i : Fin n) (p : peek i τ ≡ t) (q : poke i u τ ≡ τ′)
              (d : Þ / Γ ⊢ t ‵= u) → Þ / Γ ⊢ ‵fun f τ ‵= ‵fun f τ′

  ‵dis    : ∀ {Þ Γ t} → Þ / Γ ⊢ 𝕊 t ‵≠ 𝟘

  ‵inj    : ∀ {Þ Γ t u} (d : Þ / Γ ⊢ 𝕊 t ‵= 𝕊 u) → Þ / Γ ⊢ t ‵= u

  --   A[0/x₀]    ∀y.A[y/x₀]→A[y+1/x₀]
  -- ------------------------------------
  --              ∀y.A[y/x₀]
  ‵ind    : ∀ {Þ Γ A A′ A″} (p : A [ 𝟘 /0]Fm ≡ A′) (q : wkFm A [ 𝕊 (‵tvar zero) /1]Fm ≡ A″)
              (d : Þ / Γ ⊢ A′) (e : Þ / Γ ⊢ ‵∀ (A ‵⊃ A″)) → Þ / Γ ⊢ ‵∀ A

  ‵proj   : ∀ {Þ Γ n τ τ′} (i : Fin n) (p : peek i τ ≡ τ′) → Þ / Γ ⊢ ‵fun (proj i) τ ‵= τ′

  ‵comp   : ∀ {Þ Γ n m τ τ′} (g : Prim m) (φ : Prim§ n m) (p : for φ (flip ‵fun τ) ≡ τ′) →
              Þ / Γ ⊢ ‵fun (comp g φ) τ ‵= ‵fun g τ′

  ‵rec    : ∀ {Þ Γ n t τ} (f : Prim n) (g : Prim (suc (suc n))) →
              Þ / Γ ⊢ ‵fun (rec f g) (τ , 𝟘) ‵= ‵fun f τ ‵∧
                ‵fun (rec f g) (τ , 𝕊 t) ‵= ‵fun g (τ , t , ‵fun (rec f g) (τ , t))

infix 3 _/_⊢§_
data _/_⊢§_ {k} (Þ : Theory) (Γ : Fm§ k) : Fm§ k → Set where
  ∙   : Þ / Γ ⊢§ ∙
  _,_ : ∀ {Δ A} (δ : Þ / Γ ⊢§ Δ) (d : Þ / Γ ⊢ A) → Þ / Γ ⊢§ Δ , A

-- NOTE: literals for derivation variables in terms
instance
  number⊢ : ∀ {Þ k} {Γ : Fm§ k} {A} → Number (Þ / Γ ⊢ A)
  number⊢ {Γ = Γ} {A} = record
    { Constraint = λ m → Γ ∋⟨ m ⟩ A
    ; fromNat    = λ m {{p}} → ‵var (∋#→∋ p)
    }


----------------------------------------------------------------------------------------------------

-- TODO: clean these up

eqrenpeekTm : ∀ {k k′ n} (η : k ≤ k′) (i : Fin n) (τ : Tm§ k n) →
                (peek i ∘ renTm§ η) τ ≡ (renTm η ∘ peek i) τ
eqrenpeekTm η zero    (τ , t) = refl
eqrenpeekTm η (suc i) (τ , t) = eqrenpeekTm η i τ

eqrenpokeTm : ∀ {k k′ n} (η : k ≤ k′) (i : Fin n) (s : Tm k) (τ : Tm§ k n) →
                (poke i (renTm η s) ∘ renTm§ η) τ ≡ (renTm§ η ∘ poke i s) τ
eqrenpokeTm η zero    s (τ , t) = refl
eqrenpokeTm η (suc i) s (τ , t) = (_, renTm η t) & eqrenpokeTm η i s τ

eqrenforTm : ∀ {k k′ n m} (η : k ≤ k′) (φ : Prim§ n m) (τ : Tm§ k n) →
               (for φ ∘ flip ‵fun ∘ renTm§ η) τ ≡ (renTm§ η ∘ for φ ∘ flip ‵fun) τ
eqrenforTm η ∙       τ = refl
eqrenforTm η (φ , f) τ = (_, ‵fun f (renTm§ η τ)) & eqrenforTm η φ τ

-- TODO: is the argument order correct here? is this somehow tget?
tren⊑ : ∀ {k k′ Γ Γ′} (η : k ≤ k′) → Γ ⊑ Γ′ → renFm§ η Γ ⊑ renFm§ η Γ′
tren⊑ η stop      = stop
tren⊑ η (wk⊑ ζ)   = wk⊑ (tren⊑ η ζ)
tren⊑ η (lift⊑ ζ) = lift⊑ (tren⊑ η ζ)

twk⊑ : ∀ {k} {Γ Γ′ : Fm§ k} → Γ ⊑ Γ′ → wkFm§ Γ ⊑ wkFm§ Γ′
twk⊑ η = tren⊑ (wk≤ id≤) η

-- {-# REWRITE lidrenFm lidrenFm§ #-}
-- TODO: useless? needs rewrite
-- lidtren⊑ : ∀ {k} {Γ Γ′ : Fm§ k} (η : Γ ⊑ Γ′) → tren⊑ id≤ η ≡ η
-- lidtren⊑ stop      = refl
-- lidtren⊑ (wk⊑ η)   = wk⊑ & lidtren⊑ η
-- lidtren⊑ (lift⊑ η) = lift⊑ & lidtren⊑ η

-- {-# REWRITE comprenFm comprenFm§ #-}
-- TODO: useless? needs rewrite
-- this one seems left-handed
-- comptren⊑ : ∀ {k k′ k″} {Γ Γ′ : Fm§ k} (η′ : k′ ≤ k″) (η : k ≤ k′) (ζ : Γ ⊑ Γ′) →
--   tren⊑ (η′ ∘≤ η) ζ ≡ (tren⊑ η′ ∘ tren⊑ η) ζ
-- comptren⊑ η′ η stop      = refl
-- comptren⊑ η′ η (wk⊑ ζ)   = wk⊑ & comptren⊑ η′ η ζ
-- comptren⊑ η′ η (lift⊑ ζ) = lift⊑ & comptren⊑ η′ η ζ

ridtren⊑ : ∀ {k k′} {Γ : Fm§ k} (η : k ≤ k′) → tren⊑ {Γ = Γ} η id⊑ ≡ id⊑
ridtren⊑ {Γ = ∙}     η = refl
ridtren⊑ {Γ = Γ , A} η = lift⊑ & ridtren⊑ η

-- TODO: rename? some kind of comptren⊑, but not the one i expected...
-- this one seems right-handed
-- TODO: argument order for tren⊑ seems wrong
comptren⊑? : ∀ {k k′ Γ Γ′ Γ″} (η : k ≤ k′) (ζ′ : Γ′ ⊑ Γ″) (ζ : Γ ⊑ Γ′) →
               tren⊑ η (ζ′ ∘⊑ ζ) ≡ tren⊑ η ζ′ ∘⊑ tren⊑ η ζ
comptren⊑? η stop       ζ         = refl
comptren⊑? η (wk⊑ ζ′)   ζ         = wk⊑ & comptren⊑? η ζ′ ζ
comptren⊑? η (lift⊑ ζ′) (wk⊑ ζ)   = wk⊑ & comptren⊑? η ζ′ ζ
comptren⊑? η (lift⊑ ζ′) (lift⊑ ζ) = lift⊑ & comptren⊑? η ζ′ ζ

tren∋ : ∀ {k k′ Γ A} (η : k ≤ k′) → Γ ∋ A → renFm§ η Γ ∋ renFm η A
tren∋ η zero    = zero
tren∋ η (suc i) = suc (tren∋ η i)

twk∋ : ∀ {k} {Γ : Fm§ k} {A} → Γ ∋ A → wkFm§ Γ ∋ wkFm A
twk∋ i = tren∋ (wk≤ id≤) i

-- {-# REWRITE lidrenFm lidrenFm§ #-}
-- TODO: useless?
-- lidtren∋ : ∀ {k} {Γ : Fm§ k} {A} (i : Γ ∋ A) → tren∋ id≤ i ≡ i
-- lidtren∋ zero    = refl
-- lidtren∋ (suc i) = suc & idtren∋ i

-- {-# REWRITE comprenFm comprenFm§ #-}
-- TODO: useless?
-- comptren∋ : ∀ {k k′ k″} {Γ : Fm§ k} {A} (η′ : k′ ≤ k″) (η : k ≤ k′) (i : Γ ∋ A) →
--               tren∋ (η′ ∘≤ η) i ≡ (tren∋ η′ ∘ tren∋ η) i
-- comptren∋ η′ η zero    = refl
-- comptren∋ η′ η (suc i) = suc & comptren∋ η′ η i

tren : ∀ {Þ k k′} {Γ : Fm§ k} {A} (η : k ≤ k′) → Þ / Γ ⊢ A → Þ / renFm§ η Γ ⊢ renFm η A
tren η (‵var i)                = ‵var (tren∋ η i)
tren η (‵lam d)                = ‵lam (tren η d)
tren η (d ‵$ e)                = tren η d ‵$ tren η e
tren η (‵pair d e)             = ‵pair (tren η d) (tren η e)
tren η (‵fst d)                = ‵fst (tren η d)
tren η (‵snd d)                = ‵snd (tren η d)
tren η (‵left d)               = ‵left (tren η d)
tren η (‵right d)              = ‵right (tren η d)
tren η (‵either c d e)         = ‵either (tren η c) (tren η d) (tren η e)
tren η (‵all refl d)           = ‵all (eqwkrenFm§ η _) (tren (lift≤ η) d)
tren η (‵unall t refl d)       = ‵unall (renTm η t) (eqrencut0Fm η _ t) (tren η d)
tren η (‵ex t refl d)          = ‵ex (renTm η t) (eqrencut0Fm η _ t) (tren η d)
tren η (‵letex refl refl d e)  = ‵letex (eqwkrenFm§ η _) (eqwkrenFm η _)
                                   (tren η d) (tren (lift≤ η) e)
tren η (‵abort d)              = ‵abort (tren η d)
tren η (‵magic d)              = ‵magic (tren η d)
tren η ‵refl                   = ‵refl
tren η (‵sym d)                = ‵sym (tren η d)
tren η (‵trans d e)            = ‵trans (tren η d) (tren η e)
tren η (‵cong f i refl refl d) = ‵cong f i (eqrenpeekTm η i _) (eqrenpokeTm η i _ _) (tren η d)
tren η ‵dis                    = ‵dis
tren η (‵inj d)                = ‵inj (tren η d)
tren η (‵ind refl refl d e)    = ‵ind (eqrencut0Fm η _ 𝟘) (eqrencut1Fm η _ (𝕊 (‵tvar zero)))
                                   (tren η d) (tren η e)
tren η (‵proj i refl)          = ‵proj i (eqrenpeekTm η i _)
tren η (‵comp g φ refl)        = ‵comp g φ (eqrenforTm η φ _)
tren η (‵rec f g)              = ‵rec f g

twk : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A → Þ / wkFm§ Γ ⊢ wkFm A
twk d = tren (wk≤ id≤) d

tren§ : ∀ {Þ k k′ Γ Δ} (η : k ≤ k′) → Þ / Γ ⊢§ Δ → Þ / renFm§ η Γ ⊢§ renFm§ η Δ
tren§ η ∙       = ∙
tren§ η (δ , d) = tren§ η δ , tren η d

twk§ : ∀ {Þ k} {Γ : Fm§ k} {Δ} → Þ / Γ ⊢§ Δ → Þ / wkFm§ Γ ⊢§ wkFm§ Δ
twk§ d = tren§ (wk≤ id≤) d

-- TODO: probably necessary for compsub
-- tsub : ∀ {Þ k m} {Γ : Fm§ k} {A} (σ : Tm§ m k) → Þ / Γ ⊢ A → Þ / subFm§ σ Γ ⊢ subFm σ A
-- tsub σ d = {!!}

-- TODO: needs rewrite; useless?
-- lidtren : ∀ {Þ k} {Γ : Fm§ k} {A} (d : Þ / Γ ⊢ A) → tren id≤ d ≡ d
-- lidtren = ?

-- TODO: needs rewrite; useless?
-- comptren : ∀ {Þ k k′ k″} {Γ : Fm§ k} {A} (η′ : k′ ≤ k″) (η : k ≤ k′) (d : Þ / Γ ⊢ A) →
--              tren (η′ ∘≤ η) d ≡ (tren η′ ∘ tren η) d
-- comptren = ?

ridtren : ∀ {Þ k k′} {Γ : Fm§ k} {A} (η : k ≤ k′) (i : Γ ∋ A) →
            (tren {Þ = Þ} η ∘ ‵var) i ≡ (‵var ∘ tren∋ η) i
ridtren η i = refl


----------------------------------------------------------------------------------------------------

-- 3.1. derivations: renaming

ren : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A} → Γ ⊑ Γ′ → Þ / Γ ⊢ A → Þ / Γ′ ⊢ A
ren η (‵var i)            = ‵var (ren∋ η i)
ren η (‵lam d)            = ‵lam (ren (lift⊑ η) d)
ren η (d ‵$ e)            = ren η d ‵$ ren η e
ren η (‵pair d e)         = ‵pair (ren η d) (ren η e)
ren η (‵fst d)            = ‵fst (ren η d)
ren η (‵snd d)            = ‵snd (ren η d)
ren η (‵left d)           = ‵left (ren η d)
ren η (‵right d)          = ‵right (ren η d)
ren η (‵either c d e)     = ‵either (ren η c) (ren (lift⊑ η) d) (ren (lift⊑ η) e)
ren η (‵all refl d)       = ‵all refl (ren (twk⊑ η) d)
ren η (‵unall t p d)      = ‵unall t p (ren η d)
ren η (‵ex t p d)         = ‵ex t p (ren η d)
ren η (‵letex refl q d e) = ‵letex refl q (ren η d) (ren (lift⊑ (twk⊑ η)) e)
ren η (‵abort d)          = ‵abort (ren η d)
ren η (‵magic d)          = ‵magic (ren (lift⊑ η) d)
ren η ‵refl               = ‵refl
ren η (‵sym d)            = ‵sym (ren η d)
ren η (‵trans d e)        = ‵trans (ren η d) (ren η e)
ren η (‵cong f i p q d)   = ‵cong f i p q (ren η d)
ren η ‵dis                = ‵dis
ren η (‵inj d)            = ‵inj (ren η d)
ren η (‵ind p q d e)      = ‵ind p q (ren η d) (ren η e)
ren η (‵proj i p)         = ‵proj i p
ren η (‵comp g φ p)       = ‵comp g φ p
ren η (‵rec f g)          = ‵rec f g


----------------------------------------------------------------------------------------------------

-- 3.2. derivations: generic lemmas from RenKit

wk : ∀ {Þ k} {Γ : Fm§ k} {A C} → Þ / Γ ⊢ A → Þ / Γ , C ⊢ A
wk d = ren (wk⊑ id⊑) d

ren§ : ∀ {Þ k} {Γ Γ′ : Fm§ k} {Δ} → Γ ⊑ Γ′ → Þ / Γ ⊢§ Δ → Þ / Γ′ ⊢§ Δ
ren§ η ∙       = ∙
ren§ η (δ , d) = ren§ η δ , ren η d

wk§ : ∀ {Þ k} {Γ : Fm§ k} {Δ C} → Þ / Γ ⊢§ Δ → Þ / Γ , C ⊢§ Δ
wk§ δ = ren§ (wk⊑ id⊑) δ

lift§ : ∀ {Þ k} {Γ : Fm§ k} {Δ C} → Þ / Γ ⊢§ Δ → Þ / Γ , C ⊢§ Δ , C
lift§ δ = wk§ δ , ‵var zero

var§ : ∀ {Þ k} {Γ Γ′ : Fm§ k} → Γ ⊑ Γ′ → Þ / Γ′ ⊢§ Γ
var§ stop      = ∙
var§ (wk⊑ η)   = wk§ (var§ η)
var§ (lift⊑ η) = lift§ (var§ η)

-- TODO: check if changing this affects anything
id§ : ∀ {Þ k} {Γ : Fm§ k} → Þ / Γ ⊢§ Γ
-- id§ {Γ = ∙}     = ∙
-- id§ {Γ = Γ , A} = lift§ id§
id§ = var§ id⊑

sub∋ : ∀ {Þ k} {Γ Ξ : Fm§ k} {A} → Þ / Ξ ⊢§ Γ → Γ ∋ A → Þ / Ξ ⊢ A
sub∋ (σ , s) zero    = s
sub∋ (σ , s) (suc i) = sub∋ σ i


----------------------------------------------------------------------------------------------------

-- 3.3. derivations: substitution

sub : ∀ {Þ k} {Γ Ξ : Fm§ k} {A} → Þ / Ξ ⊢§ Γ → Þ / Γ ⊢ A → Þ / Ξ ⊢ A
sub σ (‵var i)            = sub∋ σ i
sub σ (‵lam d)            = ‵lam (sub (lift§ σ) d)
sub σ (d ‵$ e)            = sub σ d ‵$ sub σ e
sub σ (‵pair d e)         = ‵pair (sub σ d) (sub σ e)
sub σ (‵fst d)            = ‵fst (sub σ d)
sub σ (‵snd d)            = ‵snd (sub σ d)
sub σ (‵left d)           = ‵left (sub σ d)
sub σ (‵right d)          = ‵right (sub σ d)
sub σ (‵either c d e)     = ‵either (sub σ c) (sub (lift§ σ) d) (sub (lift§ σ) e)
sub σ (‵all refl d)       = ‵all refl (sub (twk§ σ) d)
sub σ (‵unall t p d)      = ‵unall t p (sub σ d)
sub σ (‵ex t p d)         = ‵ex t p (sub σ d)
sub σ (‵letex refl q d e) = ‵letex refl q (sub σ d) (sub (lift§ (twk§ σ)) e)
sub σ (‵abort d)          = ‵abort (sub σ d)
sub σ (‵magic d)          = ‵magic (sub (lift§ σ) d)
sub σ ‵refl               = ‵refl
sub σ (‵sym d)            = ‵sym (sub σ d)
sub σ (‵trans d e)        = ‵trans (sub σ d) (sub σ e)
sub σ (‵cong f i p q d)   = ‵cong f i p q (sub σ d)
sub σ ‵dis                = ‵dis
sub σ (‵inj d)            = ‵inj (sub σ d)
sub σ (‵ind p q d e)      = ‵ind p q (sub σ d) (sub σ e)
sub σ (‵proj i p)         = ‵proj i p
sub σ (‵comp g φ p)       = ‵comp g φ p
sub σ (‵rec f g)          = ‵rec f g


----------------------------------------------------------------------------------------------------

-- 3.4. derivations: generic lemmas from SubKit

sub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} → Þ / Ξ ⊢§ Γ → Þ / Γ ⊢§ Δ → Þ / Ξ ⊢§ Δ
sub§ σ ∙       = ∙
sub§ σ (δ , d) = sub§ σ δ , sub σ d

_[_/0] : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ , A ⊢ B → Þ / Γ ⊢ A → Þ / Γ ⊢ B
d [ s /0] = sub (id§ , s) d

get§ : ∀ {Þ k} {Γ Δ Δ′ : Fm§ k} → Δ ⊑ Δ′ → Þ / Γ ⊢§ Δ′ → Þ / Γ ⊢§ Δ
get§ stop      δ       = δ
get§ (wk⊑ η)   (δ , d) = get§ η δ
get§ (lift⊑ η) (δ , d) = get§ η δ , d


----------------------------------------------------------------------------------------------------

-- 3.5. derivations: fundamental renaming lemmas

lidren : ∀ {Þ k} {Γ : Fm§ k} {A} (d : Þ / Γ ⊢ A) → ren id⊑ d ≡ d
lidren (‵var i)                = ‵var & idren∋ i
lidren (‵lam d)                = ‵lam & lidren d
lidren (d ‵$ e)                = _‵$_ & lidren d ⊗ lidren e
lidren (‵pair d e)             = ‵pair & lidren d ⊗ lidren e
lidren (‵fst d)                = ‵fst & lidren d
lidren (‵snd d)                = ‵snd & lidren d
lidren (‵left d)               = ‵left & lidren d
lidren (‵right d)              = ‵right & lidren d
lidren (‵either c d e)         = ‵either & lidren c ⊗ lidren d ⊗ lidren e
lidren (‵all refl d)           = ‵all refl
                                   & ( flip ren d & ridtren⊑ (wk≤ id≤)
                                     ⋮ lidren d
                                     )
lidren (‵unall t refl d)       = ‵unall t refl & lidren d
lidren (‵ex t refl d)          = ‵ex t refl & lidren d
lidren (‵letex refl refl d e)  = ‵letex refl refl
                                   & lidren d
                                   ⊗ ( (flip ren e ∘ lift⊑) & ridtren⊑ (wk≤ id≤)
                                     ⋮ lidren e
                                     )
lidren (‵abort d)              = ‵abort & lidren d
lidren (‵magic d)              = ‵magic & lidren d
lidren ‵refl                   = refl
lidren (‵sym d)                = ‵sym & lidren d
lidren (‵trans d e)            = ‵trans & lidren d ⊗ lidren e
lidren (‵cong f i refl refl d) = ‵cong f i refl refl & lidren d
lidren ‵dis                    = refl
lidren (‵inj d)                = ‵inj & lidren d
lidren (‵ind refl refl d e)    = ‵ind refl refl & lidren d ⊗ lidren e
lidren (‵proj i refl)          = refl
lidren (‵comp g φ refl)        = refl
lidren (‵rec f g)              = refl

compren : ∀ {Þ k} {Γ Γ′ Γ″ : Fm§ k} {A} (η′ : Γ′ ⊑ Γ″) (η : Γ ⊑ Γ′) (d : Þ / Γ ⊢ A) →
            ren (η′ ∘⊑ η) d ≡ (ren η′ ∘ ren η) d
compren η′ η (‵var i)                = ‵var & compren∋ η′ η i
compren η′ η (‵lam d)                = ‵lam & compren (lift⊑ η′) (lift⊑ η) d
compren η′ η (d ‵$ e)                = _‵$_ & compren η′ η d ⊗ compren η′ η e
compren η′ η (‵pair d e)             = ‵pair & compren η′ η d ⊗ compren η′ η e
compren η′ η (‵fst d)                = ‵fst & compren η′ η d
compren η′ η (‵snd d)                = ‵snd & compren η′ η d
compren η′ η (‵left d)               = ‵left & compren η′ η d
compren η′ η (‵right d)              = ‵right & compren η′ η d
compren η′ η (‵either c d e)         = ‵either
                                         & compren η′ η c
                                         ⊗ compren (lift⊑ η′) (lift⊑ η) d
                                         ⊗ compren (lift⊑ η′) (lift⊑ η) e
compren η′ η (‵all refl d)           = ‵all refl
                                         & ( flip ren d & comptren⊑? (wk≤ id≤) η′ η
                                           ⋮ compren (twk⊑ η′) (twk⊑ η) d
                                           )
compren η′ η (‵unall t refl d)       = ‵unall t refl & compren η′ η d
compren η′ η (‵ex t refl d)          = ‵ex t refl & compren η′ η d
compren η′ η (‵letex refl refl d e)  = ‵letex refl refl
                                         & compren η′ η d
                                         ⊗ ( (flip ren e ∘ lift⊑) & comptren⊑? (wk≤ id≤) η′ η
                                           ⋮ compren (lift⊑ (twk⊑ η′)) (lift⊑ (twk⊑ η)) e
                                           )
compren η′ η (‵abort d)              = ‵abort & compren η′ η d
compren η′ η (‵magic d)              = ‵magic & compren (lift⊑ η′) (lift⊑ η) d
compren η′ η ‵refl                   = refl
compren η′ η (‵sym d)                = ‵sym & compren η′ η d
compren η′ η (‵trans d e)            = ‵trans & compren η′ η d ⊗ compren η′ η e
compren η′ η (‵cong f i refl refl d) = ‵cong f i refl refl & compren η′ η d
compren η′ η ‵dis                    = refl
compren η′ η (‵inj d)                = ‵inj & compren η′ η d
compren η′ η (‵ind refl refl d e)    = ‵ind refl refl & compren η′ η d ⊗ compren η′ η e
compren η′ η (‵proj i refl)          = refl
compren η′ η (‵comp g φ refl)        = refl
compren η′ η (‵rec f g)              = refl

ridren : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A} (η : Γ ⊑ Γ′) (i : Γ ∋ A) →
           (ren {Þ = Þ} η ∘ ‵var) i ≡ (‵var ∘ ren∋ η) i
ridren η i = refl

ridsub : ∀ {Þ k} {Γ Ξ : Fm§ k} {A} (σ : Þ / Ξ ⊢§ Γ) (i : Γ ∋ A) →
           (sub σ ∘ ‵var) i ≡ sub∋ σ i
ridsub σ i = refl


----------------------------------------------------------------------------------------------------

-- TODO: clean these up

cast⊑ : ∀ {k} {Γ Γ′ : Fm§ k} → Γ ≡ Γ′ → Γ ⊑ Γ′
cast⊑ refl = id⊑

-- TODO: rename
cast⊑-pair : ∀ {k} {Γ Γ′ : Fm§ k} {C C′} (p : Γ ≡ Γ′) (q : C ≡ C′) →
               cast⊑ ((Γ′ ,_) & q) ∘⊑ lift⊑ (cast⊑ p) ≡ cast⊑ (_,_ & p ⊗ q)
cast⊑-pair refl refl = lift⊑ & lid⊑ id⊑

-- TODO: rename
cast⊑-pair-alt : ∀ {k} {Γ Γ′ : Fm§ k} {C C′} (p : Γ ≡ Γ′) (q : C ≡ C′) →
                   lift⊑ (cast⊑ p) ∘⊑ cast⊑ ((Γ ,_) & q) ≡ cast⊑ (_,_ & p ⊗ q)
cast⊑-pair-alt refl refl = lift⊑ & lid⊑ id⊑

-- TODO: rename
cast⊑-eat : ∀ {k} {Γ Γ′ : Fm§ k} {C C′} (q : C ≡ C′) (ζ : Γ ⊑ Γ′) →
              cast⊑ ((Γ′ ,_) & q) ∘⊑ wk⊑ ζ ≡ wk⊑ ζ
cast⊑-eat refl ζ = wk⊑ & lid⊑ ζ

-- TODO: rename
cast⊑-slide : ∀ {k} {Γ Γ′ : Fm§ k} {C C′} (q : C ≡ C′) (ζ : Γ ⊑ Γ′) →
                cast⊑ ((Γ′ ,_) & q) ∘⊑ lift⊑ ζ ≡ lift⊑ ζ ∘⊑ cast⊑ ((Γ ,_) & q)
cast⊑-slide refl ζ = lift⊑ & ( lid⊑ ζ
                             ⋮ rid⊑ ζ ⁻¹
                             )

-- cast⊑-trans : ∀ {k} {Γ Γ′ Γ″ : Fm§ k} (e₂ : Γ ≡ Γ′) (e₁ : Γ′ ≡ Γ″) →
--                 cast⊑ ( e₂ ⋮ e₁) ≡ cast⊑ e₁ ∘⊑ cast⊑ e₂
-- cast⊑-trans refl refl = lid⊑ id⊑ ⁻¹

-- cast⊑-cancel : ∀ {k} {Γ Γ′ : Fm§ k} (e : Γ ≡ Γ′) → cast⊑ e ∘⊑ cast⊑ (e ⁻¹) ≡ id⊑
-- cast⊑-cancel refl = lid⊑ id⊑

-- cast⊑-cancel-alt : ∀ {k} {Γ Γ′ : Fm§ k} (e : Γ ≡ Γ′) → cast⊑ (e ⁻¹) ∘⊑ cast⊑ e ≡ id⊑
-- cast⊑-cancel-alt refl = lid⊑ id⊑

-- cast⊑-ren : ∀ {k k′} {Γ Γ′ : Fm§ k} {η η′ : k ≤ k′} (ζ : Γ ⊑ Γ′) (e : η ≡ η′) →
--                 cast⊑ ((flip renFm§ Γ′) & e) ∘⊑ tren⊑ η ζ ≡
--                   tren⊑ η′ ζ ∘⊑ cast⊑ ((flip renFm§ Γ) & e)
-- cast⊑-ren {η = η} {η′ = η′} ζ refl = ( lid⊑ (tren⊑ η ζ)  ⋮ rid⊑ (tren⊑ η ζ) ⁻¹ )

eqall : ∀ {Þ k} {Γ : Fm§ k} {Γ′ A} (p : Γ′ ≡ wkFm§ Γ) (d : Þ / Γ′ ⊢ A) →
          ‵all refl (ren (cast⊑ p) d) ≡ ‵all p d
eqall refl d = ‵all refl & lidren d

eqletex : ∀ {Þ k} {Γ : Fm§ k} {Γ′ A C C′} (p : Γ′ ≡ wkFm§ Γ) (q : C′ ≡ wkFm C)
            (d : Þ / Γ ⊢ ‵∃ A) (e : Þ / Γ′ , A ⊢ C′) →
            ‵letex refl q d (ren (lift⊑ (cast⊑ p)) e) ≡ ‵letex p q d e
eqletex refl q d e = ‵letex refl q d & lidren e


----------------------------------------------------------------------------------------------------

-- TODO: clean these up

-- TODO: rename
untitled1 : ∀ {k k′} {Γ Γ′ : Fm§ k} (η : k ≤ k′) (ζ : Γ ⊑ Γ′) →
              (twk⊑ ∘ tren⊑ η) ζ ∘⊑ cast⊑ (eqwkrenFm§ η Γ) ≡
              cast⊑ (eqwkrenFm§ η Γ′) ∘⊑ (tren⊑ (lift≤ η) ∘ twk⊑) ζ
untitled1 {Γ = Γ}    {Γ′ = ∙}      η stop       = refl
untitled1 {Γ = Γ}    {Γ′ = Γ′ , C} η (wk⊑ ζ)    =
    begin
      twk⊑ ((tren⊑ η ∘ wk⊑) ζ) ∘⊑ cast⊑ (eqwkrenFm§ η Γ)
    ≡⟨⟩
      wk⊑ ((twk⊑ ∘ tren⊑ η) ζ ∘⊑ cast⊑ (eqwkrenFm§ η Γ))
    ≡⟨ cast⊑-eat (eqwkrenFm η C) ((twk⊑ ∘ tren⊑ η) ζ ∘⊑ cast⊑ (eqwkrenFm§ η Γ)) ⁻¹ ⟩
      cast⊑ ((wkFm§ (renFm§ η Γ′) ,_) & eqwkrenFm η C) ∘⊑
        wk⊑ ((twk⊑ ∘ tren⊑ η) ζ ∘⊑ cast⊑ (eqwkrenFm§ η Γ))
    ≡⟨ ((cast⊑ ((wkFm§ (renFm§ η Γ′) ,_) & eqwkrenFm η C) ∘⊑_) ∘ wk⊑) & untitled1 η ζ ⟩
      cast⊑ ((wkFm§ (renFm§ η Γ′) ,_) & eqwkrenFm η C) ∘⊑
        wk⊑ (cast⊑ (eqwkrenFm§ η Γ′) ∘⊑ (tren⊑ (lift≤ η) ∘ twk⊑) ζ)
    ≡⟨ ass⊑
         (cast⊑ (((wkFm§ ∘ renFm§ η) Γ′ ,_) & eqwkrenFm η C))
         (lift⊑ (cast⊑ (eqwkrenFm§ η Γ′)))
         (wk⊑ ((tren⊑ (lift≤ η) ∘ twk⊑) ζ))
    ⟩
      (cast⊑ (((wkFm§ ∘ renFm§ η) Γ′ ,_) & eqwkrenFm η C) ∘⊑
          lift⊑ (cast⊑ (eqwkrenFm§ η Γ′))) ∘⊑
        wk⊑ ((tren⊑ (lift≤ η) ∘ twk⊑) ζ)
    ≡⟨ (_∘⊑ (wk⊑ ∘ tren⊑ (lift≤ η) ∘ twk⊑) ζ) & cast⊑-pair (eqwkrenFm§ η Γ′) (eqwkrenFm η C) ⟩
      cast⊑ (_,_ & eqwkrenFm§ η Γ′ ⊗ eqwkrenFm η C) ∘⊑ (wk⊑ ∘ tren⊑ (lift≤ η) ∘ twk⊑) ζ
    ≡⟨⟩
      cast⊑ (eqwkrenFm§ η (Γ′ , C)) ∘⊑ (tren⊑ (lift≤ η) ∘ twk⊑ ∘ wk⊑) ζ
    ∎
  where
    open ≡-Reasoning
untitled1 {Γ = Γ , C} {Γ′ = Γ′ , C} η (lift⊑ ζ) =
   begin
     twk⊑ ((tren⊑ η ∘ lift⊑) ζ) ∘⊑ cast⊑ (eqwkrenFm§ η (Γ , C))
   ≡⟨⟩
     twk⊑ ((lift⊑ ∘ tren⊑ η) ζ) ∘⊑
       cast⊑ (_,_ & eqwkrenFm§ η Γ ⊗ eqwkrenFm η C)
   ≡⟨ (twk⊑ ((lift⊑ ∘ tren⊑ η) ζ) ∘⊑_) & cast⊑-pair-alt (eqwkrenFm§ η Γ) (eqwkrenFm η C) ⁻¹ ⟩
     twk⊑ ((lift⊑ ∘ tren⊑ η) ζ) ∘⊑
       lift⊑ (cast⊑ (eqwkrenFm§ η Γ)) ∘⊑
       cast⊑ ((((renFm§ (lift≤ η) ∘ wkFm§) Γ) ,_) & eqwkrenFm η C)
   ≡⟨ ass⊑
        (twk⊑ ((lift⊑ ∘ tren⊑ η) ζ))
        (lift⊑ (cast⊑ (eqwkrenFm§ η Γ)))
        (cast⊑ ((((renFm§ (lift≤ η) ∘ wkFm§) Γ) ,_) & eqwkrenFm η C))
   ⟩
     lift⊑ ((twk⊑ ∘ tren⊑ η) ζ ∘⊑ cast⊑ (eqwkrenFm§ η Γ)) ∘⊑
       cast⊑ ((((renFm§ (lift≤ η) ∘ wkFm§) Γ) ,_) & eqwkrenFm η C)
   ≡⟨ cast⊑-slide (eqwkrenFm η C) ((twk⊑ ∘ tren⊑ η) ζ ∘⊑ cast⊑ (eqwkrenFm§ η Γ)) ⁻¹ ⟩
     cast⊑ (((wkFm§ ∘ renFm§ η) Γ′ ,_) & eqwkrenFm η C) ∘⊑
       lift⊑ ((twk⊑ ∘ tren⊑ η) ζ ∘⊑ cast⊑ (eqwkrenFm§ η Γ))
   ≡⟨ ((cast⊑ (((wkFm§ ∘ renFm§ η) Γ′ ,_) & eqwkrenFm η C) ∘⊑_) ∘ lift⊑) & untitled1 η ζ ⟩
     cast⊑ (((wkFm§ ∘ renFm§ η) Γ′ ,_) & eqwkrenFm η C) ∘⊑
       lift⊑ ((cast⊑ (eqwkrenFm§ η Γ′)) ∘⊑ ((tren⊑ (lift≤ η) ∘ twk⊑) ζ))
   ≡⟨ ass⊑
        (cast⊑ (((wkFm§ ∘ renFm§ η) Γ′ ,_) & eqwkrenFm η C))
        (lift⊑ (cast⊑ (eqwkrenFm§ η Γ′)))
        (lift⊑ ((tren⊑ (lift≤ η) ∘ twk⊑) ζ))
   ⟩
     (cast⊑ (((wkFm§ ∘ renFm§ η) Γ′ ,_) & eqwkrenFm η C) ∘⊑
         lift⊑ (cast⊑ (eqwkrenFm§ η Γ′))) ∘⊑
       lift⊑ ((tren⊑ (lift≤ η) ∘ twk⊑) ζ)
   ≡⟨ (_∘⊑ lift⊑ ((tren⊑ (lift≤ η) ∘ twk⊑) ζ)) & cast⊑-pair (eqwkrenFm§ η Γ′) (eqwkrenFm η C) ⟩
     cast⊑ (_,_ & eqwkrenFm§ η Γ′ ⊗ eqwkrenFm η C) ∘⊑ lift⊑ ((tren⊑ (lift≤ η) ∘ twk⊑) ζ)
   ≡⟨⟩
     cast⊑ (eqwkrenFm§ η (Γ′ , C)) ∘⊑ tren⊑ (lift≤ η) ((twk⊑ ∘ lift⊑) ζ)
   ∎
 where
   open ≡-Reasoning

eqtrenren∋ : ∀ {k k′ Γ Γ′ A} (η : k ≤ k′) (ζ : Γ ⊑ Γ′) (i : Γ ∋ A) →
               (ren∋ (tren⊑ η ζ) ∘ tren∋ η) i ≡ (tren∋ η ∘ ren∋ ζ) i
eqtrenren∋ η (wk⊑ ζ)   i       = suc & eqtrenren∋ η ζ i
eqtrenren∋ η (lift⊑ ζ) zero    = refl
eqtrenren∋ η (lift⊑ ζ) (suc i) = suc & eqtrenren∋ η ζ i

eqtrenren : ∀ {Þ k k′ Γ Γ′ A} (η : k ≤ k′) (ζ : Γ ⊑ Γ′) (d : Þ / Γ ⊢ A) →
              (ren (tren⊑ η ζ) ∘ tren η) d ≡ (tren η ∘ ren ζ) d
eqtrenren η ζ (‵var i)                = ‵var & eqtrenren∋ η ζ i
eqtrenren η ζ (‵lam d)                = ‵lam & eqtrenren η (lift⊑ ζ) d
eqtrenren η ζ (d ‵$ e)                = _‵$_ & eqtrenren η ζ d ⊗ eqtrenren η ζ e
eqtrenren η ζ (‵pair d e)             = ‵pair & eqtrenren η ζ d ⊗ eqtrenren η ζ e
eqtrenren η ζ (‵fst d)                = ‵fst & eqtrenren η ζ d
eqtrenren η ζ (‵snd d)                = ‵snd & eqtrenren η ζ d
eqtrenren η ζ (‵left d)               = ‵left & eqtrenren η ζ d
eqtrenren η ζ (‵right d)              = ‵right & eqtrenren η ζ d
eqtrenren η ζ (‵either c d e)         = ‵either
                                          & eqtrenren η ζ c
                                          ⊗ eqtrenren η (lift⊑ ζ) d
                                          ⊗ eqtrenren η (lift⊑ ζ) e
eqtrenren {Γ = Γ} {Γ′} η ζ (‵all {A = A} refl d) =
    begin
      (ren (tren⊑ η ζ) ∘ tren η) (‵all refl d)
    ≡⟨⟩
      ren (tren⊑ η ζ) (‵all (eqwkrenFm§ η Γ) (tren (lift≤ η) d))
    ≡⟨ ren (tren⊑ η ζ) & eqall (eqwkrenFm§ η Γ) (tren (lift≤ η) d) ⁻¹ ⟩
      ren (tren⊑ η ζ) (‵all refl ((ren (cast⊑ (eqwkrenFm§ η Γ)) ∘ tren (lift≤ η)) d))
    ≡⟨⟩
      ‵all refl ((ren (twk⊑ (tren⊑ η ζ)) ∘ ren (cast⊑ (eqwkrenFm§ η Γ)) ∘ tren (lift≤ η)) d)
    ≡⟨ ‵all refl
         & (begin
             (ren (twk⊑ (tren⊑ η ζ)) ∘ ren (cast⊑ (eqwkrenFm§ η Γ)) ∘ tren (lift≤ η)) d
           ≡⟨ compren (twk⊑ (tren⊑ η ζ)) (cast⊑ (eqwkrenFm§ η Γ)) (tren (lift≤ η) d) ⁻¹ ⟩
             (ren (twk⊑ (tren⊑ η ζ) ∘⊑ cast⊑ (eqwkrenFm§ η Γ)) ∘ tren (lift≤ η)) d
           ≡⟨ flip ren (tren (lift≤ η) d) & untitled1 η ζ ⟩
             (ren (cast⊑ (eqwkrenFm§ η Γ′) ∘⊑ tren⊑ (lift≤ η) (twk⊑ ζ)) ∘ tren (lift≤ η)) d
           ≡⟨ compren (cast⊑ (eqwkrenFm§ η Γ′)) (tren⊑ (lift≤ η) (twk⊑ ζ)) (tren (lift≤ η) d) ⟩
             (ren (cast⊑ (eqwkrenFm§ η Γ′)) ∘ ren (tren⊑ (lift≤ η) (twk⊑ ζ)) ∘ tren (lift≤ η)) d
           ∎)
    ⟩
      ‵all refl ((ren (cast⊑ (eqwkrenFm§ η Γ′)) ∘
        ren (tren⊑ (lift≤ η) (twk⊑ ζ)) ∘
        tren (lift≤ η)) d)
    ≡⟨ eqall (eqwkrenFm§ η Γ′) ((ren (tren⊑ (lift≤ η) (twk⊑ ζ)) ∘ tren (lift≤ η)) d) ⟩
      ‵all (eqwkrenFm§ η Γ′) ((ren (tren⊑ (lift≤ η) (twk⊑ ζ)) ∘ tren (lift≤ η)) d)
    ≡⟨ ‵all (eqwkrenFm§ η Γ′) & eqtrenren (lift≤ η) (twk⊑ ζ) d ⟩
      ‵all (eqwkrenFm§ η Γ′) (tren (lift≤ η) (ren (twk⊑ ζ) d))
    ≡⟨⟩
      (tren η ∘ ren ζ) (‵all refl d)
    ∎
  where
    open ≡-Reasoning
eqtrenren η ζ (‵unall t refl d)       = ‵unall (renTm η t) (eqrencut0Fm η _ t) & eqtrenren η ζ d
eqtrenren η ζ (‵ex t refl d)          = ‵ex (renTm η t) (eqrencut0Fm η _ t) & eqtrenren η ζ d
eqtrenren {Γ = Γ} {Γ′} η ζ (‵letex {A = A} {C} refl refl d e) =
    begin
      (ren (tren⊑ η ζ) ∘ tren η) (‵letex refl refl d e)
    ≡⟨⟩
      ren (tren⊑ η ζ) (‵letex (eqwkrenFm§ η Γ) (eqwkrenFm η C) (tren η d) (tren (lift≤ η) e))
    ≡⟨ ren (tren⊑ η ζ) & eqletex (eqwkrenFm§ η Γ) (eqwkrenFm η C) (tren η d) (tren (lift≤ η) e) ⁻¹ ⟩
      ren (tren⊑ η ζ)
        (‵letex refl (eqwkrenFm η C) (tren η d)
          ((ren (lift⊑ (cast⊑ (eqwkrenFm§ η Γ))) ∘ tren (lift≤ η)) e))
    ≡⟨⟩
      ‵letex refl (eqwkrenFm η C) ((ren (tren⊑ η ζ) ∘ tren η) d)
        ((ren (lift⊑ (twk⊑ (tren⊑ η ζ))) ∘
          ren (lift⊑ (cast⊑ (eqwkrenFm§ η Γ))) ∘
          tren (lift≤ η)) e)
    ≡⟨ ‵letex refl (eqwkrenFm η C) ((ren (tren⊑ η ζ) ∘ tren η) d)
         & (begin
           (ren (lift⊑ (twk⊑ (tren⊑ η ζ))) ∘
             ren (lift⊑ (cast⊑ (eqwkrenFm§ η Γ))) ∘
             tren (lift≤ η)) e
         ≡⟨ compren (lift⊑ (twk⊑ (tren⊑ η ζ))) (lift⊑ (cast⊑ (eqwkrenFm§ η Γ)))
              (tren (lift≤ η) e) ⁻¹
         ⟩
           (ren (lift⊑ (twk⊑ (tren⊑ η ζ)) ∘⊑
               lift⊑ (cast⊑ (eqwkrenFm§ η Γ))) ∘
             tren (lift≤ η)) e
         ≡⟨ (flip ren (tren (lift≤ η) e) ∘ lift⊑) & untitled1 η ζ ⟩
           (ren (lift⊑ (cast⊑ (eqwkrenFm§ η Γ′)) ∘⊑
               tren⊑ (lift≤ η) (lift⊑ (twk⊑ ζ))) ∘
             tren (lift≤ η)) e
         ≡⟨ compren (lift⊑ (cast⊑ (eqwkrenFm§ η Γ′))) (tren⊑ (lift≤ η) (lift⊑ (twk⊑ ζ)))
              (tren (lift≤ η) e)
         ⟩
           (ren (lift⊑ (cast⊑ (eqwkrenFm§ η Γ′))) ∘
             (ren (tren⊑ (lift≤ η) (lift⊑ (twk⊑ ζ))) ∘
             tren (lift≤ η))) e
         ∎)
    ⟩
      ‵letex refl (eqwkrenFm η C) ((ren (tren⊑ η ζ) ∘ tren η) d)
        ((ren (lift⊑ (cast⊑ (eqwkrenFm§ η Γ′))) ∘
          ren (tren⊑ (lift≤ η) (lift⊑ (twk⊑ ζ))) ∘
          tren (lift≤ η)) e)
    ≡⟨ eqletex (eqwkrenFm§ η Γ′) (eqwkrenFm η C) ((ren (tren⊑ η ζ) ∘ tren η) d)
         ((ren (tren⊑ (lift≤ η) (lift⊑ (twk⊑ ζ))) ∘ tren (lift≤ η)) e)
    ⟩
      ‵letex (eqwkrenFm§ η Γ′) (eqwkrenFm η C) ((ren (tren⊑ η ζ) ∘ tren η) d)
        ((ren (tren⊑ (lift≤ η) (lift⊑ (twk⊑ ζ))) ∘ tren (lift≤ η)) e)
    ≡⟨ ‵letex (eqwkrenFm§ η Γ′) (eqwkrenFm η C)
         & eqtrenren η ζ d
         ⊗ eqtrenren (lift≤ η) (lift⊑ (twk⊑ ζ)) e
    ⟩
      ‵letex (eqwkrenFm§ η Γ′) (eqwkrenFm η C) ((tren η ∘ ren ζ) d)
        ((tren (lift≤ η) ∘ ren (lift⊑ (twk⊑ ζ))) e)
    ≡⟨⟩
      (tren η ∘ ren ζ) (‵letex refl refl d e)
    ∎
  where
    open ≡-Reasoning
eqtrenren η ζ (‵abort d)              = ‵abort & eqtrenren η ζ d
eqtrenren η ζ (‵magic d)              = ‵magic & eqtrenren η (lift⊑ ζ) d
eqtrenren η ζ ‵refl                   = refl
eqtrenren η ζ (‵sym d)                = ‵sym & eqtrenren η ζ d
eqtrenren η ζ (‵trans d e)            = ‵trans & eqtrenren η ζ d ⊗ eqtrenren η ζ e
eqtrenren η ζ (‵cong f i refl refl d) = ‵cong f i (eqrenpeekTm η i _) (eqrenpokeTm η i _ _)
                                          & eqtrenren η ζ d
eqtrenren η ζ ‵dis                    = refl
eqtrenren η ζ (‵inj d)                = ‵inj & eqtrenren η ζ d
eqtrenren η ζ (‵ind refl refl d e)    = ‵ind (eqrencut0Fm η _ 𝟘)
                                            (eqrencut1Fm η _ (𝕊 (‵tvar zero)))
                                          & eqtrenren η ζ d
                                          ⊗ eqtrenren η ζ e
eqtrenren η ζ (‵proj i refl)          = refl
eqtrenren η ζ (‵comp g φ refl)        = refl
eqtrenren η ζ (‵rec f g)              = refl

eqtrenren§ : ∀ {Þ k k′ Γ Γ′ Δ} (η : k ≤ k′) (ζ : Γ ⊑ Γ′) (δ : Þ / Γ ⊢§ Δ) →
               (ren§ (tren⊑ η ζ) ∘ tren§ η) δ ≡ (tren§ η ∘ ren§ ζ) δ
eqtrenren§ η ζ ∙       = refl
eqtrenren§ η ζ (δ , d) = _,_ & eqtrenren§ η ζ δ ⊗ eqtrenren η ζ d

eqtrenget§ : ∀ {Þ k k′ Γ Δ Δ′} (η : k ≤ k′) (ζ : Δ ⊑ Δ′) (δ : Þ / Γ ⊢§ Δ′) →
               (get§ (tren⊑ η ζ) ∘ tren§ η) δ ≡ (tren§ η ∘ get§ ζ) δ
eqtrenget§ η stop      δ       = refl
eqtrenget§ η (wk⊑ ζ)   (δ , d) = eqtrenget§ η ζ δ
eqtrenget§ η (lift⊑ ζ) (δ , d) = (_, tren η d) & eqtrenget§ η ζ δ

ridtren§ : ∀ {Þ k k′} {Γ : Fm§ k} (η : k ≤ k′) →
             tren§ {Þ = Þ} {Γ = Γ} η id§ ≡ id§
ridtren§ {Γ = ∙}     η = refl
ridtren§ {Γ = Γ , A} η = (_, ‵var zero)
                           & ( eqtrenren§ η (wk⊑ id⊑) id§ ⁻¹
                             ⋮ ren§ & (wk⊑ & ridtren⊑ η) ⊗ ridtren§ η
                             )


----------------------------------------------------------------------------------------------------

-- 3.6. derivations: generic lemmas from RenSubKit1

lidren§ : ∀ {Þ k} {Γ Δ : Fm§ k} (δ : Þ / Γ ⊢§ Δ) → ren§ id⊑ δ ≡ δ
lidren§ ∙       = refl
lidren§ (δ , d) = _,_ & lidren§ δ ⊗ lidren d

compren§ : ∀ {Þ k} {Γ Γ′ Γ″ Δ : Fm§ k} (η′ : Γ′ ⊑ Γ″) (η : Γ ⊑ Γ′) (δ : Þ / Γ ⊢§ Δ) →
             ren§ (η′ ∘⊑ η) δ ≡ (ren§ η′ ∘ ren§ η) δ
compren§ η′ η ∙       = refl
compren§ η′ η (δ , d) = _,_ & compren§ η′ η δ ⊗ compren η′ η d

eqwkren : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A C} (η : Γ ⊑ Γ′) (d : Þ / Γ ⊢ A) →
            (ren (lift⊑ η) ∘ wk {C = C}) d ≡ (wk ∘ ren η) d
eqwkren η d = compren (lift⊑ η) (wk⊑ id⊑) d ⁻¹
            ⋮ (flip ren d ∘ wk⊑)
                & ( rid⊑ η
                  ⋮ lid⊑ η ⁻¹
                  )
            ⋮ compren (wk⊑ id⊑) η d

eqwkren§ : ∀ {Þ k} {Γ Γ′ Δ : Fm§ k} {C} (η : Γ ⊑ Γ′) (δ : Þ / Γ ⊢§ Δ) →
             (ren§ (lift⊑ η) ∘ wk§ {C = C}) δ ≡ (wk§ ∘ ren§ η) δ
eqwkren§ η ∙       = refl
eqwkren§ η (δ , d) = _,_ & eqwkren§ η δ ⊗ eqwkren η d

eqliftren§ : ∀ {Þ k} {Γ Γ′ Δ : Fm§ k} {C} (η : Γ ⊑ Γ′) (δ : Þ / Γ ⊢§ Δ) →
               (ren§ (lift⊑ η) ∘ lift§ {C = C}) δ ≡ (lift§ ∘ ren§ η) δ
eqliftren§ η δ = _,_ & eqwkren§ η δ ⊗ ridren (lift⊑ η) zero

ridren§ : ∀ {Þ k} {Γ Γ′ : Fm§ k} (η : Γ ⊑ Γ′) → ren§ {Þ = Þ} η id§ ≡ var§ η
ridren§ stop      = refl
ridren§ (wk⊑ η)   = (flip ren§ id§ ∘ wk⊑) & lid⊑ η ⁻¹
                  ⋮ compren§ (wk⊑ id⊑) η id§
                  ⋮ wk§ & ridren§ η
ridren§ (lift⊑ η) = _,_
                      & ( eqwkren§ η id§
                        ⋮ wk§ & ridren§ η
                        )
                      ⊗ ridren (lift⊑ η) zero

eqrensub∋ : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A} (η : Ξ ⊑ Ξ′) (σ : Þ / Ξ ⊢§ Γ) (i : Γ ∋ A) →
              sub∋ (ren§ η σ) i ≡ (ren η ∘ sub∋ σ) i
eqrensub∋ η (σ , s) zero    = refl
eqrensub∋ η (σ , s) (suc i) = eqrensub∋ η σ i

eqsubren∋ : ∀ {Þ k} {Γ Γ′ Ξ : Fm§ k} {A} (σ : Þ / Ξ ⊢§ Γ′) (η : Γ ⊑ Γ′) (i : Γ ∋ A) →
              sub∋ (get§ η σ) i ≡ (sub∋ σ ∘ ren∋ η) i
eqsubren∋ ∙       stop      i       = refl
eqsubren∋ (σ , s) (wk⊑ η)   i       = eqsubren∋ σ η i
eqsubren∋ (σ , s) (lift⊑ η) zero    = refl
eqsubren∋ (σ , s) (lift⊑ η) (suc i) = eqsubren∋ σ η i

idsub∋ : ∀ {Þ k} {Γ : Fm§ k} {A} (i : Γ ∋ A) → sub∋ {Þ = Þ} id§ i ≡ ‵var i
idsub∋ zero    = refl
idsub∋ (suc i) = eqrensub∋ (wk⊑ id⊑) id§ i
               ⋮ wk & idsub∋ i
               ⋮ ridren (wk⊑ id⊑) i
               ⋮ (‵var ∘ suc) & idren∋ i

compsub∋ : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ) (i : Γ ∋ A) →
             sub∋ (sub§ σ′ σ) i ≡ (sub σ′ ∘ sub∋ σ) i
compsub∋ σ′ (σ , s) zero    = refl
compsub∋ σ′ (σ , s) (suc i) = compsub∋ σ′ σ i

lidget§ : ∀ {Þ k} {Γ Δ : Fm§ k} (δ : Þ / Γ ⊢§ Δ) → get§ id⊑ δ ≡ δ
lidget§ ∙       = refl
lidget§ (δ , d) = (_, d) & lidget§ δ

compget§ : ∀ {Þ k} {Γ Δ Δ′ Δ″ : Fm§ k} (η : Δ ⊑ Δ′) (η′ : Δ′ ⊑ Δ″) (δ : Þ / Γ ⊢§ Δ″) →
             get§ (η′ ∘⊑ η) δ ≡ (get§ η ∘ get§ η′) δ
compget§ η         stop       ∙       = refl
compget§ η         (wk⊑ η′)   (δ , d) = compget§ η η′ δ
compget§ (wk⊑ η)   (lift⊑ η′) (δ , d) = compget§ η η′ δ
compget§ (lift⊑ η) (lift⊑ η′) (δ , d) = (_, d) & compget§ η η′ δ

eqrenget§ : ∀ {Þ k} {Γ Γ′ Δ Δ′ : Fm§ k} (η : Γ ⊑ Γ′) (η′ : Δ ⊑ Δ′) (δ : Þ / Γ ⊢§ Δ′) →
              (get§ η′ ∘ ren§ η) δ ≡ (ren§ η ∘ get§ η′) δ
eqrenget§ η stop       ∙       = refl
eqrenget§ η (wk⊑ η′)   (δ , d) = eqrenget§ η η′ δ
eqrenget§ η (lift⊑ η′) (δ , d) = (_, ren η d) & eqrenget§ η η′ δ

eqwkget§ : ∀ {Þ k} {Γ Δ Δ′ : Fm§ k} {C} (η : Δ ⊑ Δ′) (δ : Þ / Γ ⊢§ Δ′) →
             (get§ (wk⊑ η) ∘ lift§ {C = C}) δ ≡ (wk§ ∘ get§ η) δ
eqwkget§ η δ = eqrenget§ (wk⊑ id⊑) η δ

eqliftget§ : ∀ {Þ k} {Γ Δ Δ′ : Fm§ k} {C} (η : Δ ⊑ Δ′) (δ : Þ / Γ ⊢§ Δ′) →
               (get§ (lift⊑ η) ∘ lift§ {C = C}) δ ≡ (lift§ ∘ get§ η) δ
eqliftget§ η δ = (_, ‵var zero) & eqwkget§ η δ

ridget§ : ∀ {Þ k} {Γ Γ′ : Fm§ k} (η : Γ ⊑ Γ′) → get§ {Þ = Þ} η id§ ≡ var§ η
ridget§ stop      = refl
ridget§ (wk⊑ η)   = eqrenget§ (wk⊑ id⊑) η id§
                  ⋮ wk§ & ridget§ η
ridget§ (lift⊑ η) = (_, ‵var zero)
                      & ( eqrenget§ (wk⊑ id⊑) η id§
                        ⋮ wk§ & ridget§ η
                        )


----------------------------------------------------------------------------------------------------

-- 3.7. derivations: fundamental substitution lemmas

mutual
  eqrensub : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A} (η : Ξ ⊑ Ξ′) (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ ⊢ A) →
               sub (ren§ η σ) d ≡ (ren η ∘ sub σ) d
  eqrensub η σ (‵var i)                = eqrensub∋ η σ i
  eqrensub η σ (‵lam d)                = ‵lam & eqrensublift η σ d
  eqrensub η σ (d ‵$ e)                = _‵$_ & eqrensub η σ d ⊗ eqrensub η σ e
  eqrensub η σ (‵pair d e)             = ‵pair & eqrensub η σ d ⊗ eqrensub η σ e
  eqrensub η σ (‵fst d)                = ‵fst & eqrensub η σ d
  eqrensub η σ (‵snd d)                = ‵snd & eqrensub η σ d
  eqrensub η σ (‵left d)               = ‵left & eqrensub η σ d
  eqrensub η σ (‵right d)              = ‵right & eqrensub η σ d
  eqrensub η σ (‵either c d e)         = ‵either
                                           & eqrensub η σ c
                                           ⊗ eqrensublift η σ d
                                           ⊗ eqrensublift η σ e
  eqrensub η σ (‵all refl d)           = ‵all refl
                                           & ( flip sub d & eqtrenren§ (wk≤ id≤) η σ ⁻¹
                                             ⋮ eqrensub (twk⊑ η) (twk§ σ) d
                                             )
  eqrensub η σ (‵unall t refl d)       = ‵unall t refl & eqrensub η σ d
  eqrensub η σ (‵ex t refl d)          = ‵ex t refl & eqrensub η σ d
  eqrensub η σ (‵letex refl refl d e)  = ‵letex refl refl
                                           & eqrensub η σ d
                                           ⊗ ( (flip sub e ∘ lift§) & eqtrenren§ (wk≤ id≤) η σ ⁻¹
                                             ⋮ eqrensublift (twk⊑ η) (twk§ σ) e
                                             )
  eqrensub η σ (‵abort d)              = ‵abort & eqrensub η σ d
  eqrensub η σ (‵magic d)              = ‵magic & eqrensublift η σ d
  eqrensub η σ ‵refl                   = refl
  eqrensub η σ (‵sym d)                = ‵sym & eqrensub η σ d
  eqrensub η σ (‵trans d e)            = ‵trans & eqrensub η σ d ⊗ eqrensub η σ e
  eqrensub η σ (‵cong f i refl refl d) = ‵cong f i refl refl & eqrensub η σ d
  eqrensub η σ ‵dis                    = refl
  eqrensub η σ (‵inj d)                = ‵inj & eqrensub η σ d
  eqrensub η σ (‵ind refl refl d e)    = ‵ind refl refl & eqrensub η σ d ⊗ eqrensub η σ e
  eqrensub η σ (‵proj i refl)          = refl
  eqrensub η σ (‵comp g φ refl)        = refl
  eqrensub η σ (‵rec f g)              = refl

  eqrensublift : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A B} (η : Ξ ⊑ Ξ′) (σ : Þ / Ξ ⊢§ Γ)
                   (d : Þ / Γ , A ⊢ B) →
                   sub (lift§ (ren§ η σ)) d ≡ (ren (lift⊑ η) ∘ sub (lift§ σ)) d
  eqrensublift η σ d = flip sub d & eqliftren§ η σ ⁻¹
                     ⋮ eqrensub (lift⊑ η) (lift§ σ) d

mutual
  eqsubren : ∀ {Þ k} {Γ Γ′ Ξ : Fm§ k} {A} (σ : Þ / Ξ ⊢§ Γ′) (η : Γ ⊑ Γ′) (d : Þ / Γ ⊢ A) →
               sub (get§ η σ) d ≡ (sub σ ∘ ren η) d
  eqsubren σ η (‵var i)                = eqsubren∋ σ η i
  eqsubren σ η (‵lam d)                = ‵lam & eqsubrenlift σ η d
  eqsubren σ η (d ‵$ e)                = _‵$_ & eqsubren σ η d ⊗ eqsubren σ η e
  eqsubren σ η (‵pair d e)             = ‵pair & eqsubren σ η d ⊗ eqsubren σ η e
  eqsubren σ η (‵fst d)                = ‵fst & eqsubren σ η d
  eqsubren σ η (‵snd d)                = ‵snd & eqsubren σ η d
  eqsubren σ η (‵left d)               = ‵left & eqsubren σ η d
  eqsubren σ η (‵right d)              = ‵right & eqsubren σ η d
  eqsubren σ η (‵either c d e)         = ‵either
                                           & eqsubren σ η c
                                           ⊗ eqsubrenlift σ η d
                                           ⊗ eqsubrenlift σ η e
  eqsubren σ η (‵all refl d)           = ‵all refl
                                           & ( flip sub d & eqtrenget§ (wk≤ id≤) η σ ⁻¹
                                             ⋮ eqsubren (twk§ σ) (twk⊑ η) d
                                             )
  eqsubren σ η (‵unall t refl d)       = ‵unall t refl & eqsubren σ η d
  eqsubren σ η (‵ex t refl d)          = ‵ex t refl & eqsubren σ η d
  eqsubren σ η (‵letex refl refl d e)  = ‵letex refl refl
                                           & eqsubren σ η d
                                           ⊗ ( (flip sub e ∘ lift§) & eqtrenget§ (wk≤ id≤) η σ ⁻¹
                                             ⋮ eqsubrenlift (twk§ σ) (twk⊑ η) e
                                             )
  eqsubren σ η (‵abort d)              = ‵abort & eqsubren σ η d
  eqsubren σ η (‵magic d)              = ‵magic & eqsubrenlift σ η d
  eqsubren σ η ‵refl                   = refl
  eqsubren σ η (‵sym d)                = ‵sym & eqsubren σ η d
  eqsubren σ η (‵trans d e)            = ‵trans & eqsubren σ η d ⊗ eqsubren σ η e
  eqsubren σ η (‵cong f i refl refl d) = ‵cong f i refl refl & eqsubren σ η d
  eqsubren σ η ‵dis                    = refl
  eqsubren σ η (‵inj d)                = ‵inj & eqsubren σ η d
  eqsubren σ η (‵ind refl refl d e)    = ‵ind refl refl & eqsubren σ η d ⊗ eqsubren σ η e
  eqsubren σ η (‵proj i refl)          = refl
  eqsubren σ η (‵comp g φ refl)        = refl
  eqsubren σ η (‵rec f g)              = refl

  eqsubrenlift : ∀ {Þ k} {Γ Γ′ Ξ : Fm§ k} {A B} (σ : Þ / Ξ ⊢§ Γ′) (η : Γ ⊑ Γ′)
                   (d : Þ / Γ , A ⊢ B) →
                   sub (lift§ (get§ η σ)) d ≡ (sub (lift§ σ) ∘ ren (lift⊑ η)) d
  eqsubrenlift σ η d = flip sub d & eqliftget§ η σ ⁻¹
                     ⋮ eqsubren (lift§ σ) (lift⊑ η) d

lidsub : ∀ {Þ k} {Γ : Fm§ k} {A} (d : Þ / Γ ⊢ A) → sub id§ d ≡ d
lidsub (‵var i)                = idsub∋ i
lidsub (‵lam d)                = ‵lam & lidsub d
lidsub (d ‵$ e)                = _‵$_ & lidsub d ⊗ lidsub e
lidsub (‵pair d e)             = ‵pair & lidsub d ⊗ lidsub e
lidsub (‵fst d)                = ‵fst & lidsub d
lidsub (‵snd d)                = ‵snd & lidsub d
lidsub (‵left d)               = ‵left & lidsub d
lidsub (‵right d)              = ‵right & lidsub d
lidsub (‵either c d e)         = ‵either & lidsub c ⊗ lidsub d ⊗ lidsub e
lidsub (‵all refl d)           = ‵all refl
                                   & ( flip sub d & ridtren§ (wk≤ id≤)
                                     ⋮ lidsub d
                                     )
lidsub (‵unall t refl d)       = ‵unall t refl & lidsub d
lidsub (‵ex t refl d)          = ‵ex t refl & lidsub d
lidsub (‵letex refl refl d e)  = ‵letex refl refl
                                    & lidsub d
                                    ⊗ ( (flip sub e ∘ lift§) & ridtren§ (wk≤ id≤)
                                      ⋮ lidsub e
                                      )
lidsub (‵abort d)              = ‵abort & lidsub d
lidsub (‵magic d)              = ‵magic & lidsub d
lidsub ‵refl                   = refl
lidsub (‵sym d)                = ‵sym & lidsub d
lidsub (‵trans d e)            = ‵trans & lidsub d ⊗ lidsub e
lidsub (‵cong f i refl refl d) = ‵cong f i refl refl & lidsub d
lidsub ‵dis                    = refl
lidsub (‵inj d)                = ‵inj & lidsub d
lidsub (‵ind refl refl d e)    = ‵ind refl refl & lidsub d ⊗ lidsub e
lidsub (‵proj i refl)          = refl
lidsub (‵comp g φ refl)        = refl
lidsub (‵rec f g)              = refl


----------------------------------------------------------------------------------------------------

-- TODO: clean this up; avoid heteq?

hlidren§ : ∀ {Þ k} {Γ Γ′ Δ : Fm§ k} (p : Γ ≡ Γ′) (δ : Þ / Γ ⊢§ Δ) → ren§ (cast⊑ p) δ ≅ δ
hlidren§ refl δ = ≡→≅ (lidren§ δ)

hlidget§ : ∀ {Þ k} {Γ Δ Δ′ : Fm§ k} (p : Δ ≡ Δ′) (δ : Þ / Γ ⊢§ Δ′) → get§ (cast⊑ p) δ ≅ δ
hlidget§ refl δ = ≡→≅ (lidget§ δ)

hcomptren∋ : ∀ {k k′ k″} {Γ : Fm§ k} {A} (η′ : k′ ≤ k″) (η : k ≤ k′) (i : Γ ∋ A) →
               tren∋ (η′ ∘≤ η) i ≅ (tren∋ η′ ∘ tren∋ η) i
hcomptren∋ η′ η i = {!!}
-- TODO: this doesn't work without rewriting by comprenFm/comprenFm§
-- hcomptren∋ η′ η zero    = refl
-- hcomptren∋ η′ η (suc i) = suc &′ hcomptren∋ η′ η i

hcomptren : ∀ {Þ k k′ k″} {Γ : Fm§ k} {A} (η′ : k′ ≤ k″) (η : k ≤ k′) (d : Þ / Γ ⊢ A) →
              tren (η′ ∘≤ η) d ≅ (tren η′ ∘ tren η) d
hcomptren η′ η d = {!!}

hcomptren§ : ∀ {Þ k k′ k″} {Γ Δ : Fm§ k} (η′ : k′ ≤ k″) (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
              tren§ (η′ ∘≤ η) δ ≅ (tren§ η′ ∘ tren§ η) δ
hcomptren§ η′ η δ = {!!}
-- TODO: this doesn't work without rewriting by comprenFm/comprenFm§
-- TODO: fix ⊗′ and use instead of ⋮′
-- hcomptren§ η′ η ∙       = refl
-- hcomptren§ η′ η (δ , d) = (_, _) &′ hcomptren§ η′ η δ
--                         ⋮′ (_ ,_) &′ hcomptren η′ η d

-- TODO: rename
huntitled2 : ∀ {Þ k k′ Γ Δ} (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
               get§ (cast⊑ (eqwkrenFm§ η Δ)) ((twk§ ∘ tren§ η) δ) ≅
                 ren§ (cast⊑ (eqwkrenFm§ η Γ)) ((tren§ (lift≤ η) ∘ twk§) δ)
huntitled2 {Γ = Γ} {Δ} η δ =
    begin
      get§ (cast⊑ (eqwkrenFm§ η Δ)) ((twk§ ∘ tren§ η) δ)
    ≅⟨ hlidget§ (eqwkrenFm§ η Δ) ((twk§ ∘ tren§ η) δ) ⟩
      twk§ (tren§ η δ)
    ≅⟨ hcomptren§ (wk≤ id≤) η δ ⁻¹′ ⟩
      tren§ (wk≤ id≤ ∘≤ η) δ
    ≅⟨ (flip tren§ δ ∘ wk≤) &′ ≡→≅ (lid≤ η ⋮ rid≤ η ⁻¹) ⟩
      tren§ (lift≤ η ∘≤ wk≤ id≤) δ
    ≅⟨ hcomptren§ (lift≤ η) (wk≤ id≤) δ ⟩
      (tren§ (lift≤ η) ∘ twk§) δ
    ≅⟨ hlidren§ (eqwkrenFm§ η Γ) ((tren§ (lift≤ η) ∘ twk§) δ) ⁻¹′ ⟩
      ren§ (cast⊑ (eqwkrenFm§ η Γ)) ((tren§ (lift≤ η) ∘ twk§) δ)
    ∎
  where
    open ≅-Reasoning


----------------------------------------------------------------------------------------------------

-- TODO: clean these up

eqtrenlift§ : ∀ {Þ k k′ Γ Δ C} (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
                (lift§ ∘ tren§ η) δ ≡ (tren§ η ∘ lift§ {C = C}) δ
eqtrenlift§ η ∙       = refl
eqtrenlift§ η (δ , d) = (_, ‵var zero)
                        & ( _,_
                              & ((flip ren§ (tren§ η δ) ∘ wk⊑) & ridtren⊑ η ⁻¹)
                              ⊗ (flip ren (tren η d) ∘ wk⊑) & ridtren⊑ η ⁻¹
                          ⋮ eqtrenren§ η (wk⊑ id⊑) (δ , d)
                          )

-- TODO: rename
untitled2 : ∀ {Þ k k′ Γ Δ} (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
              get§ (cast⊑ (eqwkrenFm§ η Δ)) ((twk§ ∘ tren§ η) δ) ≡
                ren§ (cast⊑ (eqwkrenFm§ η Γ)) ((tren§ (lift≤ η) ∘ twk§) δ)
untitled2 η δ = ≅→≡ (huntitled2 η δ)

eqtrensub∋ : ∀ {Þ k k′ Γ Ξ A} (η : k ≤ k′) (σ : Þ / Ξ ⊢§ Γ) (i : Γ ∋ A) →
               (sub∋ (tren§ η σ) ∘ tren∋ η) i ≡ (tren η ∘ sub∋ σ) i
eqtrensub∋ η (σ , d) zero    = refl
eqtrensub∋ η (σ , d) (suc i) = eqtrensub∋ η σ i

mutual
  eqtrensub : ∀ {Þ k k′ Γ Ξ A} (η : k ≤ k′) (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ ⊢ A) →
                (sub (tren§ η σ) ∘ tren η) d ≡ (tren η ∘ sub σ) d
  eqtrensub η σ (‵var i)                = eqtrensub∋ η σ i
  eqtrensub η σ (‵lam d)                = ‵lam & eqtrensublift η σ d
  eqtrensub η σ (d ‵$ e)                = _‵$_ & eqtrensub η σ d ⊗ eqtrensub η σ e
  eqtrensub η σ (‵pair d e)             = ‵pair & eqtrensub η σ d ⊗ eqtrensub η σ e
  eqtrensub η σ (‵fst d)                = ‵fst & eqtrensub η σ d
  eqtrensub η σ (‵snd d)                = ‵snd & eqtrensub η σ d
  eqtrensub η σ (‵left d)               = ‵left & eqtrensub η σ d
  eqtrensub η σ (‵right d)              = ‵right & eqtrensub η σ d
  eqtrensub η σ (‵either c d e)         = ‵either
                                            & eqtrensub η σ c
                                            ⊗ eqtrensublift η σ d
                                            ⊗ eqtrensublift η σ e
  eqtrensub {Γ = Γ} {Ξ} η σ (‵all {A = A} refl d) =
      begin
        (sub (tren§ η σ) ∘ tren η) (‵all refl d)
      ≡⟨⟩
        sub (tren§ η σ) (‵all (eqwkrenFm§ η Γ) (tren (lift≤ η) d))
      ≡⟨ sub (tren§ η σ) & eqall (eqwkrenFm§ η Γ) (tren (lift≤ η) d) ⁻¹ ⟩
        sub (tren§ η σ) (‵all refl (ren (cast⊑ (eqwkrenFm§ η Γ)) (tren (lift≤ η) d)))
      ≡⟨⟩
        ‵all refl (sub (twk§ (tren§ η σ)) (ren (cast⊑ (eqwkrenFm§ η Γ)) (tren (lift≤ η) d)))
      ≡⟨ ‵all refl
          & (begin
              sub (twk§ (tren§ η σ)) (ren (cast⊑ (eqwkrenFm§ η Γ)) (tren (lift≤ η) d))
            ≡⟨ eqsubren (twk§ (tren§ η σ)) (cast⊑ (eqwkrenFm§ η Γ)) (tren (lift≤ η) d) ⁻¹ ⟩
              sub (get§ (cast⊑ (eqwkrenFm§ η Γ)) (twk§ (tren§ η σ))) (tren (lift≤ η) d)
            ≡⟨ flip sub (tren (lift≤ η) d) & untitled2 η σ ⟩
              sub (ren§ (cast⊑ (eqwkrenFm§ η Ξ)) (tren§ (lift≤ η) (twk§ σ))) (tren (lift≤ η) d)
            ≡⟨ eqrensub (cast⊑ (eqwkrenFm§ η Ξ)) (tren§ (lift≤ η) (twk§ σ)) (tren (lift≤ η) d) ⟩
              ren (cast⊑ (eqwkrenFm§ η Ξ)) (sub (tren§ (lift≤ η) (twk§ σ)) (tren (lift≤ η) d))
            ∎)
      ⟩
        ‵all refl
          (ren (cast⊑ (eqwkrenFm§ η Ξ))
            (sub (tren§ (lift≤ η) (twk§ σ)) (tren (lift≤ η) d)))
      ≡⟨ eqall (eqwkrenFm§ η Ξ) ((sub (tren§ (lift≤ η) (twk§ σ)) ∘ tren (lift≤ η)) d) ⟩
        ‵all (eqwkrenFm§ η Ξ)
          ((sub (tren§ (lift≤ η) (twk§ σ)) ∘ tren (lift≤ η)) d)
      ≡⟨ ‵all (eqwkrenFm§ η Ξ) & eqtrensub (lift≤ η) (twk§ σ) d ⟩
        ‵all (eqwkrenFm§ η Ξ) (tren (lift≤ η) (sub (twk§ σ) d))
      ≡⟨⟩
        (tren η ∘ sub σ) (‵all refl d)
      ∎
    where
      open ≡-Reasoning
  eqtrensub η σ (‵unall t refl d)       = ‵unall (renTm η t) (eqrencut0Fm η _ t) & eqtrensub η σ d
  eqtrensub η σ (‵ex t refl d)          = ‵ex (renTm η t) (eqrencut0Fm η _ t) & eqtrensub η σ d
  eqtrensub {Γ = Γ} {Ξ} η σ (‵letex {A = A} {C} refl refl d e) =
      begin
        (sub (tren§ η σ) ∘ tren η) (‵letex refl refl d e)
      ≡⟨⟩
        sub (tren§ η σ)
          (‵letex (eqwkrenFm§ η Γ) (eqwkrenFm η C) (tren η d)
          (tren (lift≤ η) e))
      ≡⟨ sub (tren§ η σ) & eqletex (eqwkrenFm§ η Γ) (eqwkrenFm η C) (tren η d)
           (tren (lift≤ η) e) ⁻¹
      ⟩
        sub (tren§ η σ)
          (‵letex refl (eqwkrenFm η C) (tren η d)
            ((ren (lift⊑ (cast⊑ (eqwkrenFm§ η Γ))) ∘ tren (lift≤ η)) e))
      ≡⟨⟩
        ‵letex refl (eqwkrenFm η C) ((sub (tren§ η σ) ∘ tren η) d)
          ((sub (lift§ (twk§ (tren§ η σ))) ∘
            ren (lift⊑ (cast⊑ (eqwkrenFm§ η Γ))) ∘
            tren (lift≤ η)) e)
      ≡⟨ ‵letex refl (eqwkrenFm η C) ((sub (tren§ η σ) ∘ tren η) d)
           & (begin
             (sub (lift§ ((twk§ ∘ tren§ η) σ)) ∘
               (ren (lift⊑ (cast⊑ (eqwkrenFm§ η Γ))) ∘
               tren (lift≤ η))) e
           ≡⟨ eqsubrenlift ((twk§ ∘ tren§ η) σ) (cast⊑ (eqwkrenFm§ η Γ)) (tren (lift≤ η) e) ⁻¹ ⟩
             (sub (lift§
                 ((get§ (cast⊑ (eqwkrenFm§ η Γ)) ∘
                   (twk§ ∘ tren§ η)) σ)) ∘
               tren (lift≤ η)) e
           ≡⟨ (flip sub (tren (lift≤ η) e) ∘ lift§) & untitled2 η σ ⟩
             (sub (lift§
                 ((ren§ (cast⊑ (eqwkrenFm§ η Ξ)) ∘
                   tren§ (lift≤ η)) (twk§ σ))) ∘
               tren (lift≤ η)) e
           ≡⟨ eqrensublift (cast⊑ (eqwkrenFm§ η Ξ)) (tren§ (lift≤ η) (twk§ σ)) (tren (lift≤ η) e) ⟩
             (ren (lift⊑ (cast⊑ (eqwkrenFm§ η Ξ))) ∘
               (sub (lift§ (tren§ (lift≤ η) (twk§ σ))) ∘
               tren (lift≤ η))) e
           ∎)
      ⟩
        ‵letex refl (eqwkrenFm η C) (sub (tren§ η σ) (tren η d))
          (ren (lift⊑ (cast⊑ (eqwkrenFm§ η Ξ)))
           (sub (lift§ (tren§ (lift≤ η) (twk§ σ))) (tren (lift≤ η) e)))
      ≡⟨ eqletex (eqwkrenFm§ η Ξ) (eqwkrenFm η C) ((sub (tren§ η σ) ∘ tren η) d)
           ((sub (lift§ (tren§ (lift≤ η) (twk§ σ))) ∘ tren (lift≤ η)) e)
      ⟩
        ‵letex (eqwkrenFm§ η Ξ) (eqwkrenFm η C)
          ((sub (tren§ η σ) ∘ tren η) d)
          ((sub (lift§ (tren§ (lift≤ η) (twk§ σ))) ∘ tren (lift≤ η)) e)
      ≡⟨ ‵letex (eqwkrenFm§ η Ξ) (eqwkrenFm η C)
           & eqtrensub η σ d
           ⊗ eqtrensublift (lift≤ η) (twk§ σ) e
      ⟩
        ‵letex (eqwkrenFm§ η Ξ) (eqwkrenFm η C) (tren η (sub σ d))
          (tren (lift≤ η) (sub (lift§ (twk§ σ)) e))
      ≡⟨⟩
        (tren η ∘ sub σ) (‵letex refl refl d e)
      ∎
    where
      open ≡-Reasoning
  eqtrensub η σ (‵abort d)              = ‵abort & eqtrensub η σ d
  eqtrensub η σ (‵magic d)              = ‵magic & eqtrensublift η σ d
  eqtrensub η σ ‵refl                   = refl
  eqtrensub η σ (‵sym d)                = ‵sym & eqtrensub η σ d
  eqtrensub η σ (‵trans d e)            = ‵trans & eqtrensub η σ d ⊗ eqtrensub η σ e
  eqtrensub η σ (‵cong f i refl refl d) = ‵cong f i (eqrenpeekTm η i _) (eqrenpokeTm η i _ _)
                                            & eqtrensub η σ d
  eqtrensub η σ ‵dis                    = refl
  eqtrensub η σ (‵inj d)                = ‵inj & eqtrensub η σ d
  eqtrensub η σ (‵ind refl refl d e)    = ‵ind (eqrencut0Fm η _ 𝟘)
                                              (eqrencut1Fm η _ (𝕊 (‵tvar zero)))
                                            & eqtrensub η σ d ⊗ eqtrensub η σ e
  eqtrensub η σ (‵proj i refl)          = refl
  eqtrensub η σ (‵comp g φ refl)        = refl
  eqtrensub η σ (‵rec f g)              = refl

  -- TODO: rename to eqtrensublift; reverse
  eqtrensublift : ∀ {Þ k k′ Γ Ξ A C} (η : k ≤ k′) (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ , C ⊢ A) →
                    (sub (lift§ (tren§ η σ)) ∘ tren η) d ≡ (tren η ∘ sub (lift§ σ)) d
  eqtrensublift η σ d = flip sub (tren η d) & eqtrenlift§ η σ
                      ⋮ eqtrensub η (lift§ σ) d

-- TODO: rename to eqtrensub§; reverse
eqtrensub§ : ∀ {Þ k k′ Γ Ξ Δ} (η : k ≤ k′) (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
               (sub§ (tren§ η σ) ∘ tren§ η) δ ≡ (tren§ η ∘ sub§ σ) δ
eqtrensub§ η σ ∙       = refl
eqtrensub§ η σ (δ , d) = _,_ & eqtrensub§ η σ δ ⊗ eqtrensub η σ d


----------------------------------------------------------------------------------------------------

-- 3.8. derivations: generic lemmas from RenSubKit2

eqrensub§ : ∀ {Þ k} {Γ Ξ Ξ′ Δ : Fm§ k} (η : Ξ ⊑ Ξ′) (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
              sub§ (ren§ η σ) δ ≡ (ren§ η ∘ sub§ σ) δ
eqrensub§ η σ ∙       = refl
eqrensub§ η σ (δ , d) = _,_ & eqrensub§ η σ δ ⊗ eqrensub η σ d

eqsubren§ : ∀ {Þ k} {Γ Γ′ Ξ Δ : Fm§ k} (σ : Þ / Ξ ⊢§ Γ′) (η : Γ ⊑ Γ′) (δ : Þ / Γ ⊢§ Δ) →
              sub§ (get§ η σ) δ ≡ (sub§ σ ∘ ren§ η) δ
eqsubren§ σ η ∙       = refl
eqsubren§ σ η (δ , d) = _,_ & eqsubren§ σ η δ ⊗ eqsubren σ η d

lidsub§ : ∀ {Þ k} {Γ Δ : Fm§ k} (δ : Þ / Γ ⊢§ Δ) → sub§ id§ δ ≡ δ
lidsub§ ∙       = refl
lidsub§ (δ , d) = _,_ & lidsub§ δ ⊗ lidsub d

eqsub : ∀ {Þ k} {Γ Ξ : Fm§ k} {A B} (σ : Þ / Ξ ⊢§ Γ) (s : Þ / Ξ ⊢ B) (d : Þ / Γ ⊢ A) →
          (sub (σ , s) ∘ wk) d ≡ sub σ d
eqsub σ s d = eqsubren (σ , s) (wk⊑ id⊑) d ⁻¹
            ⋮ flip sub d & lidget§ σ

eqsub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} {B} (σ : Þ / Ξ ⊢§ Γ) (s : Þ / Ξ ⊢ B) (δ : Þ / Γ ⊢§ Δ) →
           (sub§ (σ , s) ∘ wk§) δ ≡ sub§ σ δ
eqsub§ σ s ∙       = refl
eqsub§ σ s (δ , d) = _,_ & eqsub§ σ s δ ⊗ eqsub σ s d

eqwksub : ∀ {Þ k} {Γ Ξ : Fm§ k} {A C} (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ ⊢ A) →
            (sub (lift§ σ) ∘ wk {C = C}) d ≡ (wk ∘ sub σ) d
eqwksub σ d = eqsubren (lift§ σ) (wk⊑ id⊑) d ⁻¹
            ⋮ flip sub d
                & ( eqwkget§ id⊑ σ
                  ⋮ wk§ & lidget§ σ
                  )
            ⋮ eqrensub (wk⊑ id⊑) σ d

eqwksub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} {C} (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
             (sub§ (lift§ σ) ∘ wk§ {C = C}) δ ≡ (wk§ ∘ sub§ σ) δ
eqwksub§ σ ∙       = refl
eqwksub§ σ (δ , d) = _,_ & eqwksub§ σ δ ⊗ eqwksub σ d

eqliftsub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} {C} (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
               (sub§ (lift§ σ) ∘ lift§ {C = C}) δ ≡ (lift§ ∘ sub§ σ) δ
eqliftsub§ σ δ = _,_ & eqwksub§ σ δ ⊗ ridsub (lift§ σ) zero

ridsub§ : ∀ {Þ k} {Γ Ξ : Fm§ k} (σ : Þ / Ξ ⊢§ Γ) → sub§ σ id§ ≡ σ
ridsub§ ∙       = refl
ridsub§ (σ , s) = _,_
                    & ( eqsub§ σ s id§
                      ⋮ ridsub§ σ
                      )
                    ⊗ ridsub (σ , s) zero


----------------------------------------------------------------------------------------------------

-- 3.9. derivations: more fundamental substitution lemmas

mutual
  compsub : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ ⊢ A) →
              sub (sub§ σ′ σ) d ≡ (sub σ′ ∘ sub σ) d

  compsub σ′ σ (‵var i)                = compsub∋ σ′ σ i
  compsub σ′ σ (‵lam d)                = ‵lam & compsublift σ′ σ d
  compsub σ′ σ (d ‵$ e)                = _‵$_ & compsub σ′ σ d ⊗ compsub σ′ σ e
  compsub σ′ σ (‵pair d e)             = ‵pair & compsub σ′ σ d ⊗ compsub σ′ σ e
  compsub σ′ σ (‵fst d)                = ‵fst & compsub σ′ σ d
  compsub σ′ σ (‵snd d)                = ‵snd & compsub σ′ σ d
  compsub σ′ σ (‵left d)               = ‵left & compsub σ′ σ d
  compsub σ′ σ (‵right d)              = ‵right & compsub σ′ σ d
  compsub σ′ σ (‵either c d e)         = ‵either
                                           & compsub σ′ σ c
                                           ⊗ compsublift σ′ σ d
                                           ⊗ compsublift σ′ σ e
  compsub σ′ σ (‵all refl d)           = ‵all refl
                                           & ( flip sub d & eqtrensub§ (wk≤ id≤) σ′ σ ⁻¹
                                             ⋮ compsub (twk§ σ′) (twk§ σ) d
                                             )
  compsub σ′ σ (‵unall t refl d)       = ‵unall t refl & compsub σ′ σ d
  compsub σ′ σ (‵ex t refl d)          = ‵ex t refl & compsub σ′ σ d
  compsub σ′ σ (‵letex refl refl d e)  = ‵letex refl refl
                                           & compsub σ′ σ d
                                           ⊗ ( (flip sub e ∘ lift§) & eqtrensub§ (wk≤ id≤) σ′ σ ⁻¹
                                             ⋮ compsublift (twk§ σ′) (twk§ σ) e
                                             )
  compsub σ′ σ (‵abort d)              = ‵abort & compsub σ′ σ d
  compsub σ′ σ (‵magic d)              = ‵magic & compsublift σ′ σ d
  compsub σ′ σ ‵refl                   = refl
  compsub σ′ σ (‵sym d)                = ‵sym & compsub σ′ σ d
  compsub σ′ σ (‵trans d e)            = ‵trans & compsub σ′ σ d ⊗ compsub σ′ σ e
  compsub σ′ σ (‵cong f i refl refl d) = ‵cong f i refl refl & compsub σ′ σ d
  compsub σ′ σ ‵dis                    = refl
  compsub σ′ σ (‵inj d)                = ‵inj & compsub σ′ σ d
  compsub σ′ σ (‵ind refl refl d e)    = ‵ind refl refl & compsub σ′ σ d ⊗ compsub σ′ σ e
  compsub σ′ σ (‵proj i refl)          = refl
  compsub σ′ σ (‵comp g φ refl)        = refl
  compsub σ′ σ (‵rec f g)              = refl

  compsublift : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A B} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ)
                  (d : Þ / Γ , A ⊢ B) →
                  sub (lift§ (sub§ σ′ σ)) d ≡ (sub (lift§ σ′) ∘ sub (lift§ σ)) d
  compsublift σ′ σ d = flip sub d & eqliftsub§ σ′ σ ⁻¹
                     ⋮ compsub (lift§ σ′) (lift§ σ) d


----------------------------------------------------------------------------------------------------

-- 3.10. derivations: generic lemmas from RenSubKit3

asssub§ : ∀ {Þ k} {Γ Ξ Ξ′ Δ : Fm§ k} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
            sub§ (sub§ σ′ σ) δ ≡ (sub§ σ′ ∘ sub§ σ) δ
asssub§ σ′ σ ∙       = refl
asssub§ σ′ σ (δ , d) = _,_ & asssub§ σ′ σ δ ⊗ compsub σ′ σ d

eqrencut : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A B} (η : Γ ⊑ Γ′) (d : Þ / Γ , A ⊢ B) (s : Þ / Γ ⊢ A) →
             ren (lift⊑ η) d [ ren η s /0] ≡ ren η (d [ s /0])
eqrencut η d s = eqsubren (id§ , ren η s) (lift⊑ η) d ⁻¹
               ⋮ (flip sub d ∘ (_, ren η s))
                   & ( ridget§ η
                     ⋮ ridren§ η ⁻¹
                     )
               ⋮ eqrensub η (id§ , s) d

eqsubcut : ∀ {Þ k} {Γ Ξ : Fm§ k} {A B} (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ , A ⊢ B) (s : Þ / Γ ⊢ A) →
             sub (lift§ σ) d [ sub σ s /0] ≡ sub σ (d [ s /0])
eqsubcut σ d s = compsub (id§ , sub σ s) (lift§ σ) d ⁻¹
               ⋮ flip sub d
                   & ( _,_
                         & ( eqsubren§ (id§ , sub σ s) (wk⊑ id⊑) σ ⁻¹
                           ⋮ flip sub§ σ & lidget§ id§
                           ⋮ lidsub§ σ
                           ⋮ ridsub§ σ ⁻¹
                           )
                         ⊗ ridsub (id§ , sub σ s) zero
                     )
               ⋮ compsub σ (id§ , s) d


----------------------------------------------------------------------------------------------------

-- 4.0. various things

⊃id : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A ‵⊃ A
⊃id = ‵lam 0

det : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ A ‵⊃ B → Þ / Γ , A ⊢ B
det d = wk d ‵$ 0

⊃exch : ∀ {Þ k} {Γ : Fm§ k} {A B C} → Þ / Γ ⊢ (A ‵⊃ B ‵⊃ C) ‵⊃ B ‵⊃ A ‵⊃ C
⊃exch = ‵lam (‵lam (‵lam ((2 ‵$ 0) ‵$ 1)))

exch : ∀ {Þ k} {Γ : Fm§ k} {A B C} → Þ / Γ , B , A ⊢ C → Þ / Γ , A , B ⊢ C
exch d = det (det (⊃exch ‵$ ‵lam (‵lam d)))

abort : ∀ {Þ k} {Γ : Fm§ k} {C} → Þ / Γ ⊢ ‵⊥ → Þ / Γ ⊢ C
abort {Þ = HA} d = ‵abort d
abort {Þ = PA} d = ‵magic (wk d)


----------------------------------------------------------------------------------------------------

-- 4.1. equational reasoning with object-level equality predicate
-- TODO: uniform notation with _⁻¹ and _⋮_?

module _ {Þ k} {Γ : Fm§ k} where
  ≡→= : ∀ {t u} → t ≡ u → Þ / Γ ⊢ t ‵= u
  ≡→= refl = ‵refl

module =-Reasoning {Þ k} {Γ : Fm§ k} where
  infix  3 _∎
  infixr 2 _=⟨⟩_ _=⟨_⟩_ _=⟨_⟩⁻¹_ _≡⟨_⟩_ _≡⟨_⟩⁻¹_
  infix  1 begin_

  begin_ : ∀ {t u} → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ t ‵= u
  begin d = d

  _=⟨⟩_ : ∀ t {u} → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ t ‵= u
  t =⟨⟩ d = d

  _=⟨_⟩_ : ∀ s {t u} → Þ / Γ ⊢ s ‵= t → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ s ‵= u
  s =⟨ d ⟩ e = ‵trans d e

  _=⟨_⟩⁻¹_ : ∀ s {t u} → Þ / Γ ⊢ t ‵= s → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ s ‵= u
  s =⟨ d ⟩⁻¹ e = ‵trans (‵sym d) e

  _≡⟨_⟩_ : ∀ s {t u} → s ≡ t → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ s ‵= u
  s ≡⟨ d ⟩ e = ‵trans (≡→= d) e

  _≡⟨_⟩⁻¹_ : ∀ s {t u} → t ≡ s → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ s ‵= u
  s ≡⟨ d ⟩⁻¹ e = ‵trans (≡→= (d ⁻¹)) e

  _∎ : ∀ t → Þ / Γ ⊢ t ‵= t
  t ∎ = ‵refl


----------------------------------------------------------------------------------------------------

-- 4.2. equational reasoning with object-level logical equivalence
-- TODO: uniform notation with _⁻¹ and _⋮_?

module _ {Þ k} {Γ : Fm§ k} where
  ⫗refl : ∀ {A} → Þ / Γ ⊢ A ‵⫗ A
  ⫗refl = ‵pair ⊃id ⊃id

  ⫗sym : ∀ {A B} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ B ‵⫗ A
  ⫗sym d = ‵pair (‵snd d) (‵fst d)

  ⫗trans : ∀ {A B C} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ B ‵⫗ C → Þ / Γ ⊢ A ‵⫗ C
  ⫗trans d e = ‵pair
                  (‵lam
                    (‵fst (wk e) ‵$ ‵fst (wk d) ‵$ 0))
                  (‵lam
                    (‵snd (wk d) ‵$ ‵snd (wk e) ‵$ 0))

  cong⊃ : ∀ {A A′ B B′} → Þ / Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ B ‵⫗ B′ →
            Þ / Γ ⊢ (A ‵⊃ B) ‵⫗ (A′ ‵⊃ B′)
  cong⊃ d e = ‵pair
                (‵lam (‵lam
                  (‵fst (wk (wk e)) ‵$ 1 ‵$ ‵snd (wk (wk d)) ‵$ 0)))
                (‵lam (‵lam
                  (‵snd (wk (wk e)) ‵$ 1 ‵$ ‵fst (wk (wk d)) ‵$ 0)))

  cong∧ : ∀ {A A′ B B′} → Þ / Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ B ‵⫗ B′ →
            Þ / Γ ⊢ A ‵∧ B ‵⫗ A′ ‵∧ B′
  cong∧ d e = ‵pair
                (‵lam (‵pair
                  (‵fst (wk d) ‵$ ‵fst 0)
                  (‵fst (wk e) ‵$ ‵snd 0)))
                (‵lam (‵pair
                  (‵snd (wk d) ‵$ ‵fst 0)
                  (‵snd (wk e) ‵$ ‵snd 0)))

  cong∨ : ∀ {A A′ B B′} → Þ / Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ B ‵⫗ B′ →
            Þ / Γ ⊢ A ‵∨ B ‵⫗ A′ ‵∨ B′
  cong∨ d e = ‵pair
                (‵lam (‵either 0
                  (‵left (‵fst (wk (wk d)) ‵$ 0))
                  (‵right (‵fst (wk (wk e)) ‵$ 0))))
                (‵lam (‵either 0
                  (‵left (‵snd (wk (wk d)) ‵$ 0))
                  (‵right (‵snd (wk (wk e)) ‵$ 0))))

  cong∀ : ∀ {A A′} → Þ / wkFm§ Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ ‵∀ A ‵⫗ ‵∀ A′
  cong∀ d = ‵pair
              (‵lam
                (‵all refl (ren (twk⊑ (wk⊑ id⊑)) (‵fst d) ‵$ ‵unall (‵tvar 0) idcutFm 0)))
              (‵lam
                (‵all refl (ren (twk⊑ (wk⊑ id⊑)) (‵snd d) ‵$ ‵unall (‵tvar 0) idcutFm 0)))

  cong∃ : ∀ {A A′} → Þ / wkFm§ Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ ‵∃ A ‵⫗ ‵∃ A′
  cong∃ d = ‵pair
              (‵lam (‵letex refl refl 0
                (‵ex (‵tvar 0) idcutFm (‵fst (wk (wk d)) ‵$ 0))))
              (‵lam (‵letex refl refl 0
                (‵ex (‵tvar 0) idcutFm (‵snd (wk (wk d)) ‵$ 0))))

  ≡→⫗ : ∀ {A B} → A ≡ B → Þ / Γ ⊢ A ‵⫗ B
  ≡→⫗ refl = ⫗refl

module ⫗-Reasoning {Þ k} {Γ : Fm§ k} where
  infix  3 _∎
  infixr 2 _⫗⟨⟩_ _⫗⟨_⟩_ _⫗⟨_⟩⁻¹_ _≡⟨_⟩_ _≡⟨_⟩⁻¹_
  infix  1 begin_

  begin_ : ∀ {A B} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ A ‵⫗ B
  begin d = d

  _⫗⟨⟩_ : ∀ A {B} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ A ‵⫗ B
  A ⫗⟨⟩ d = d

  _⫗⟨_⟩_ : ∀ A {B C} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ B ‵⫗ C → Þ / Γ ⊢ A ‵⫗ C
  A ⫗⟨ d ⟩ e = ⫗trans d e

  _⫗⟨_⟩⁻¹_ : ∀ A {B C} → Þ / Γ ⊢ B ‵⫗ A → Þ / Γ ⊢ B ‵⫗ C → Þ / Γ ⊢ A ‵⫗ C
  A ⫗⟨ d ⟩⁻¹ e = ⫗trans (⫗sym d) e

  _≡⟨_⟩_ : ∀ A {B C} → A ≡ B → Þ / Γ ⊢ B ‵⫗ C → Þ / Γ ⊢ A ‵⫗ C
  A ≡⟨ d ⟩ e = ⫗trans (≡→⫗ d) e

  _≡⟨_⟩⁻¹_ : ∀ A {B C} → B ≡ A → Þ / Γ ⊢ B ‵⫗ C → Þ / Γ ⊢ A ‵⫗ C
  A ≡⟨ d ⟩⁻¹ e = ⫗trans (≡→⫗ (d ⁻¹)) e

  _∎ : ∀ A → Þ / Γ ⊢ A ‵⫗ A
  A ∎ = ⫗refl


----------------------------------------------------------------------------------------------------

-- 4.3. object-level continuation/double negation monad/applicative/functor
-- ⊃-prefixed versions use object-level implication
-- unprefixed versions use  object-level equivalence, for use in ⫗-reasoning, or
--   meta-level implication, for general ease of use
-- TODO: laws?

⊃return : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A ‵⊃ ‵¬ ‵¬ A
⊃return = ‵lam (‵lam (0 ‵$ 1))

return : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A → Þ / Γ ⊢ ‵¬ ‵¬ A
return d = ⊃return ‵$ d

⊃bind : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ ‵¬ ‵¬ A ‵⊃ (A ‵⊃ ‵¬ ‵¬ B) ‵⊃ ‵¬ ‵¬ B
⊃bind = ‵lam (‵lam (‵lam (2 ‵$ ‵lam ((2 ‵$ 0) ‵$ 1))))

infixl 1 _>>=_
_>>=_ : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ ‵¬ ‵¬ A → Þ / Γ ⊢ A ‵⊃ ‵¬ ‵¬ B → Þ / Γ ⊢ ‵¬ ‵¬ B
d >>= e = (⊃bind ‵$ d) ‵$ e

⊃join : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ ‵¬ ‵¬ ‵¬ ‵¬ A ‵⊃ ‵¬ ‵¬ A
⊃join = ‵lam (0 >>= ⊃id)

join : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ ‵¬ ‵¬ ‵¬ ‵¬ A → Þ / Γ ⊢ ‵¬ ‵¬ A
join d = ⊃join ‵$ d

⊃apply : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ ‵¬ ‵¬ (A ‵⊃ B) ‵⊃ ‵¬ ‵¬ A ‵⊃ ‵¬ ‵¬ B
⊃apply = ‵lam (‵lam (1 >>= ‵lam (1 >>= ‵lam (return (1 ‵$ 0)))))

infixl 4 _⊛_
_⊛_ : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ ‵¬ ‵¬ (A ‵⊃ B) → Þ / Γ ⊢ ‵¬ ‵¬ A → Þ / Γ ⊢ ‵¬ ‵¬ B
d ⊛ e = d >>= ‵lam (wk e >>= ‵lam (return (1 ‵$ 0)))

⊃map : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ (A ‵⊃ B) ‵⊃ ‵¬ ‵¬ A ‵⊃ ‵¬ ‵¬ B
⊃map = ‵lam (‵lam (return 1 ⊛ 0))

infixl 4 _<$>_
_<$>_ : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ A ‵⊃ B → Þ / Γ ⊢ ‵¬ ‵¬ A → Þ / Γ ⊢ ‵¬ ‵¬ B
d <$> e = (⊃map ‵$ d) ‵$ e

dnem : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ ‵¬ ‵¬ (A ‵∨ ‵¬ A)
dnem = ‵lam (0 ‵$ ‵right (‵lam (1 ‵$ ‵left 0)))


----------------------------------------------------------------------------------------------------

-- 4.4. object-level extended middle

⊃dne : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ ‵¬ ‵¬ A ‵⊃ A
⊃dne = ‵lam (‵magic (1 ‵$ 0))

dne : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ ‵¬ ‵¬ A → PA / Γ ⊢ A
dne d = ⊃dne ‵$ d

dn : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ ‵¬ ‵¬ A ‵⫗ A
dn = ‵pair ⊃dne ⊃return

em : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ A ‵∨ ‵¬ A
em = dne dnem


----------------------------------------------------------------------------------------------------

-- 4.5. object-level de Morgan’s laws

-- NOTE: constructive
module _ {Þ k} {Γ : Fm§ k} where
  ⊃pdm1a : ∀ {A B} → Þ / Γ ⊢ ‵¬ A ‵∧ ‵¬ B ‵⊃ ‵¬ (A ‵∨ B)
  ⊃pdm1a = ‵lam (‵lam (‵either 0
             (‵fst 2 ‵$ 0)
             (‵snd 2 ‵$ 0)))

  ⊃qdm1a : ∀ {A} → Þ / Γ ⊢ ‵∀ ‵¬ A ‵⊃ ‵¬ (‵∃ A)
  ⊃qdm1a = ‵lam (‵lam (‵letex refl refl 0
             (‵unall (‵tvar 0) idcutFm 2 ‵$ 0)))

  ⊃npdm1a : ∀ {A B} → Þ / Γ ⊢ A ‵∧ B ‵⊃ ‵¬ (‵¬ A ‵∨ ‵¬ B)
  ⊃npdm1a = ‵lam (‵lam (abort (‵either 0
              (0 ‵$ ‵fst 2)
              (0 ‵$ ‵snd 2))))

  ⊃nqdm1a : ∀ {A} → Þ / Γ ⊢ ‵∀ A ‵⊃ ‵¬ (‵∃ ‵¬ A)
  ⊃nqdm1a = ‵lam (‵lam (abort (‵letex refl refl 0
              (0 ‵$ ‵unall (‵tvar 0) idcutFm 2))))

  ⊃pdm2a : ∀ {A B} → Þ / Γ ⊢ ‵¬ A ‵∨ ‵¬ B ‵⊃ ‵¬ (A ‵∧ B)
  ⊃pdm2a = ‵lam (‵lam (‵either 1
             (0 ‵$ ‵fst 1)
             (0 ‵$ ‵snd 1)))

  ⊃qdm2a : ∀ {A} → Þ / Γ ⊢ ‵∃ ‵¬ A ‵⊃ ‵¬ (‵∀ A)
  ⊃qdm2a = ‵lam (‵lam (‵letex refl refl 1
             (0 ‵$ ‵unall (‵tvar 0) idcutFm 1)))

  ⊃npdm2a : ∀ {A B} → Þ / Γ ⊢ A ‵∨ B ‵⊃ ‵¬ (‵¬ A ‵∧ ‵¬ B)
  ⊃npdm2a = ‵lam (‵lam (abort (‵either 1
              (‵fst 1 ‵$ 0)
              (‵snd 1 ‵$ 0))))

  ⊃nqdm2a : ∀ {A} → Þ / Γ ⊢ ‵∃ A ‵⊃ ‵¬ (‵∀ ‵¬ A)
  ⊃nqdm2a = ‵lam (‵lam (abort (‵letex refl refl 1
              (‵unall (‵tvar 0) idcutFm 1 ‵$ 0))))

  ⊃pdm1b : ∀ {A B} → Þ / Γ ⊢ ‵¬ (A ‵∨ B) ‵⊃ ‵¬ A ‵∧ ‵¬ B
  ⊃pdm1b = ‵lam (‵pair
             (‵lam (1 ‵$ ‵left 0))
             (‵lam (1 ‵$ ‵right 0)))

  ⊃qdm1b : ∀ {A} → Þ / Γ ⊢ ‵¬ (‵∃ A) ‵⊃ ‵∀ ‵¬ A
  ⊃qdm1b = ‵lam (‵all refl (‵lam
             (1 ‵$ ‵ex (‵tvar 0) idcutFm 0)))

  pdm1 : ∀ {A B} → Þ / Γ ⊢ ‵¬ A ‵∧ ‵¬ B ‵⫗ ‵¬ (A ‵∨ B)
  pdm1 = ‵pair ⊃pdm1a ⊃pdm1b

  qdm1 : ∀ {A} → Þ / Γ ⊢ ‵∀ ‵¬ A ‵⫗ ‵¬ (‵∃ A)
  qdm1 = ‵pair ⊃qdm1a ⊃qdm1b

-- NOTE: non-constructive
module _ {k} {Γ : Fm§ k} where
  ⊃npdm1b : ∀ {A B} → PA / Γ ⊢ ‵¬ (‵¬ A ‵∨ ‵¬ B) ‵⊃ A ‵∧ B
  ⊃npdm1b = ‵lam (‵pair
              (‵either em
                0
                (abort (1 ‵$ ‵left 0)))
              (‵either em
                0
                (abort (1 ‵$ ‵right 0))))

  ⊃nqdm1b : ∀ {A} → PA / Γ ⊢ ‵¬ (‵∃ ‵¬ A) ‵⊃ ‵∀ A
  ⊃nqdm1b = ‵lam (‵all refl (‵either em
              0
              (abort (1 ‵$ ‵ex (‵tvar 0) idcutFm 0))))

  ⊃pdm2b : ∀ {A B} → PA / Γ ⊢ ‵¬ (A ‵∧ B) ‵⊃ ‵¬ A ‵∨ ‵¬ B
  ⊃pdm2b = ‵lam (‵either em
             (‵either em
               (abort (2 ‵$ ‵pair 1 0))
               (‵right 0))
             (‵left 0))

  ⊃qdm2b : ∀ {A} → PA / Γ ⊢ ‵¬ (‵∀ A) ‵⊃ ‵∃ ‵¬ A
  ⊃qdm2b = ‵lam (‵either em
             0
             (abort (1 ‵$ wk (wk ⊃nqdm1b) ‵$ 0)))

  ⊃npdm2b : ∀ {A B} → PA / Γ ⊢ ‵¬ (‵¬ A ‵∧ ‵¬ B) ‵⊃ A ‵∨ B
  ⊃npdm2b = ‵lam (‵either em
              (‵left 0)
              (‵either em
                (‵right 0)
                (abort (2 ‵$ ‵pair 1 0))))

  ⊃nqdm2b : ∀ {A} → PA / Γ ⊢ ‵¬ (‵∀ ‵¬ A) ‵⊃ ‵∃ A
  ⊃nqdm2b = ‵lam (‵either em
              0
              (abort (1 ‵$ wk ⊃qdm1b ‵$ 0)))

  npdm1 : ∀ {A B} → PA / Γ ⊢ A ‵∧ B ‵⫗ ‵¬ (‵¬ A ‵∨ ‵¬ B)
  npdm1 = ‵pair ⊃npdm1a ⊃npdm1b

  nqdm1 : ∀ {A} → PA / Γ ⊢ ‵∀ A ‵⫗ ‵¬ (‵∃ ‵¬ A)
  nqdm1 = ‵pair ⊃nqdm1a ⊃nqdm1b

  pdm2 : ∀ {A B} → PA / Γ ⊢ ‵¬ A ‵∨ ‵¬ B ‵⫗ ‵¬ (A ‵∧ B)
  pdm2 = ‵pair ⊃pdm2a ⊃pdm2b

  qdm2 : ∀ {A} → PA / Γ ⊢ ‵∃ ‵¬ A ‵⫗ ‵¬ (‵∀ A)
  qdm2 = ‵pair ⊃qdm2a ⊃qdm2b

  npdm2 : ∀ {A B} → PA / Γ ⊢ A ‵∨ B ‵⫗ ‵¬ (‵¬ A ‵∧ ‵¬ B)
  npdm2 = ‵pair ⊃npdm2a ⊃npdm2b

  nqdm2 : ∀ {A} → PA / Γ ⊢ ‵∃ A ‵⫗ ‵¬ (‵∀ ‵¬ A)
  nqdm2 = ‵pair ⊃nqdm2a ⊃nqdm2b


----------------------------------------------------------------------------------------------------

-- TODO: 4.6. other object-level non-constructive tautologies

{-A     B    ¬A    ¬B    A∧B   A∨B   A⊃B   A⫗B ¬A∧B  ¬A∨B  ¬A⊃B  ¬A⫗B  A∧¬B  A∨¬B  A⊃¬B A⫗¬B
----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- -----
  0     0     1     1     0     0     1     1     0     1     0     0     0     1     1     0
  0     1     1     0     0     1     1     0     1     1     1     1     0     0     1     1
  1     0     0     1     0     1     0     0     0     0     1     1     1     1     1     1
  1     1     0     0     1     1     1     1     0     1     1     0     0     1     0     0-}

-- module _ where
--   tau1 : ∀ {A B} → PA / Γ ⊢ A ‵⊃ B ‵⫗ ‵¬ A ‵∨ B
--   tau1 = {!!}
--
--   tau2 : ∀ {A B} → PA / Γ ⊢ (‵¬ A ‵⫗ B) ‵⫗ (A ‵⫗ ‵¬ B)
--   tau2 = {!!}


----------------------------------------------------------------------------------------------------

-- 5.1. statement of theorem 1

-- TODO: state theorem 1


----------------------------------------------------------------------------------------------------

-- 5.2. lemma 2

lem2 : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A → PA / Γ ⊢ A
lem2 (‵var i)                = ‵var i
lem2 (‵lam d)                = ‵lam (lem2 d)
lem2 (d ‵$ e)                = lem2 d ‵$ lem2 e
lem2 (‵pair d e)             = ‵pair (lem2 d) (lem2 e)
lem2 (‵fst d)                = ‵fst (lem2 d)
lem2 (‵snd d)                = ‵snd (lem2 d)
lem2 (‵left d)               = ‵left (lem2 d)
lem2 (‵right d)              = ‵right (lem2 d)
lem2 (‵either c d e)         = ‵either (lem2 c) (lem2 d) (lem2 e)
lem2 (‵all refl d)           = ‵all refl (lem2 d)
lem2 (‵unall t refl d)       = ‵unall t refl (lem2 d)
lem2 (‵ex t refl d)          = ‵ex t refl (lem2 d)
lem2 (‵letex refl refl d e)  = ‵letex refl refl (lem2 d) (lem2 e)
lem2 (‵abort d)              = abort (lem2 d)
lem2 (‵magic d)              = ‵magic (lem2 d)
lem2 ‵refl                   = ‵refl
lem2 (‵sym d)                = ‵sym (lem2 d)
lem2 (‵trans d e)            = ‵trans (lem2 d) (lem2 e)
lem2 (‵cong f i refl refl d) = ‵cong f i refl refl (lem2 d)
lem2 ‵dis                    = ‵dis
lem2 (‵inj d)                = ‵inj (lem2 d)
lem2 (‵ind refl refl d e)    = ‵ind refl refl (lem2 d) (lem2 e)
lem2 (‵proj i refl)          = ‵proj i refl
lem2 (‵comp g φ refl)        = ‵comp g φ refl
lem2 (‵rec f g)              = ‵rec f g


----------------------------------------------------------------------------------------------------

-- 5.3. quantifier-free formulas

data IsQFree {k} : Fm k → Set where
  _‵⊃_ : ∀ {A B} (p : IsQFree A) (q : IsQFree B) → IsQFree (A ‵⊃ B)
  _‵∧_ : ∀ {A B} (p : IsQFree A) (q : IsQFree B) → IsQFree (A ‵∧ B)
  _‵∨_ : ∀ {A B} (p : IsQFree A) (q : IsQFree B) → IsQFree (A ‵∨ B)
  ‵⊥  : IsQFree ‵⊥
  _‵=_ : ∀ {t u} → IsQFree (t ‵= u)

-- TODO: lemma 3
-- module _ where
--   open =-Reasoning
--
--   lem3 : ∀ {Þ k} {Γ : Fm§ k} (A : Fm k) {{_ : IsQFree A}} → Σ (Prim k) λ f →
--            Þ / Γ ⊢ A ‵⫗ ‵fun f (tab ‵var) ‵= 𝟘
--   lem3 (A ‵⊃ B) = {!!}
--   lem3 (A ‵∧ B) = {!!}
--   lem3 (A ‵∨ B) = {!!}
--   lem3 ‵⊥      = sig
--                     (ƒconst 1)
--                     (‵pair
--                       (‵lam (abort 0))
--                       (‵lam (‵dis ‵$ (‵lam goal) ‵$ 0)))
--                   where
--                     goal : ∀ {Þ k} {Γ : Fm§ k} →
--                              Þ / Γ , ‵fun (ƒconst 1) (tab ‵var) ‵= 𝟘 ⊢ 𝕊 𝟘 ‵= 𝟘
--                     goal = begin
--                              𝕊 𝟘
--                            =⟨⟩
--                              ‵fun suc (∙ , ‵fun zero ∙)
--                            =⟨ ‵cong suc zero refl refl
--                                  (begin
--                                    ‵fun zero ∙
--                                  =˘⟨ ‵comp zero ∙ refl ⟩
--                                    ‵fun (comp zero ∙) (tab ‵var)
--                                  ∎)
--                                ⟩
--                              ‵fun suc (∙ , ‵fun (comp zero ∙) (tab ‵var))
--                            =˘⟨ ‵comp suc ((∙ , comp zero ∙)) refl ⟩
--                              ‵fun (comp suc (∙ , comp zero ∙)) (tab ‵var)
--                            =⟨⟩
--                              ‵fun (ƒconst 1) (tab ‵var)
--                            =⟨ 0 ⟩
--                              𝟘
--                            ∎
--   lem3 (t ‵= u) = {!!}


----------------------------------------------------------------------------------------------------

-- 5.4. TODO: section title

-- TODO: definition of Π⁰₂
-- TODO: lemma 4


----------------------------------------------------------------------------------------------------

-- 5.5. double negation translation

_° : ∀ {k} → Fm k → Fm k
(A ‵⊃ B) ° = A ° ‵⊃ B °
(A ‵∧ B) ° = A ° ‵∧ B °
(A ‵∨ B) ° = ‵¬ ‵¬ (A ° ‵∨ B °)
(‵∀ A)   ° = ‵∀ A °
(‵∃ A)   ° = ‵¬ ‵¬ (‵∃ A °)
‵⊥      ° = ‵⊥
(t ‵= u) ° = ‵¬ ‵¬ (t ‵= u)

_°§ : ∀ {k} → Fm§ k → Fm§ k
∙       °§ = ∙
(Γ , A) °§ = Γ °§ , A °

-- TODO: interactions between DNT and renaming/substitution
module _ where
  postulate
    TODO2 : ∀ {k} {A : Fm (suc k)} {t} → A [ t /0]Fm ° ≡ A ° [ t /0]Fm
  -- TODO2 = {!!}

  postulate
    TODO3 : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / wkFm§ Γ °§ ⊢ A → Þ / wkFm§ (Γ °§) ⊢ A
  -- TODO3 = {!!}

  postulate
    TODO4 : ∀ {Þ k} {Γ : Fm§ k} {A t} → Þ / Γ ⊢ A [ t /0]Fm ° → Þ / Γ ⊢ A ° [ t /0]Fm
  -- TODO4 = {!!}

  postulate
    TODO5 : ∀ {Þ k} {Γ : Fm§ k} {A t} → Þ / Γ ⊢ ‵∀ (A ° ‵⊃ wkFm A [ t /1]Fm °) →
              Þ / Γ ⊢ ‵∀ (A ° ‵⊃ wkFm (A °) [ t /1]Fm)
  -- TODO5 = {!!}

  postulate
    TODO6 : ∀ {Þ k} {Γ : Fm§ k} {A C} → Þ / wkFm§ Γ °§ , A ° ⊢ wkFm C ° →
              Þ / wkFm§ (Γ °§) , A ° ⊢ wkFm (C °)
  -- TODO6 = {!!}

-- TODO: lemma 5
module _ where
  open ⫗-Reasoning

  lem5-1 : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ A ° ‵⫗ A
  lem5-1 {A = A ‵⊃ B} = cong⊃ lem5-1 lem5-1
  lem5-1 {A = A ‵∧ B} = cong∧ lem5-1 lem5-1
  lem5-1 {A = A ‵∨ B} = begin
                          (A ‵∨ B) °
                        ⫗⟨ dn ⟩
                          A ° ‵∨ B °
                        ⫗⟨ cong∨ lem5-1 lem5-1 ⟩
                          A ‵∨ B
                        ∎
  lem5-1 {A = ‵∀ A}   = cong∀ lem5-1
  lem5-1 {A = ‵∃ A}   = begin
                          (‵∃ A) °
                        ⫗⟨ dn ⟩
                          ‵∃ A °
                        ⫗⟨ cong∃ lem5-1 ⟩
                          ‵∃ A
                        ∎
  lem5-1 {A = ‵⊥}    = ⫗refl
  lem5-1 {A = t ‵= u} = dn

lem5-2 : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ ‵¬ ‵¬ (A °) ‵⊃ A °
lem5-2 {A = A ‵⊃ B} = ‵lam (‵lam (lem5-2 ‵$ ‵lam
                         (2 ‵$ ‵lam
                           (1 ‵$ 0 ‵$ 2))))
lem5-2 {A = A ‵∧ B} = ‵lam (‵pair
                         (lem5-2 ‵$ ‵lam
                           (1 ‵$ ‵lam
                             (1 ‵$ ‵fst 0)))
                         (lem5-2 ‵$ ‵lam
                           (1 ‵$ ‵lam
                             (1 ‵$ ‵snd 0))))
lem5-2 {A = A ‵∨ B} = ‵lam (join 0)
lem5-2 {A = ‵∀ A}   = ‵lam (‵all refl (lem5-2 ‵$ ‵lam
                         (1 ‵$ ‵lam
                           (1 ‵$ ‵unall (‵tvar 0) idcutFm 0))))
lem5-2 {A = ‵∃ A}   = ‵lam (join 0)
lem5-2 {A = ‵⊥}    = ‵lam (0 ‵$ ⊃id)
lem5-2 {A = t ‵= u} = ‵lam (join 0)

lem5-3∋ : ∀ {k} {Γ : Fm§ k} {A} → Γ ∋ A → Γ °§ ∋ A °
lem5-3∋ zero    = zero
lem5-3∋ (suc i) = suc (lem5-3∋ i)

lem5-3 : ∀ {Þ k} {Γ : Fm§ k} {A} → PA / Γ ⊢ A → Þ / Γ °§ ⊢ A °
lem5-3 (‵var i)                = ‵var (lem5-3∋ i)
lem5-3 (‵lam d)                = ‵lam (lem5-3 d)
lem5-3 (d ‵$ e)                = lem5-3 d ‵$ lem5-3 e
lem5-3 (‵pair d e)             = ‵pair (lem5-3 d) (lem5-3 e)
lem5-3 (‵fst d)                = ‵fst (lem5-3 d)
lem5-3 (‵snd d)                = ‵snd (lem5-3 d)
lem5-3 (‵left d)               = return (‵left (lem5-3 d))
lem5-3 (‵right d)              = return (‵right (lem5-3 d))
lem5-3 (‵either c d e)         = lem5-2 ‵$ (lem5-3 c >>= ‵lam (‵either 0
                                   (return (exch (wk (lem5-3 d))))
                                   (return (exch (wk (lem5-3 e))))))
lem5-3 (‵all refl d)           = ‵all refl (TODO3 (lem5-3 d))
lem5-3 (‵unall t refl d)       = ‵unall t (TODO2 ⁻¹) (lem5-3 d)
lem5-3 (‵ex t refl d)          = return (‵ex t (TODO2 ⁻¹) (lem5-3 d))
lem5-3 (‵letex refl refl d e)  = lem5-2 ‵$ (lem5-3 d >>= ‵lam (‵letex refl refl 0
                                   (return (exch (wk (TODO6 (lem5-3 e)))))))
lem5-3 (‵magic d)              = lem5-2 ‵$ ‵lam (lem5-3 d)
lem5-3 ‵refl                   = return (‵refl)
lem5-3 (‵sym d)                = lem5-3 d >>= ‵lam
                                   (return (‵sym 0))
lem5-3 (‵trans d e)            = lem5-3 d >>= ‵lam
                                   (wk (lem5-3 e) >>= ‵lam
                                     (return (‵trans 1 0)))
lem5-3 (‵cong f i refl refl d) = lem5-3 d >>= ‵lam
                                   (return (‵cong f i refl refl 0))
lem5-3 ‵dis                    = return ‵dis
lem5-3 (‵inj d)                = lem5-3 d >>= ‵lam
                                   (return (‵inj 0))
lem5-3 (‵ind refl refl d e)    = ‵ind refl refl (TODO4 (lem5-3 d)) (TODO5 (lem5-3 e))
lem5-3 (‵proj i refl)          = return (‵proj i refl)
lem5-3 (‵comp g φ refl)        = return (‵comp g φ refl)
lem5-3 (‵rec {t = t} f g)      = ‵pair
                                   (return (‵fst (‵rec {t = t} f g)))
                                   (return (‵snd (‵rec f g)))

-- "Note that the converse of 3 trivially holds wih 1."
lem5-3⁻¹ : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ °§ ⊢ A ° → PA / Γ ⊢ A
lem5-3⁻¹ d = aux (‵fst lem5-1 ‵$ lem2 d)
  where
    aux : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ °§ ⊢ A → PA / Γ ⊢ A
    aux {Γ = ∙}     d = d
    aux {Γ = Γ , C} d = wk (aux (‵lam d)) ‵$ (‵snd lem5-1 ‵$ 0)

-- TODO: "A counterexample for 4 is ¬∀y.A[y/x₀]."
-- lem5-4 : ∀ {k} {Γ : Fm§ k} → ¬ (∀ {A} → HA / Γ , ‵¬ (‵∀ A) ⊢ (‵¬ (‵∀ A)) °)
-- lem5-4 = {!!}


----------------------------------------------------------------------------------------------------

-- 5.6. A-translation

_ᴬ⟨_⟩ : ∀ {k} → Fm k → Fm k → Fm k
(A ‵⊃ B) ᴬ⟨ T ⟩ = A ᴬ⟨ T ⟩ ‵⊃ B ᴬ⟨ T ⟩
(A ‵∧ B) ᴬ⟨ T ⟩ = A ᴬ⟨ T ⟩ ‵∧ B ᴬ⟨ T ⟩
(A ‵∨ B) ᴬ⟨ T ⟩ = A ᴬ⟨ T ⟩ ‵∨ B ᴬ⟨ T ⟩
(‵∀ A)   ᴬ⟨ T ⟩ = ‵∀ A ᴬ⟨ wkFm T ⟩
(‵∃ A)   ᴬ⟨ T ⟩ = ‵∃ A ᴬ⟨ wkFm T ⟩
‵⊥      ᴬ⟨ T ⟩ = T
(t ‵= u) ᴬ⟨ T ⟩ = (t ‵= u) ‵∨ T

_ᴬ⟨_⟩§ : ∀ {k} → Fm§ k → Fm k → Fm§ k
∙       ᴬ⟨ T ⟩§ = ∙
(Γ , A) ᴬ⟨ T ⟩§ = Γ ᴬ⟨ T ⟩§ , A ᴬ⟨ T ⟩

-- TODO: interactions between A-translation and renaming/substitution
module _ where
  postulate
    TODO7 : ∀ {k} {A : Fm (suc k)} {T t} → A [ t /0]Fm ᴬ⟨ T ⟩ ≡ A ᴬ⟨ wkFm T ⟩ [ t /0]Fm
  -- TODO7 = ?

-- TODO: lemma 6
module _ where
  -- NOTE: non-constructive
  aux1 : ∀ {k} {Γ : Fm§ k} {A B C} → PA / Γ ⊢ (A ‵∨ C) ‵⊃ (B ‵∨ C) ‵⫗ (A ‵⊃ B) ‵∨ C
  aux1 = ‵pair
           (‵lam (‵either em
             (‵right 0)
             (‵left (‵lam
               (‵either (2 ‵$ (‵left 0))
                 0
                 (abort (2 ‵$ 0)))))))
           (‵lam (‵lam (‵either 0
             (‵either 2
               (‵left (0 ‵$ 1))
               (‵right 0))
             (‵right 0))))

  aux2 : ∀ {Þ k} {Γ : Fm§ k} {A B C} → Þ / Γ ⊢ (A ‵∨ C) ‵∧ (B ‵∨ C) ‵⫗ (A ‵∧ B) ‵∨ C
  aux2 = ‵pair
           (‵lam (‵either (‵fst 0)
             (‵either (‵snd 1)
               (‵left (‵pair 1 0))
               (‵right 0))
             (‵right 0)))
           (‵lam (‵either 0
             (‵pair (‵left (‵fst 0)) (‵left (‵snd 0)))
             (‵pair (‵right 0) (‵right 0))))

  aux3 : ∀ {Þ k} {Γ : Fm§ k} {A B C} → Þ / Γ ⊢ (A ‵∨ C) ‵∨ (B ‵∨ C) ‵⫗ (A ‵∨ B) ‵∨ C
  aux3 = ‵pair
           (‵lam (‵either 0
             (‵either 0
               (‵left (‵left 0))
               (‵right 0))
             (‵either 0
               (‵left (‵right 0))
               (‵right 0))))
           (‵lam (‵either 0
             (‵either 0
               (‵left (‵left 0))
               (‵right (‵left 0)))
             (‵left (‵right 0)))) -- NOTE: could also be ‵right

  -- NOTE: non-constructive
  aux4 : ∀ {k} {Γ : Fm§ k} {A C} → PA / Γ ⊢ ‵∀ (A ‵∨ wkFm C) ‵⫗ ‵∀ A ‵∨ C
  aux4 = ‵pair
           (‵lam (‵either em
             (‵right 0)
             (‵left
               (‵all refl (‵either (‵unall (‵tvar 0) idcutFm 1)
                 0
                 (abort (1 ‵$ 0)))))))
           (‵lam (‵either 0
             (‵all refl (‵left (‵unall (‵tvar 0) idcutFm 0)))
             (‵all refl (‵right 0))))

  aux5 : ∀ {Þ k} {Γ : Fm§ k} {A C} → Þ / Γ ⊢ ‵∃ (A ‵∨ wkFm C) ‵⫗ ‵∃ A ‵∨ C
  aux5 {A = A} {C} = ‵pair
           (‵lam (‵letex refl refl 0 (‵either 0
             (‵left (‵ex (‵tvar 0) idcutFm 0))
             (‵right 0))))
           (‵lam (‵either 0
             (‵letex refl refl 0
               (‵ex (‵tvar 0) (_‵∨_ & idcutFm ⊗ idcutFm) (‵left 0)))
             (‵ex 𝟘 -- NOTE: could also be any other number
               ( (subFm (idTm§ , 𝟘) A ‵∨_)
                   & ( eqsubFm idTm§ 𝟘 C
                     ⋮ lidsubFm C
                     )
               )
               (‵right 0))))

  aux6 : ∀ {Þ k} {Γ : Fm§ k} {C} → Þ / Γ ⊢ C ‵⫗ ‵⊥ ‵∨ C
  aux6 = ‵pair
           (‵lam (‵right 0))
           (‵lam (‵either 0 (abort 0) 0))

module _ where
  open ⫗-Reasoning

  lem6-1 : ∀ {k} {Γ : Fm§ k} {A T} → PA / Γ ⊢ A ᴬ⟨ T ⟩ ‵⫗ A ‵∨ T
  lem6-1 {A = A ‵⊃ B} {T} = begin
                              A ᴬ⟨ T ⟩ ‵⊃ B ᴬ⟨ T ⟩
                            ⫗⟨ cong⊃ lem6-1 lem6-1 ⟩
                              (A ‵∨ T) ‵⊃ (B ‵∨ T)
                            ⫗⟨ aux1 ⟩
                              (A ‵⊃ B) ‵∨ T
                            ∎
  lem6-1 {A = A ‵∧ B} {T} = begin
                              A ᴬ⟨ T ⟩ ‵∧ B ᴬ⟨ T ⟩
                            ⫗⟨ cong∧ lem6-1 lem6-1 ⟩
                              (A ‵∨ T) ‵∧ (B ‵∨ T)
                            ⫗⟨ aux2 ⟩
                              (A ‵∧ B) ‵∨ T
                            ∎
  lem6-1 {A = A ‵∨ B} {T} = begin
                              A ᴬ⟨ T ⟩ ‵∨ B ᴬ⟨ T ⟩
                            ⫗⟨ cong∨ lem6-1 lem6-1 ⟩
                              (A ‵∨ T) ‵∨ (B ‵∨ T)
                            ⫗⟨ aux3 ⟩
                              (A ‵∨ B) ‵∨ T
                            ∎
  lem6-1 {A = ‵∀ A}   {T} = begin
                              ‵∀ (A ᴬ⟨ wkFm T ⟩)
                            ⫗⟨ cong∀ lem6-1 ⟩
                              ‵∀ (A ‵∨ wkFm T)
                            ⫗⟨ aux4 ⟩
                              ‵∀ A ‵∨ T
                            ∎
  lem6-1 {A = ‵∃ A}   {T} = begin
                              ‵∃ (A ᴬ⟨ wkFm T ⟩)
                            ⫗⟨ cong∃ lem6-1 ⟩
                              ‵∃ (A ‵∨ wkFm T)
                            ⫗⟨ aux5 ⟩
                              ‵∃ A ‵∨ T
                            ∎
  lem6-1 {A = ‵⊥}    {T} = aux6
  lem6-1 {A = t ‵= u} {T} = ⫗refl

-- lem6-2 : ∀ {Þ k} {Γ : Fm§ k} {A T} → Þ / Γ ⊢ T ‵⊃ A ᴬ⟨ T ⟩
-- lem6-2 {A = A ‵⊃ B} = ‵lam (‵lam (lem6-2 ‵$ 1)) -- NOTE: function argument ignored
-- lem6-2 {A = A ‵∧ B} = ‵lam (‵pair (lem6-2 ‵$ 0) (lem6-2 ‵$ 0))
-- lem6-2 {A = A ‵∨ B} = ‵lam (‵left (lem6-2 ‵$ 0)) -- NOTE: could also be ‵right
-- lem6-2 {A = ‵∀ A}   = ‵lam (‵all refl (lem6-2 ‵$ 0))
-- lem6-2 {A = ‵∃ A}   = {!!}
-- -- ‵lam (‵this 𝟘 TODO7 (lem6-2 {A = A [ 𝟘 ]} ‵$ 0)) -- TODO: termination failure
-- lem6-2 {A = ‵⊥}    = ⊃id
-- lem6-2 {A = t ‵= u} = ‵lam (‵right 0)

-- lem6-3∋ : ∀ {k} {Γ : Fm§ k} {A T} → Γ ∋ A → Γ ᴬ⟨ T ⟩§ ∋ A ᴬ⟨ T ⟩
-- lem6-3∋ zero    = zero
-- lem6-3∋ (suc i) = suc (lem6-3∋ i)

-- -- -- TODO: "The proof of 3 is a bit tricky where eigenvariable conditions are involved."
-- -- lem6-3 : ∀ {Þ k} {Γ : Fm§ k} {A T} → Þ / Γ ⊢ A → Þ / Γ ᴬ⟨ T ⟩§ ⊢ A ᴬ⟨ T ⟩
-- -- lem6-3 (‵var i)                = ‵var (lem6-3∋ i)
-- -- lem6-3 (‵lam d)                = ‵lam (lem6-3 d)
-- -- lem6-3 (d ‵$ e)                = lem6-3 d ‵$ lem6-3 e
-- -- lem6-3 (‵pair d e)             = ‵pair (lem6-3 d) (lem6-3 e)
-- -- lem6-3 (‵fst d)                = ‵fst (lem6-3 d)
-- -- lem6-3 (‵snd d)                = ‵snd (lem6-3 d)
-- -- lem6-3 (‵left d)               = ‵left (lem6-3 d)
-- -- lem6-3 (‵right d)              = ‵right (lem6-3 d)
-- -- lem6-3 (‵either c d e)         = ‵either (lem6-3 c) (lem6-3 d) (lem6-3 e)
-- -- lem6-3 (‵all refl d)           = {!!}
-- -- lem6-3 (‵unall t refl d)       = {!!}
-- -- lem6-3 (‵ex t refl d)          = {!!}
-- -- lem6-3 (‵letex refl refl d e)  = {!!}
-- -- lem6-3 (‵abort d)              = {!!}
-- -- lem6-3 (‵magic d)              = {!!}
-- -- lem6-3 ‵refl                   = ‵left ‵refl
-- -- lem6-3 (‵sym d)                = ‵either (lem6-3 d)
-- --                                    (‵left (‵sym 0))
-- --                                    (‵right 0)
-- -- lem6-3 (‵trans d e)            = ‵either (lem6-3 d)
-- --                                    (‵either (wk (lem6-3 e))
-- --                                      (‵left (‵trans 1 0))
-- --                                      (‵right 0))
-- --                                    (‵right 0)
-- -- lem6-3 (‵cong f i refl refl d) = {!!}
-- -- lem6-3 ‵dis                    = {!!}
-- -- lem6-3 (‵inj d)                = {!!}
-- -- lem6-3 (‵ind refl refl d e)    = {!!}
-- -- lem6-3 (‵proj i refl)          = {!!}
-- -- lem6-3 (‵comp g φ refl)        = {!!}
-- -- lem6-3 (‵rec f g)              = {!!}

-- -- -- TODO: "A counterexample for 4 is A = ¬¬T."
-- -- -- lem6-4 : ∀ {k} {Γ : Fm§ k} → ¬ (∀ {T} → HA / Γ , ‵¬ ‵¬ T ⊢ (‵¬ ‵¬ T) ᴬ⟨ T ⟩)
-- -- -- lem6-4 = {!!}


-- -- ----------------------------------------------------------------------------------------------------

-- -- -- TODO: section title
-- -- -- TODO: lemma 7
-- -- -- TODO: corollary 8
-- -- -- TODO: theorem 1


-- -- ----------------------------------------------------------------------------------------------------
