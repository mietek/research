-- 2025-03-21
-- Friedman’s A-Translation
-- https://www.mscs.dal.ca/~selinger/papers/friedman.pdf
-- thanks to ncf and roconnor
-- first-order predicate logic with one sort (naturals) and one predicate (equality)

module Selinger92 where

open import Agda.Builtin.FromNat using (Number ; fromNat)

open import Data.Empty using (⊥)

import Data.Fin as Fin
open Fin using (Fin ; zero ; suc)

import Data.Nat as Nat
open Nat using (zero ; suc)
  renaming (ℕ to Nat)

open import Data.Product using (Σ ; _×_)
  renaming (_,_ to sig ; proj₁ to fst ; proj₂ to snd)

open import Data.Sum using (_⊎_)
  renaming (inj₁ to left ; inj₂ to right)

open import Data.Unit using (⊤ ; tt)

open import Function using (_∘_ ; _$_ ; const ; flip ; id)

import Level
open Level using (_⊔_ ; Level)

import Relation.Binary.PropositionalEquality as Id
open Id using (_≡_ ; refl ; module ≡-Reasoning)

open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
  renaming (contradiction to _↯_)

open import Relation.Nullary.Decidable using (True)


----------------------------------------------------------------------------------------------------

-- right-handed lists and vectors

infixl 4 _,_
data List {𝓍} (X : Set 𝓍) : Set 𝓍 where
  ∙   : List X
  _,_ : ∀ (ξ : List X) (x : X) → List X

data Vec {𝓍} (X : Set 𝓍) : Nat → Set 𝓍 where
  ∙   : Vec X zero
  _,_ : ∀ {n} (ξ : Vec X n) (x : X) → Vec X (suc n)

get : ∀ {𝓍} {X : Set 𝓍} {n} → Fin n → Vec X n → X
get zero    (ξ , x) = x
get (suc i) (ξ , x) = get i ξ

put : ∀ {𝓍} {X : Set 𝓍} {n} → Fin n → Vec X n → X → Vec X n
put zero    (ξ , x) y = ξ , y
put (suc i) (ξ , x) y = put i ξ y , x

for : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {n} → Vec X n → (X → Y) → Vec Y n
for ∙       f = ∙
for (ξ , x) f = for ξ f , f x

tab : ∀ {𝓍} {X : Set 𝓍} {n} → (Fin n → X) → Vec X n
tab {n = zero}  f = ∙
tab {n = suc n} f = tab (f ∘ suc) , f zero


----------------------------------------------------------------------------------------------------

-- missing things

infixl 9 _&_
_&_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (f : X → Y) {x x′} → x ≡ x′ → f x ≡ f x′
_&_ = Id.cong

infixl 8 _⊗_
_⊗_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {f g : X → Y} {x x′} → f ≡ g → x ≡ x′ → f x ≡ g x′
refl ⊗ refl = refl

infix 9 _⁻¹
_⁻¹ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} → x ≡ x′ → x′ ≡ x
_⁻¹ = Id.sym

infixr 4 _⋮_
_⋮_ : ∀ {𝓍} {X : Set 𝓍} {x x′ x″ : X} → x ≡ x′ → x′ ≡ x″ → x ≡ x″
_⋮_ = Id.trans

coe : ∀ {𝓍} {X X′ : Set 𝓍} → X ≡ X′ → X → X′
coe = Id.subst id

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

-- untyped de Bruijn indices and order-preserving embeddings for term variables

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
id≤ {zero}  = stop
id≤ {suc k} = lift≤ id≤

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
wkFin = renFin (wk≤ id≤)

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

-- typed de Bruijn indices and order-preserving embeddings for derivation variables

module _ {𝓍} {X : Set 𝓍} where
  infix 3 _∋_
  data _∋_ : List X → X → Set 𝓍 where
    zero : ∀ {Γ A} → Γ , A ∋ A
    suc  : ∀ {Γ A C} (i : Γ ∋ A) → Γ , C ∋ A

-- NOTE: literals for standalone derivation variables
module _ {𝓍} {X : Set 𝓍} where
  infix 3 _∋⟨_⟩_
  data _∋⟨_⟩_ : List X → Nat → X → Set 𝓍 where
    instance
      zero : ∀ {Γ A} → Γ , A ∋⟨ zero ⟩ A
      suc  : ∀ {Γ m A C} {{i : Γ ∋⟨ m ⟩ A}} → Γ , C ∋⟨ suc m ⟩ A

  ∋#→∋ : ∀ {m} {Γ : List X} {A} → Γ ∋⟨ m ⟩ A → Γ ∋ A
  ∋#→∋ zero        = zero
  ∋#→∋ (suc {{i}}) = suc (∋#→∋ i)

  instance
    number∋ : ∀ {Γ : List X} {A} → Number (Γ ∋ A)
    number∋ {Γ = Γ} {A} = record
      { Constraint = λ m → Γ ∋⟨ m ⟩ A
      ; fromNat    = λ m {{p}} → ∋#→∋ p
      }

module _ {𝓍} {X : Set 𝓍} where
  infix 3 _⊑_
  data _⊑_ : List X → List X → Set 𝓍 where
    stop  : ∙ ⊑ ∙
    wk⊑   : ∀ {Γ Γ′ C} (η : Γ ⊑ Γ′) → Γ ⊑ Γ′ , C
    lift⊑ : ∀ {Γ Γ′ C} (η : Γ ⊑ Γ′) → Γ , C ⊑ Γ′ , C

  id⊑ : ∀ {Γ} → Γ ⊑ Γ
  id⊑ {∙}     = stop
  id⊑ {Γ , A} = lift⊑ id⊑

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
  wk∋ = ren∋ (wk⊑ id⊑)

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

-- primitive recursive n-ary functions on naturals
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
#proj i ξ = get i ξ

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

-- some primitive recursive n-ary functions on naturals
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

module _ where
  open ≡-Reasoning

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

-- terms, indexed by number of term variables

mutual
  data Tm (k : Nat) : Set where
    ‵var : ∀ (i : Fin k) → Tm k -- i-th term variable
    ‵fun : ∀ {n} (f : Prim n) (τ : Tm§ k n) → Tm k

  Tm§ : Nat → Nat → Set
  Tm§ k n = Vec (Tm k) n

-- -- NOTE: literals for term variables in terms
-- -- TODO: delete?
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

-- -- NOTE: literals for naturals encoded as object-level primitive recursive functions
-- -- TODO: delete?
-- module _ where
--   natTm : ∀ {k} → Nat → Tm k
--   natTm zero    = 𝟘
--   natTm (suc m) = 𝕊 (natTm m)
--
--   instance
--     numberTm : ∀ {k} → Number (Tm k)
--     numberTm {k} = record
--       { Constraint = λ _ → ⊤
--       ; fromNat    = λ m → natTm m
--       }


----------------------------------------------------------------------------------------------------

-- terms: renaming

mutual
  renTm : ∀ {k k′} → k ≤ k′ → Tm k → Tm k′
  renTm η (‵var i)   = ‵var (renFin η i)
  renTm η (‵fun f τ) = ‵fun f (renTm§ η τ)

  renTm§ : ∀ {k k′ n} → k ≤ k′ → Tm§ k n → Tm§ k′ n
  renTm§ η ∙       = ∙
  renTm§ η (τ , t) = renTm§ η τ , renTm η t


----------------------------------------------------------------------------------------------------

-- terms: generic lemmas from RenKit

wkTm : ∀ {k} → Tm k → Tm (suc k)
wkTm t = renTm (wk≤ id≤) t

wkTm§ : ∀ {k n} → Tm§ k n → Tm§ (suc k) n
wkTm§ τ = renTm§ (wk≤ id≤) τ

liftTm§ : ∀ {k n} → Tm§ k n → Tm§ (suc k) (suc n)
liftTm§ τ = wkTm§ τ , ‵var zero

varTm§ : ∀ {k k′} → k ≤ k′ → Tm§ k′ k
varTm§ stop      = ∙
varTm§ (wk≤ η)   = wkTm§ (varTm§ η)
varTm§ (lift≤ η) = liftTm§ (varTm§ η)

-- TODO: check if changing this affects anything
idTm§ : ∀ {k} → Tm§ k k
idTm§ {zero}  = ∙
idTm§ {suc k} = liftTm§ idTm§
-- idTm§ = var§ id≤

subFin : ∀ {k m} → Tm§ m k → Fin k → Tm m
subFin (σ , s) zero    = s
subFin (σ , s) (suc i) = subFin σ i


----------------------------------------------------------------------------------------------------

-- terms: substitution

mutual
  subTm : ∀ {k m} → Tm§ m k → Tm k → Tm m
  subTm σ (‵var i)   = subFin σ i
  subTm σ (‵fun f τ) = ‵fun f (subTm§ σ τ)

  subTm§ : ∀ {k m n} → Tm§ m k → Tm§ k n → Tm§ m n
  subTm§ σ ∙       = ∙
  subTm§ σ (τ , t) = subTm§ σ τ , subTm σ t


----------------------------------------------------------------------------------------------------

-- terms: generic lemmas from SubKit

_[_]Tm : ∀ {k} → Tm (suc k) → Tm k → Tm k
t [ s ]Tm = subTm (idTm§ , s) t

getTm§ : ∀ {k n n′} → n ≤ n′ → Tm§ k n′ → Tm§ k n
getTm§ stop      τ       = τ
getTm§ (wk≤ η)   (τ , t) = getTm§ η τ
getTm§ (lift≤ η) (τ , t) = getTm§ η τ , t


----------------------------------------------------------------------------------------------------

-- terms: fundamental renaming lemmas

mutual
  lidrenTm : ∀ {k} (t : Tm k) → renTm id≤ t ≡ t
  lidrenTm (‵var i)   = ‵var & idrenFin i
  lidrenTm (‵fun f τ) = ‵fun f & lidrenTm§ τ

  lidrenTm§ : ∀ {k n} (τ : Tm§ k n) → renTm§ id≤ τ ≡ τ
  lidrenTm§ ∙       = refl
  lidrenTm§ (τ , t) = _,_ & lidrenTm§ τ ⊗ lidrenTm t

mutual
  comprenTm : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (t : Tm k) →
                renTm (η′ ∘≤ η) t ≡ (renTm η′ ∘ renTm η) t
  comprenTm η′ η (‵var i)   = ‵var & comprenFin η′ η i
  comprenTm η′ η (‵fun f τ) = ‵fun f & comprenTm§ η′ η τ

  comprenTm§ : ∀ {k k′ k″ n} (η′ : k′ ≤ k″) (η : k ≤ k′) (τ : Tm§ k n) →
                 renTm§ (η′ ∘≤ η) τ ≡ (renTm§ η′ ∘ renTm§ η) τ
  comprenTm§ η′ η ∙       = refl
  comprenTm§ η′ η (τ , t) = _,_ & comprenTm§ η′ η τ ⊗ comprenTm η′ η t

ridrenTm : ∀ {k k′} (η : k ≤ k′) (i : Fin k) → renTm η (‵var i) ≡ ‵var (renFin η i)
ridrenTm η i = refl

ridsubTm : ∀ {k m} (σ : Tm§ m k) (i : Fin k) → subTm σ (‵var i) ≡ subFin σ i
ridsubTm σ i = refl


----------------------------------------------------------------------------------------------------

-- terms: generic lemmas from RenSubKit1

eqwkrenTm : ∀ {k k′} (η : k ≤ k′) (t : Tm k) →
              (renTm (lift≤ η) ∘ wkTm) t ≡ (wkTm ∘ renTm η) t
eqwkrenTm η t = comprenTm (lift≤ η) (wk≤ id≤) t ⁻¹
              ⋮ (flip renTm t ∘ wk≤) & (rid≤ η ⋮ lid≤ η ⁻¹)
              ⋮ comprenTm (wk≤ id≤) η t

eqwkrenTm§ : ∀ {k k′ n} (η : k ≤ k′) (τ : Tm§ k n) →
               (renTm§ (lift≤ η) ∘ wkTm§) τ ≡ (wkTm§ ∘ renTm§ η) τ
eqwkrenTm§ η ∙       = refl
eqwkrenTm§ η (τ , t) = _,_ & eqwkrenTm§ η τ ⊗ eqwkrenTm η t

eqliftrenTm§ : ∀ {k k′ n} (η : k ≤ k′) (τ : Tm§ k n) →
                 (renTm§ (lift≤ η) ∘ liftTm§) τ ≡ (liftTm§ ∘ renTm§ η) τ
eqliftrenTm§ η τ = ((renTm§ (lift≤ η) ∘ wkTm§) τ ,_) & ridrenTm (lift≤ η) zero
                 ⋮ (_, ‵var zero) & eqwkrenTm§ η τ

ridrenTm§ : ∀ {k k′} (η : k ≤ k′) → renTm§ η idTm§ ≡ varTm§ η
ridrenTm§ stop      = refl
ridrenTm§ (wk≤ η)   = (flip renTm§ idTm§ ∘ wk≤) & lid≤ η ⁻¹
                    ⋮ comprenTm§ (wk≤ id≤) η idTm§
                    ⋮ wkTm§ & ridrenTm§ η
ridrenTm§ (lift≤ η) = ((renTm§ (lift≤ η) ∘ wkTm§) idTm§ ,_) & ridrenTm (lift≤ η) zero
                    ⋮ (_, ‵var zero) & (eqwkrenTm§ η idTm§ ⋮ wkTm§ & ridrenTm§ η)

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

idsubFin : ∀ {k} (i : Fin k) → subFin idTm§ i ≡ ‵var i
idsubFin zero    = refl
idsubFin (suc i) = eqrensubFin (wk≤ id≤) idTm§ i
                 ⋮ wkTm & idsubFin i
                 ⋮ ridrenTm (wk≤ id≤) i
                 ⋮ (‵var ∘ suc) & idrenFin i

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
eqliftgetTm§ η τ = (_, ‵var zero) & eqwkgetTm§ η τ

ridgetTm§ : ∀ {k k′} (η : k ≤ k′) → getTm§ η idTm§ ≡ varTm§ η
ridgetTm§ stop      = refl
ridgetTm§ (wk≤ η)   = eqrengetTm§ (wk≤ id≤) η idTm§
                    ⋮ wkTm§ & ridgetTm§ η
ridgetTm§ (lift≤ η) = (_, ‵var zero) & (eqrengetTm§ (wk≤ id≤) η idTm§
                    ⋮ wkTm§ & ridgetTm§ η)


----------------------------------------------------------------------------------------------------

-- terms: fundamental substitution lemmas

mutual
  eqrensubTm : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (t : Tm k) →
                 subTm (renTm§ η σ) t ≡ (renTm η ∘ subTm σ) t
  eqrensubTm η σ (‵var i)   = eqrensubFin η σ i
  eqrensubTm η σ (‵fun f τ) = ‵fun f & eqrensubTm§ η σ τ

  eqrensubTm§ : ∀ {k m m′ n} (η : m ≤ m′) (σ : Tm§ m k) (τ : Tm§ k n) →
                 subTm§ (renTm§ η σ) τ ≡ (renTm§ η ∘ subTm§ σ) τ
  eqrensubTm§ η σ ∙       = refl
  eqrensubTm§ η σ (τ , t) = _,_ & eqrensubTm§ η σ τ ⊗ eqrensubTm η σ t

mutual
  eqsubrenTm : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (t : Tm k) →
                 subTm (getTm§ η σ) t ≡ (subTm σ ∘ renTm η) t
  eqsubrenTm σ η (‵var i)   = eqsubrenFin σ η i
  eqsubrenTm σ η (‵fun f τ) = ‵fun f & eqsubrenTm§ σ η τ

  eqsubrenTm§ : ∀ {k k′ m n} (σ : Tm§ m k′) (η : k ≤ k′) (τ : Tm§ k n) →
                  subTm§ (getTm§ η σ) τ ≡ (subTm§ σ ∘ renTm§ η) τ
  eqsubrenTm§ σ η ∙       = refl
  eqsubrenTm§ σ η (τ , t) = _,_ & eqsubrenTm§ σ η τ ⊗ eqsubrenTm σ η t

mutual
  lidsubTm : ∀ {k} (t : Tm k) → subTm idTm§ t ≡ t
  lidsubTm (‵var i)   = idsubFin i
  lidsubTm (‵fun f τ) = ‵fun f & lidsubTm§ τ

  lidsubTm§ : ∀ {k n} (τ : Tm§ k n) → subTm§ idTm§ τ ≡ τ
  lidsubTm§ ∙       = refl
  lidsubTm§ (τ , t) = _,_ & lidsubTm§ τ ⊗ lidsubTm t


----------------------------------------------------------------------------------------------------

-- terms: generic lemmas from RenSubKit2

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
              ⋮ flip subTm t & (eqwkgetTm§ id≤ σ ⋮ wkTm§ & lidgetTm§ σ)
              ⋮ eqrensubTm (wk≤ id≤) σ t

eqwksubTm§ : ∀ {k m n} (σ : Tm§ m k) (τ : Tm§ k n) →
               (subTm§ (liftTm§ σ) ∘ wkTm§) τ ≡ (wkTm§ ∘ subTm§ σ) τ
eqwksubTm§ σ ∙       = refl
eqwksubTm§ σ (τ , t) = _,_ & eqwksubTm§ σ τ ⊗ eqwksubTm σ t

eqliftsubTm§ : ∀ {k m n} (σ : Tm§ m k) (τ : Tm§ k n) →
                 (subTm§ (liftTm§ σ) ∘ liftTm§) τ ≡ (liftTm§ ∘ subTm§ σ) τ
eqliftsubTm§ σ τ = ((subTm§ (liftTm§ σ) ∘ wkTm§) τ ,_) & ridsubTm (liftTm§ σ) zero
                 ⋮ (_, ‵var zero) & eqwksubTm§ σ τ

ridsubTm§ : ∀ {k m} (σ : Tm§ m k) → subTm§ σ idTm§ ≡ σ
ridsubTm§ ∙       = refl
ridsubTm§ (σ , s) = ((subTm§ (σ , s) ∘ wkTm§) idTm§ ,_) & ridsubTm (σ , s) zero
                  ⋮ (_, s) & (eqsubTm§ σ s idTm§ ⋮ ridsubTm§ σ)


----------------------------------------------------------------------------------------------------

-- terms: more fundamental substitution lemmas

mutual
  compsubTm : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (t : Tm k) →
                subTm (subTm§ σ′ σ) t ≡ (subTm σ′ ∘ subTm σ) t
  compsubTm σ′ σ (‵var i)   = compsubFin σ′ σ i
  compsubTm σ′ σ (‵fun f τ) = ‵fun f & compsubTm§ σ′ σ τ

  compsubTm§ : ∀ {k m m′ n} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (τ : Tm§ k n) →
                 subTm§ (subTm§ σ′ σ) τ ≡ (subTm§ σ′ ∘ subTm§ σ) τ
  compsubTm§ σ′ σ ∙       = refl
  compsubTm§ σ′ σ (τ , t) = _,_ & compsubTm§ σ′ σ τ ⊗ compsubTm σ′ σ t


----------------------------------------------------------------------------------------------------

-- terms: generic lemmas from RenSubKit3

asssubTm§ : ∀ {k m m′ n} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (τ : Tm§ k n) →
              (subTm§ σ′ ∘ subTm§ σ) τ ≡ subTm§ (subTm§ σ′ σ) τ
asssubTm§ σ′ σ ∙       = refl
asssubTm§ σ′ σ (τ , t) = _,_ & asssubTm§ σ′ σ τ ⊗ compsubTm σ′ σ t ⁻¹

rencutTm : ∀ {k k′} (η : k ≤ k′) (t : Tm (suc k)) (s : Tm k) →
             renTm (lift≤ η) t [ renTm η s ]Tm ≡ renTm η (t [ s ]Tm)
rencutTm η t s = eqsubrenTm (idTm§ , renTm η s) (lift≤ η) t ⁻¹
               ⋮ (flip subTm t ∘ (_, renTm η s)) & (ridgetTm§ η ⋮ ridrenTm§ η ⁻¹)
               ⋮ eqrensubTm η (idTm§ , s) t

subcutTm : ∀ {k m} (σ : Tm§ m k) (t : Tm (suc k)) (s : Tm k) →
             subTm (liftTm§ σ) t [ subTm σ s ]Tm ≡ subTm σ (t [ s ]Tm)
subcutTm σ t s = compsubTm (idTm§ , subTm σ s) (liftTm§ σ) t ⁻¹
               ⋮ flip subTm t &
                   ( _,_ & ( eqsubrenTm§ (idTm§ , subTm σ s) (wk≤ id≤) σ ⁻¹
                            ⋮ flip subTm§ σ & lidgetTm§ idTm§
                            ⋮ lidsubTm§ σ
                            ⋮ ridsubTm§ σ ⁻¹
                            )
                          ⊗ ridsubTm (idTm§ , subTm σ s) zero
                   )
               ⋮ compsubTm σ (idTm§ , s) t


----------------------------------------------------------------------------------------------------

-- formulas, indexed by number of term variables

infix  19 _‵=_
infixl 18 _‵∧_
infixl 17 _‵∨_
infixr 16 _‵⊃_
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

infixr 15 _‵⫗_
_‵⫗_ : ∀ {k} → Fm k → Fm k → Fm k
A ‵⫗ B = (A ‵⊃ B) ‵∧ (B ‵⊃ A)

‵¬_ : ∀ {k} → Fm k → Fm k
‵¬ A = A ‵⊃ ‵⊥

infix 19 _‵≠_
_‵≠_ : ∀ {k} → Tm k → Tm k → Fm k
t ‵≠ u = ‵¬ (t ‵= u)


----------------------------------------------------------------------------------------------------

-- formulas: renaming

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

-- weaken formula by adding one unused term variable
wkFm : ∀ {k} → Fm k → Fm (suc k)
wkFm A = renFm (wk≤ id≤) A

-- weaken formulas by adding one unused term variable
wkFm§ : ∀ {k} → Fm§ k → Fm§ (suc k)
wkFm§ Γ = renFm§ (wk≤ id≤) Γ


----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- TODO: substitution for terms and formulas

postulate
  -- exchange two topmost term variables in formula
  texFm : ∀ {k} (A : Fm (suc (suc k))) → Fm (suc (suc k))

  -- substitute topmost term variable in formula by term
  _[_] : ∀ {k} (A : Fm (suc k)) (s : Tm k) → Fm k

  TODO0 : ∀ {k} {A : Fm k} {t} → A ≡ wkFm A [ t ]
  TODO1 : ∀ {k} {A : Fm (suc k)} → A ≡ renFm (lift≤ (wk≤ id≤)) A [ ‵var zero ]
  TODO7 : ∀ {k} {A : Fm (suc k)} {B t} → A [ t ] ‵∨ B [ t ] ≡ (A ‵∨ B) [ t ]

module _ where
  open ≡-Reasoning

  TODO8 : ∀ {k} {A : Fm (suc k)} {B t} → A [ t ] ‵∨ B ≡ (A ‵∨ wkFm B) [ t ]
  TODO8 {A = A} {B} {t} = _‵∨_ & refl ⊗ TODO0
                        ⋮ TODO7

  TODO9 : ∀ {k} {A : Fm (suc k)} {B} → A ‵∨ wkFm B ≡
            (renFm (lift≤ (wk≤ id≤)) A ‵∨ renFm (lift≤ (wk≤ id≤)) (wkFm B)) [ ‵var zero ]
  TODO9 {A = A} {B} = _‵∨_ & TODO1 ⊗ TODO1
                    ⋮ TODO7


----------------------------------------------------------------------------------------------------

-- TODO: are these really necessary?

tren⊑ : ∀ {k k′ Γ Γ′} (η : k ≤ k′) → Γ ⊑ Γ′ → renFm§ η Γ ⊑ renFm§ η Γ′
tren⊑ η stop      = stop
tren⊑ η (wk⊑ ζ)   = wk⊑ (tren⊑ η ζ)
tren⊑ η (lift⊑ ζ) = lift⊑ (tren⊑ η ζ)

twk⊑ : ∀ {k} {Γ Γ′ : Fm§ k} → Γ ⊑ Γ′ → wkFm§ Γ ⊑ wkFm§ Γ′
twk⊑ η = tren⊑ (wk≤ id≤) η


----------------------------------------------------------------------------------------------------

-- Heyting and Peano arithmetic
data Theory : Set where
  HA : Theory
  PA : Theory

infixr 14 _‵$_

-- derivations, indexed by list of derivation variables
infix 3 _/_⊢_
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
  ‵all    : ∀ {Þ Γ A} (d : Þ / wkFm§ Γ ⊢ A) → Þ / Γ ⊢ ‵∀ A

  --   ∀y.A[y/x₀]
  -- --------------
  --    A[t/x₀]
  ‵one    : ∀ {Þ Γ A A′} t (p : A′ ≡ A [ t ]) (d : Þ / Γ ⊢ ‵∀ A) → Þ / Γ ⊢ A′

  --    A[t/x₀]
  -- --------------
  --   ∃y.A[y/x₀]
  ‵this   : ∀ {Þ Γ A A′} t (p : A′ ≡ A [ t ]) (d : Þ / Γ ⊢ A′) → Þ / Γ ⊢ ‵∃ A

  --                 A(x₀)
  --                   ⋮
  --   ∃y.A[y/x₀]      C
  -- -----------------------
  --           C
  ‵some   : ∀ {Þ Γ A C} (d : Þ / Γ ⊢ ‵∃ A) (e : Þ / wkFm§ Γ , A ⊢ wkFm C) → Þ / Γ ⊢ C

  -- explosion (ex falso quodlibet) as primitive in Heyting arithmetic
  ‵abort  : ∀ {Γ C} (d : HA / Γ ⊢ ‵⊥) → HA / Γ ⊢ C

  -- double negation elimination (reductio ad absurdum) as primitive in Peano arithmetic
  ‵magic  : ∀ {Γ A} (d : PA / Γ , ‵¬ A ⊢ ‵⊥) → PA / Γ ⊢ A

  ‵refl   : ∀ {Þ Γ t} → Þ / Γ ⊢ t ‵= t
  ‵sym    : ∀ {Þ Γ t u} (d : Þ / Γ ⊢ t ‵= u) → Þ / Γ ⊢ u ‵= t
  ‵trans  : ∀ {Þ Γ s t u} (d : Þ / Γ ⊢ s ‵= t) (e : Þ / Γ ⊢ t ‵= u) → Þ / Γ ⊢ s ‵= u

  ‵cong   : ∀ {Þ Γ n τ u} (f : Prim n) (i : Fin n) (d : Þ / Γ ⊢ get i τ ‵= u) →
              Þ / Γ ⊢ ‵fun f τ ‵= ‵fun f (put i τ u)

  ‵dis    : ∀ {Þ Γ t} → Þ / Γ ⊢ 𝕊 t ‵≠ 𝟘

  ‵inj    : ∀ {Þ Γ t u} (d : Þ / Γ ⊢ 𝕊 t ‵= 𝕊 u) → Þ / Γ ⊢ t ‵= u

  --   A[0/x₀]    ∀y.A[y/x₀]→A[y+1/x₀]
  -- ------------------------------------
  --              ∀y.A[y/x₀]
  ‵ind    : ∀ {Þ Γ A} (d : Þ / Γ ⊢ A [ 𝟘 ])
              (e : Þ / Γ ⊢ ‵∀ (A ‵⊃ (texFm (wkFm A)) [ 𝕊 𝟘 ])) →
              Þ / Γ ⊢ ‵∀ A

  ‵proj   : ∀ {Þ Γ n τ} (i : Fin n) → Þ / Γ ⊢ ‵fun (proj i) τ ‵= get i τ

  ‵comp   : ∀ {Þ Γ n m τ} (g : Prim m) (φ : Prim§ n m) →
              Þ / Γ ⊢ ‵fun (comp g φ) τ ‵= ‵fun g (for φ λ f → ‵fun f τ)

  ‵rec    : ∀ {Þ Γ n t τ} (f : Prim n) (g : Prim (suc (suc n))) →
              Þ / Γ ⊢ ‵fun (rec f g) (τ , 𝟘) ‵= ‵fun f τ ‵∧
                ‵fun (rec f g) (τ , 𝕊 t) ‵= ‵fun g (τ , t , ‵fun (rec f g) (τ , t))

-- NOTE: literals for derivation variables in terms
instance
  number⊢ : ∀ {Þ k} {Γ : Fm§ k} {A} → Number (Þ / Γ ⊢ A)
  number⊢ {Γ = Γ} {A} = record
    { Constraint = λ m → Γ ∋⟨ m ⟩ A
    ; fromNat    = λ m {{p}} → ‵var (∋#→∋ p)
    }


----------------------------------------------------------------------------------------------------

-- renaming for derivations

ren : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A} → Γ ⊑ Γ′ → Þ / Γ ⊢ A → Þ / Γ′ ⊢ A
ren η (‵var i)         = ‵var (ren∋ η i)
ren η (‵lam d)         = ‵lam (ren (lift⊑ η) d)
ren η (d ‵$ e)         = ren η d ‵$ ren η e
ren η (‵pair d e)      = ‵pair (ren η d) (ren η e)
ren η (‵fst d)         = ‵fst (ren η d)
ren η (‵snd d)         = ‵snd (ren η d)
ren η (‵left d)        = ‵left (ren η d)
ren η (‵right d)       = ‵right (ren η d)
ren η (‵either c d e)  = ‵either (ren η c) (ren (lift⊑ η) d) (ren (lift⊑ η) e)
ren η (‵all d)         = ‵all (ren (twk⊑ η) d)
ren η (‵one t refl d)  = ‵one t refl (ren η d)
ren η (‵this t refl d) = ‵this t refl (ren η d)
ren η (‵some d e)      = ‵some (ren η d) (ren (lift⊑ (twk⊑ η)) e)
ren η (‵abort d)       = ‵abort (ren η d)
ren η (‵magic d)       = ‵magic (ren (lift⊑ η) d)
ren η ‵refl            = ‵refl
ren η (‵sym d)         = ‵sym (ren η d)
ren η (‵trans d e)     = ‵trans (ren η d) (ren η e)
ren η (‵cong f i d)    = ‵cong f i (ren η d)
ren η ‵dis             = ‵dis
ren η (‵inj d)         = ‵inj (ren η d)
ren η (‵ind d e)       = ‵ind (ren η d) (ren η e)
ren η (‵proj i)        = ‵proj i
ren η (‵comp g φ)      = ‵comp g φ
ren η (‵rec f g)       = ‵rec f g


----------------------------------------------------------------------------------------------------

-- generic lemmas from RenKit

infix 3 _/_⊢§_
data _/_⊢§_ {k} (Þ : Theory) (Γ : Fm§ k) : Fm§ k → Set where
  ∙   : Þ / Γ ⊢§ ∙
  _,_ : ∀ {Δ A} (δ : Þ / Γ ⊢§ Δ) (d : Þ / Γ ⊢ A) → Þ / Γ ⊢§ Δ , A

-- weaken derivation by adding one unused derivation variable
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
id§ {Γ = ∙}     = ∙
id§ {Γ = Γ , A} = lift§ id§
-- id§ = var§ id⊑

sub∋ : ∀ {Þ k} {Γ Ξ : Fm§ k} {A} → Þ / Ξ ⊢§ Γ → Γ ∋ A → Þ / Ξ ⊢ A
sub∋ (σ , s) zero    = s
sub∋ (σ , s) (suc i) = sub∋ σ i


----------------------------------------------------------------------------------------------------

-- substitution for derivations

sub : ∀ {Þ k} {Γ Ξ : Fm§ k} {A} → Þ / Ξ ⊢§ Γ → Þ / Γ ⊢ A → Þ / Ξ ⊢ A
sub σ (‵var i)         = sub∋ σ i
sub σ (‵lam d)         = ‵lam (sub (lift§ σ) d)
sub σ (d ‵$ e)         = sub σ d ‵$ sub σ e
sub σ (‵pair d e)      = ‵pair (sub σ d) (sub σ e)
sub σ (‵fst d)         = ‵fst (sub σ d)
sub σ (‵snd d)         = ‵snd (sub σ d)
sub σ (‵left d)        = ‵left (sub σ d)
sub σ (‵right d)       = ‵right (sub σ d)
sub σ (‵either c d e)  = ‵either (sub σ c) (sub (lift§ σ) d) (sub (lift§ σ) e)
sub σ (‵all d)         = ‵all {!!}
sub σ (‵one t refl d)  = ‵one t refl (sub σ d)
sub σ (‵this t refl d) = ‵this t refl (sub σ d)
sub σ (‵some d e)      = ‵some (sub σ d) {!!}
sub σ (‵abort d)       = ‵abort (sub σ d)
sub σ (‵magic d)       = ‵magic (sub (lift§ σ) d)
sub σ ‵refl            = ‵refl
sub σ (‵sym d)         = ‵sym (sub σ d)
sub σ (‵trans d e)     = ‵trans (sub σ d) (sub σ e)
sub σ (‵cong f i d)    = ‵cong f i (sub σ d)
sub σ ‵dis             = ‵dis
sub σ (‵inj d)         = ‵inj (sub σ d)
sub σ (‵ind d e)       = ‵ind (sub σ d) (sub σ e)
sub σ (‵proj i)        = ‵proj i
sub σ (‵comp g φ)      = ‵comp g φ
sub σ (‵rec f g)       = ‵rec f g


----------------------------------------------------------------------------------------------------

-- generic lemmas from SubKit

sub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} → Þ / Ξ ⊢§ Γ → Þ / Γ ⊢§ Δ → Þ / Ξ ⊢§ Δ
sub§ σ ∙       = ∙
sub§ σ (δ , d) = sub§ σ δ , sub σ d

-- TODO: rename
_[_]′ : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ , A ⊢ B → Þ / Γ ⊢ A → Þ / Γ ⊢ B
d [ s ]′ = sub (id§ , s) d

get§ : ∀ {Þ k} {Γ Δ Δ′ : Fm§ k} → Δ ⊑ Δ′ → Þ / Γ ⊢§ Δ′ → Þ / Γ ⊢§ Δ
get§ stop      δ       = δ
get§ (wk⊑ η)   (δ , d) = get§ η δ
get§ (lift⊑ η) (δ , d) = get§ η δ , d


----------------------------------------------------------------------------------------------------

-- derivations: fundamental renaming lemmas

lidren : ∀ {Þ k} {Γ : Fm§ k} {A} (d : Þ / Γ ⊢ A) → ren id⊑ d ≡ d
lidren (‵var i)         = ‵var & idren∋ i
lidren (‵lam d)         = ‵lam & lidren d
lidren (d ‵$ e)         = _‵$_ & lidren d ⊗ lidren e
lidren (‵pair d e)      = ‵pair & lidren d ⊗ lidren e
lidren (‵fst d)         = ‵fst & lidren d
lidren (‵snd d)         = ‵snd & lidren d
lidren (‵left d)        = ‵left & lidren d
lidren (‵right d)       = ‵right & lidren d
lidren (‵either c d e)  = ‵either & lidren c ⊗ lidren d ⊗ lidren e
lidren (‵all d)         = ‵all & {!!}
lidren (‵one t refl d)  = ‵one t refl & lidren d
lidren (‵this t refl d) = ‵this t refl & lidren d
lidren (‵some d e)      = ‵some & lidren d ⊗ {!!}
lidren (‵abort d)       = ‵abort & lidren d
lidren (‵magic d)       = ‵magic & lidren d
lidren ‵refl            = refl
lidren (‵sym d)         = ‵sym & lidren d
lidren (‵trans d e)     = ‵trans & lidren d ⊗ lidren e
lidren (‵cong f i d)    = ‵cong f i & lidren d
lidren ‵dis             = refl
lidren (‵inj d)         = ‵inj & lidren d
lidren (‵ind d e)       = ‵ind & lidren d ⊗ lidren e
lidren (‵proj i)        = refl
lidren (‵comp g φ)      = refl
lidren (‵rec f g)       = refl

compren : ∀ {Þ k} {Γ Γ′ Γ″ : Fm§ k} {A} (η′ : Γ′ ⊑ Γ″) (η : Γ ⊑ Γ′) (d : Þ / Γ ⊢ A) →
            ren (η′ ∘⊑ η) d ≡ (ren η′ ∘ ren η) d
compren η′ η (‵var i)         = ‵var & compren∋ η′ η i
compren η′ η (‵lam d)         = ‵lam & compren (lift⊑ η′) (lift⊑ η) d
compren η′ η (d ‵$ e)         = _‵$_ & compren η′ η d ⊗ compren η′ η e
compren η′ η (‵pair d e)      = ‵pair & compren η′ η d ⊗ compren η′ η e
compren η′ η (‵fst d)         = ‵fst & compren η′ η d
compren η′ η (‵snd d)         = ‵snd & compren η′ η d
compren η′ η (‵left d)        = ‵left & compren η′ η d
compren η′ η (‵right d)       = ‵right & compren η′ η d
compren η′ η (‵either c d e)  = ‵either & compren η′ η c
                                        ⊗ compren (lift⊑ η′) (lift⊑ η) d
                                        ⊗ compren (lift⊑ η′) (lift⊑ η) e
compren η′ η (‵all d)         = ‵all & {!!}
compren η′ η (‵one t refl d)  = ‵one t refl & compren η′ η d
compren η′ η (‵this t refl d) = ‵this t refl & compren η′ η d
compren η′ η (‵some d e)      = ‵some & compren η′ η d ⊗ {!!}
compren η′ η (‵abort d)       = ‵abort & compren η′ η d
compren η′ η (‵magic d)       = ‵magic & compren (lift⊑ η′) (lift⊑ η) d
compren η′ η ‵refl            = refl
compren η′ η (‵sym d)         = ‵sym & compren η′ η d
compren η′ η (‵trans d e)     = ‵trans & compren η′ η d ⊗ compren η′ η e
compren η′ η (‵cong f i d)    = ‵cong f i & compren η′ η d
compren η′ η ‵dis             = refl
compren η′ η (‵inj d)         = ‵inj & compren η′ η d
compren η′ η (‵ind d e)       = ‵ind & compren η′ η d ⊗ compren η′ η e
compren η′ η (‵proj i)        = refl
compren η′ η (‵comp g φ)      = refl
compren η′ η (‵rec f g)       = refl

ridren : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A} (η : Γ ⊑ Γ′) (i : Γ ∋ A) →
           ren {Þ} η (‵var i) ≡ ‵var (ren∋ η i)
ridren η i = refl

ridsub : ∀ {Þ k} {Γ Ξ : Fm§ k} {A} (σ : Þ / Ξ ⊢§ Γ) (i : Γ ∋ A) →
           sub σ (‵var i) ≡ sub∋ σ i
ridsub σ i = refl


----------------------------------------------------------------------------------------------------

-- generic lemmas from RenSubKit1

lidren§ : ∀ {Þ k} {Γ Δ : Fm§ k} (δ : Þ / Γ ⊢§ Δ) → ren§ id⊑ δ ≡ δ
lidren§ ∙       = refl
lidren§ (δ , d) = _,_ & lidren§ δ ⊗ lidren d

compren§ : ∀ {Þ k} {Γ Γ′ Γ″ Δ : Fm§ k} (η′ : Γ′ ⊑ Γ″) (η : Γ ⊑ Γ′) (δ : Þ / Γ ⊢§ Δ) →
             ren§ (η′ ∘⊑ η) δ ≡ (ren§ η′ ∘ ren§ η) δ
compren§ η′ η ∙       = refl
compren§ η′ η (δ , d) = _,_ & compren§ η′ η δ ⊗ compren η′ η d

eqwkren : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A C} (η : Γ ⊑ Γ′) (d : Þ / Γ ⊢ A) →
            (ren (lift⊑ η) ∘ wk) d ≡ (wk {C = C} ∘ ren η) d
eqwkren η d = compren (lift⊑ η) (wk⊑ id⊑) d ⁻¹
            ⋮ (flip ren d ∘ wk⊑) & (rid⊑ η ⋮ lid⊑ η ⁻¹)
            ⋮ compren (wk⊑ id⊑) η d

eqwkren§ : ∀ {Þ k} {Γ Γ′ Δ : Fm§ k} {C} (η : Γ ⊑ Γ′) (δ : Þ / Γ ⊢§ Δ) →
             (ren§ (lift⊑ η) ∘ wk§) δ ≡ (wk§ {C = C} ∘ ren§ η) δ
eqwkren§ η ∙       = refl
eqwkren§ η (δ , d) = _,_ & eqwkren§ η δ ⊗ eqwkren η d

eqliftren§ : ∀ {Þ k} {Γ Γ′ Δ : Fm§ k} {C} (η : Γ ⊑ Γ′) (δ : Þ / Γ ⊢§ Δ) →
               (ren§ (lift⊑ η) ∘ lift§) δ ≡ (lift§ {C = C} ∘ ren§ η) δ
eqliftren§ η δ = ((ren§ (lift⊑ η) ∘ wk§) δ ,_) & ridren (lift⊑ η) zero
               ⋮ (_, ‵var zero) & eqwkren§ η δ

ridren§ : ∀ {Þ k} {Γ Γ′ : Fm§ k} (η : Γ ⊑ Γ′) → ren§ {Þ} η id§ ≡ var§ η
ridren§ stop      = refl
ridren§ (wk⊑ η)   = (flip ren§ id§ ∘ wk⊑) & lid⊑ η ⁻¹
                  ⋮ compren§ (wk⊑ id⊑) η id§
                  ⋮ wk§ & ridren§ η
ridren§ (lift⊑ η) = ((ren§ (lift⊑ η) ∘ wk§) id§ ,_) & ridren (lift⊑ η) zero
                  ⋮ (_, ‵var zero) & (eqwkren§ η id§ ⋮ wk§ & ridren§ η)

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

idsub∋ : ∀ {Þ k} {Γ : Fm§ k} {A} (i : Γ ∋ A) → sub∋ {Þ} id§ i ≡ ‵var i
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
             (get§ (wk⊑ η) ∘ lift§) δ ≡ (wk§ {C = C} ∘ get§ η) δ
eqwkget§ η δ = eqrenget§ (wk⊑ id⊑) η δ

eqliftget§ : ∀ {Þ k} {Γ Δ Δ′ : Fm§ k} {C} (η : Δ ⊑ Δ′) (δ : Þ / Γ ⊢§ Δ′) →
               (get§ (lift⊑ η) ∘ lift§) δ ≡ (lift§ {C = C} ∘ get§ η) δ
eqliftget§ η δ = (_, ‵var zero) & eqwkget§ η δ

ridget§ : ∀ {Þ k} {Γ Γ′ : Fm§ k} (η : Γ ⊑ Γ′) → get§ {Þ} η id§ ≡ var§ η
ridget§ stop      = refl
ridget§ (wk⊑ η)   = eqrenget§ (wk⊑ id⊑) η id§
                  ⋮ wk§ & ridget§ η
ridget§ (lift⊑ η) = (_, ‵var zero) & (eqrenget§ (wk⊑ id⊑) η id§
                  ⋮ wk§ & ridget§ η)


----------------------------------------------------------------------------------------------------

-- derivations: fundamental substitution lemmas

mutual
  eqrensub : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A} (η : Ξ ⊑ Ξ′) (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ ⊢ A) →
               sub (ren§ η σ) d ≡ (ren η ∘ sub σ) d
  eqrensub η σ (‵var i)         = eqrensub∋ η σ i
  eqrensub η σ (‵lam d)         = ‵lam & eqrensub-lift η σ d
  eqrensub η σ (d ‵$ e)         = _‵$_ & eqrensub η σ d ⊗ eqrensub η σ e
  eqrensub η σ (‵pair d e)      = ‵pair & eqrensub η σ d ⊗ eqrensub η σ e
  eqrensub η σ (‵fst d)         = ‵fst & eqrensub η σ d
  eqrensub η σ (‵snd d)         = ‵snd & eqrensub η σ d
  eqrensub η σ (‵left d)        = ‵left & eqrensub η σ d
  eqrensub η σ (‵right d)       = ‵right & eqrensub η σ d
  eqrensub η σ (‵either c d e)  = ‵either & eqrensub η σ c
                                          ⊗ eqrensub-lift η σ d
                                          ⊗ eqrensub-lift η σ e
  eqrensub η σ (‵all d)         = ‵all & {!!}
  eqrensub η σ (‵one t refl d)  = ‵one t refl & eqrensub η σ d
  eqrensub η σ (‵this t refl d) = ‵this t refl & eqrensub η σ d
  eqrensub η σ (‵some d e)      = ‵some & eqrensub η σ d ⊗ {!!}
  eqrensub η σ (‵abort d)       = ‵abort & eqrensub η σ d
  eqrensub η σ (‵magic d)       = ‵magic & eqrensub-lift η σ d
  eqrensub η σ ‵refl            = refl
  eqrensub η σ (‵sym d)         = ‵sym & eqrensub η σ d
  eqrensub η σ (‵trans d e)     = ‵trans & eqrensub η σ d ⊗ eqrensub η σ e
  eqrensub η σ (‵cong f i d)    = ‵cong f i & eqrensub η σ d
  eqrensub η σ ‵dis             = refl
  eqrensub η σ (‵inj d)         = ‵inj & eqrensub η σ d
  eqrensub η σ (‵ind d e)       = ‵ind & eqrensub η σ d ⊗ eqrensub η σ e
  eqrensub η σ (‵proj i)        = refl
  eqrensub η σ (‵comp g φ)      = refl
  eqrensub η σ (‵rec f g)       = refl

  eqrensub-lift : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A B} (η : Ξ ⊑ Ξ′) (σ : Þ / Ξ ⊢§ Γ)
                    (d : Þ / Γ , A ⊢ B) →
                    sub (lift§ (ren§ η σ)) d ≡ ren (lift⊑ η) (sub (lift§ σ) d)
  eqrensub-lift η σ d = flip sub d & eqliftren§ η σ ⁻¹
                      ⋮ eqrensub (lift⊑ η) (lift§ σ) d

mutual
  eqsubren : ∀ {Þ k} {Γ Γ′ Ξ : Fm§ k} {A} (σ : Þ / Ξ ⊢§ Γ′) (η : Γ ⊑ Γ′) (d : Þ / Γ ⊢ A) →
               sub (get§ η σ) d ≡ (sub σ ∘ ren η) d
  eqsubren σ η (‵var i)         = eqsubren∋ σ η i
  eqsubren σ η (‵lam d)         = ‵lam & eqsubren-lift σ η d
  eqsubren σ η (d ‵$ e)         = _‵$_ & eqsubren σ η d ⊗ eqsubren σ η e
  eqsubren σ η (‵pair d e)      = ‵pair & eqsubren σ η d ⊗ eqsubren σ η e
  eqsubren σ η (‵fst d)         = ‵fst & eqsubren σ η d
  eqsubren σ η (‵snd d)         = ‵snd & eqsubren σ η d
  eqsubren σ η (‵left d)        = ‵left & eqsubren σ η d
  eqsubren σ η (‵right d)       = ‵right & eqsubren σ η d
  eqsubren σ η (‵either c d e)  = ‵either & eqsubren σ η c
                                          ⊗ eqsubren-lift σ η d
                                          ⊗ eqsubren-lift σ η e
  eqsubren σ η (‵all d)         = ‵all & {!!}
  eqsubren σ η (‵one t refl d)  = ‵one t refl & eqsubren σ η d
  eqsubren σ η (‵this t refl d) = ‵this t refl & eqsubren σ η d
  eqsubren σ η (‵some d e)      = ‵some & eqsubren σ η d ⊗ {!!}
  eqsubren σ η (‵abort d)       = ‵abort & eqsubren σ η d
  eqsubren σ η (‵magic d)       = ‵magic & eqsubren-lift σ η d
  eqsubren σ η ‵refl            = refl
  eqsubren σ η (‵sym d)         = ‵sym & eqsubren σ η d
  eqsubren σ η (‵trans d e)     = ‵trans & eqsubren σ η d ⊗ eqsubren σ η e
  eqsubren σ η (‵cong f i d)    = ‵cong f i & eqsubren σ η d
  eqsubren σ η ‵dis             = refl
  eqsubren σ η (‵inj d)         = ‵inj & eqsubren σ η d
  eqsubren σ η (‵ind d e)       = ‵ind & eqsubren σ η d ⊗ eqsubren σ η e
  eqsubren σ η (‵proj i)        = refl
  eqsubren σ η (‵comp g φ)      = refl
  eqsubren σ η (‵rec f g)       = refl

  eqsubren-lift : ∀ {Þ k} {Γ Γ′ Ξ : Fm§ k} {A B} (σ : Þ / Ξ ⊢§ Γ′) (η : Γ ⊑ Γ′)
                    (d : Þ / Γ , A ⊢ B) →
                    sub (lift§ (get§ η σ)) d ≡ sub (lift§ σ) (ren (lift⊑ η) d)
  eqsubren-lift σ η d = flip sub d & eqliftget§ η σ ⁻¹
                      ⋮ eqsubren (lift§ σ) (lift⊑ η) d

lidsub : ∀ {Þ k} {Γ : Fm§ k} {A} (d : Þ / Γ ⊢ A) → sub id§ d ≡ d
lidsub (‵var i)         = idsub∋ i
lidsub (‵lam d)         = ‵lam & lidsub d
lidsub (d ‵$ e)         = _‵$_ & lidsub d ⊗ lidsub e
lidsub (‵pair d e)      = ‵pair & lidsub d ⊗ lidsub e
lidsub (‵fst d)         = ‵fst & lidsub d
lidsub (‵snd d)         = ‵snd & lidsub d
lidsub (‵left d)        = ‵left & lidsub d
lidsub (‵right d)       = ‵right & lidsub d
lidsub (‵either c d e)  = ‵either & lidsub c ⊗ lidsub d ⊗ lidsub e
lidsub (‵all d)         = ‵all & lidsub d
lidsub (‵one t refl d)  = ‵one t refl & lidsub d
lidsub (‵this t refl d) = ‵this t refl & lidsub d
lidsub (‵some d e)      = ‵some & lidsub d ⊗ lidsub e
lidsub (‵abort d)       = ‵abort & lidsub d
lidsub (‵magic d)       = ‵magic & lidsub d
lidsub ‵refl            = refl
lidsub (‵sym d)         = ‵sym & lidsub d
lidsub (‵trans d e)     = ‵trans & lidsub d ⊗ lidsub e
lidsub (‵cong f i d)    = ‵cong f i & lidsub d
lidsub ‵dis             = refl
lidsub (‵inj d)         = ‵inj & lidsub d
lidsub (‵ind d e)       = ‵ind & lidsub d ⊗ lidsub e
lidsub (‵proj i)        = refl
lidsub (‵comp g φ)      = refl
lidsub (‵rec f g)       = refl


----------------------------------------------------------------------------------------------------

-- generic lemmas from RenSubKit2

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
            (sub (lift§ σ) ∘ wk) d ≡ (wk {C = C} ∘ sub σ) d
eqwksub σ d = eqsubren (lift§ σ) (wk⊑ id⊑) d ⁻¹
            ⋮ flip sub d & (eqwkget§ id⊑ σ ⋮ wk§ & lidget§ σ)
            ⋮ eqrensub (wk⊑ id⊑) σ d

eqwksub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} {C} (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
             (sub§ (lift§ σ) ∘ wk§) δ ≡ (wk§ {C = C} ∘ sub§ σ) δ
eqwksub§ σ ∙       = refl
eqwksub§ σ (δ , d) = _,_ & eqwksub§ σ δ ⊗ eqwksub σ d

eqliftsub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} {C} (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
               (sub§ (lift§ σ) ∘ lift§) δ ≡ (lift§ {C = C} ∘ sub§ σ) δ
eqliftsub§ σ δ = ((sub§ (lift§ σ) ∘ wk§) δ ,_) & ridsub (lift§ σ) zero
               ⋮ (_, ‵var zero) & eqwksub§ σ δ

ridsub§ : ∀ {Þ k} {Γ Ξ : Fm§ k} (σ : Þ / Ξ ⊢§ Γ) → sub§ σ id§ ≡ σ
ridsub§ ∙       = refl
ridsub§ (σ , s) = ((sub§ (σ , s) ∘ wk§) id§ ,_) & ridsub (σ , s) zero
                ⋮ (_, s) & (eqsub§ σ s id§ ⋮ ridsub§ σ)


----------------------------------------------------------------------------------------------------

-- derivations: more fundamental substitution lemmas

mutual
  compsub : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ ⊢ A) →
              sub (sub§ σ′ σ) d ≡ (sub σ′ ∘ sub σ) d
  compsub σ′ σ (‵var i)         = compsub∋ σ′ σ i
  compsub σ′ σ (‵lam d)         = ‵lam & compsub-lift σ′ σ d
  compsub σ′ σ (d ‵$ e)         = _‵$_ & compsub σ′ σ d ⊗ compsub σ′ σ e
  compsub σ′ σ (‵pair d e)      = ‵pair & compsub σ′ σ d ⊗ compsub σ′ σ e
  compsub σ′ σ (‵fst d)         = ‵fst & compsub σ′ σ d
  compsub σ′ σ (‵snd d)         = ‵snd & compsub σ′ σ d
  compsub σ′ σ (‵left d)        = ‵left & compsub σ′ σ d
  compsub σ′ σ (‵right d)       = ‵right & compsub σ′ σ d
  compsub σ′ σ (‵either c d e)  = ‵either & compsub σ′ σ c
                                          ⊗ compsub-lift σ′ σ d
                                          ⊗ compsub-lift σ′ σ e
  compsub σ′ σ (‵all d)         = ‵all & {!!}
  compsub σ′ σ (‵one t refl d)  = ‵one t refl & compsub σ′ σ d
  compsub σ′ σ (‵this t refl d) = ‵this t refl & compsub σ′ σ d
  compsub σ′ σ (‵some d e)      = ‵some & compsub σ′ σ d ⊗ {!!}
  compsub σ′ σ (‵abort d)       = ‵abort & compsub σ′ σ d
  compsub σ′ σ (‵magic d)       = ‵magic & compsub-lift σ′ σ d
  compsub σ′ σ ‵refl            = refl
  compsub σ′ σ (‵sym d)         = ‵sym & compsub σ′ σ d
  compsub σ′ σ (‵trans d e)     = ‵trans & compsub σ′ σ d ⊗ compsub σ′ σ e
  compsub σ′ σ (‵cong f i d)    = ‵cong f i & compsub σ′ σ d
  compsub σ′ σ ‵dis             = refl
  compsub σ′ σ (‵inj d)         = ‵inj & compsub σ′ σ d
  compsub σ′ σ (‵ind d e)       = ‵ind & compsub σ′ σ d ⊗ compsub σ′ σ e
  compsub σ′ σ (‵proj i)        = refl
  compsub σ′ σ (‵comp g φ)      = refl
  compsub σ′ σ (‵rec f g)       = refl

  compsub-lift : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A B} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ)
                   (d : Þ / Γ , A ⊢ B) →
                   sub (lift§ (sub§ σ′ σ)) d ≡ sub (lift§ σ′) (sub (lift§ σ) d)
  compsub-lift σ′ σ d = flip sub d & eqliftsub§ σ′ σ ⁻¹
                      ⋮ compsub (lift§ σ′) (lift§ σ) d


----------------------------------------------------------------------------------------------------

-- generic lemmas from RenSubKit3

asssub§ : ∀ {Þ k} {Γ Ξ Ξ′ Δ : Fm§ k} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
            (sub§ σ′ ∘ sub§ σ) δ ≡ sub§ (sub§ σ′ σ) δ
asssub§ σ′ σ ∙       = refl
asssub§ σ′ σ (δ , d) = _,_ & asssub§ σ′ σ δ ⊗ compsub σ′ σ d ⁻¹

rencut : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A B} (η : Γ ⊑ Γ′) (d : Þ / Γ , A ⊢ B) (s : Þ / Γ ⊢ A) →
           ren (lift⊑ η) d [ ren η s ]′ ≡ ren η (d [ s ]′)
rencut η d s = eqsubren (id§ , ren η s) (lift⊑ η) d ⁻¹
             ⋮ (flip sub d ∘ (_, ren η s)) & (ridget§ η ⋮ ridren§ η ⁻¹)
             ⋮ eqrensub η (id§ , s) d

subcut : ∀ {Þ k} {Γ Ξ : Fm§ k} {A B} (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ , A ⊢ B) (s : Þ / Γ ⊢ A) →
           sub (lift§ σ) d [ sub σ s ]′ ≡ sub σ (d [ s ]′)
subcut σ d s = compsub (id§ , sub σ s) (lift§ σ) d ⁻¹
             ⋮ flip sub d &
                 ( _,_ & ( eqsubren§ (id§ , sub σ s) (wk⊑ id⊑) σ ⁻¹
                         ⋮ flip sub§ σ & lidget§ id§
                         ⋮ lidsub§ σ
                         ⋮ ridsub§ σ ⁻¹
                         )
                       ⊗ ridsub (id§ , sub σ s) zero
                 )
             ⋮ compsub σ (id§ , s) d


----------------------------------------------------------------------------------------------------


-- TODO: fix these

tren? : ∀ {Þ k k′ Γ Γ′ A} (η : k ≤ k′) → Γ ⊑ Γ′ → Þ / renFm§ η Γ ⊢ A → Þ / renFm§ η Γ′ ⊢ A
tren? η ζ = ren (tren⊑ η ζ)

twk? : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A} → Γ ⊑ Γ′ → Þ / wkFm§ Γ ⊢ A → Þ / wkFm§ Γ′ ⊢ A
twk? = tren? (wk≤ id≤)


----------------------------------------------------------------------------------------------------

-- various things

⊃id : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A ‵⊃ A
⊃id = ‵lam 0

det : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ A ‵⊃ B → Þ / Γ , A ⊢ B
det d = wk d ‵$ 0

⊃ex : ∀ {Þ k} {Γ : Fm§ k} {A B C} → Þ / Γ ⊢ (A ‵⊃ B ‵⊃ C) ‵⊃ B ‵⊃ A ‵⊃ C
⊃ex = ‵lam (‵lam (‵lam ((2 ‵$ 0) ‵$ 1)))

ex : ∀ {Þ k} {Γ : Fm§ k} {A B C} → Þ / Γ , B , A ⊢ C → Þ / Γ , A , B ⊢ C
ex d = det (det (⊃ex ‵$ ‵lam (‵lam d)))

abort : ∀ {Þ k} {Γ : Fm§ k} {C} → Þ / Γ ⊢ ‵⊥ → Þ / Γ ⊢ C
abort {HA} d = ‵abort d
abort {PA} d = ‵magic (wk d)


----------------------------------------------------------------------------------------------------

-- lemma 2

lem2 : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A → PA / Γ ⊢ A
lem2 (‵var i)         = ‵var i
lem2 (‵lam d)         = ‵lam (lem2 d)
lem2 (d ‵$ e)         = lem2 d ‵$ lem2 e
lem2 (‵pair d e)      = ‵pair (lem2 d) (lem2 e)
lem2 (‵fst d)         = ‵fst (lem2 d)
lem2 (‵snd d)         = ‵snd (lem2 d)
lem2 (‵left d)        = ‵left (lem2 d)
lem2 (‵right d)       = ‵right (lem2 d)
lem2 (‵either c d e)  = ‵either (lem2 c) (lem2 d) (lem2 e)
lem2 (‵all d)         = ‵all (lem2 d)
lem2 (‵one t refl d)  = ‵one t refl (lem2 d)
lem2 (‵this t refl d) = ‵this t refl (lem2 d)
lem2 (‵some d e)      = ‵some (lem2 d) (lem2 e)
lem2 (‵abort d)       = abort (lem2 d)
lem2 (‵magic d)       = ‵magic (lem2 d)
lem2 ‵refl            = ‵refl
lem2 (‵sym d)         = ‵sym (lem2 d)
lem2 (‵trans d e)     = ‵trans (lem2 d) (lem2 e)
lem2 (‵cong f i d)    = ‵cong f i (lem2 d)
lem2 ‵dis             = ‵dis
lem2 (‵inj d)         = ‵inj (lem2 d)
lem2 (‵ind d e)       = ‵ind (lem2 d) (lem2 e)
lem2 (‵proj i)        = ‵proj i
lem2 (‵comp g φ)      = ‵comp g φ
lem2 (‵rec f g)       = ‵rec f g


----------------------------------------------------------------------------------------------------

module _ {Þ k} {Γ : Fm§ k} where
  ≡→= : ∀ {t u} → t ≡ u → Þ / Γ ⊢ t ‵= u
  ≡→= refl = ‵refl

module =-Reasoning {Þ k} {Γ : Fm§ k} where
  infix  1 begin_
  infixr 2 _=⟨⟩_ _=⟨_⟩_ _=˘⟨_⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {t u} → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ t ‵= u
  begin d = d

  _=⟨⟩_ : ∀ t {u} → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ t ‵= u
  t =⟨⟩ d = d

  _=⟨_⟩_ : ∀ s {t u} → Þ / Γ ⊢ s ‵= t → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ s ‵= u
  s =⟨ d ⟩ e = ‵trans d e

  _=˘⟨_⟩_ : ∀ s {t u} → Þ / Γ ⊢ t ‵= s → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ s ‵= u
  s =˘⟨ d ⟩ e = ‵trans (‵sym d) e

  _≡⟨_⟩_ : ∀ s {t u} → s ≡ t → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ s ‵= u
  s ≡⟨ d ⟩ e = ‵trans (≡→= d) e

  _≡˘⟨_⟩_ : ∀ s {t u} → t ≡ s → Þ / Γ ⊢ t ‵= u → Þ / Γ ⊢ s ‵= u
  s ≡˘⟨ d ⟩ e = ‵trans (≡→= (d ⁻¹)) e

  _∎ : ∀ t → Þ / Γ ⊢ t ‵= t
  t ∎ = ‵refl


----------------------------------------------------------------------------------------------------

module _ {Þ k} {Γ : Fm§ k} where
  ⫗refl : ∀ {A} → Þ / Γ ⊢ A ‵⫗ A
  ⫗refl {A} = ‵pair ⊃id ⊃id

  ⫗sym : ∀ {A B} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ B ‵⫗ A
  ⫗sym d = ‵pair (‵snd d) (‵fst d)

  ⫗trans : ∀ {A B C} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ B ‵⫗ C → Þ / Γ ⊢ A ‵⫗ C
  ⫗trans d e = ‵pair
                  (‵lam (‵fst (wk e) ‵$ ‵fst (wk d) ‵$ 0))
                  (‵lam (‵snd (wk d) ‵$ ‵snd (wk e) ‵$ 0))

  ⫗cong⊃ : ∀ {A A′ B B′} → Þ / Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ B ‵⫗ B′ →
              Þ / Γ ⊢ (A ‵⊃ B) ‵⫗ (A′ ‵⊃ B′)
  ⫗cong⊃ d e = ‵pair
                  (‵lam (‵lam
                    (‵fst (wk (wk e)) ‵$ 1 ‵$ ‵snd (wk (wk d)) ‵$ 0)))
                  (‵lam (‵lam
                    (‵snd (wk (wk e)) ‵$ 1 ‵$ ‵fst (wk (wk d)) ‵$ 0)))

  ⫗cong∧ : ∀ {A A′ B B′} → Þ / Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ B ‵⫗ B′ →
              Þ / Γ ⊢ A ‵∧ B ‵⫗ A′ ‵∧ B′
  ⫗cong∧ d e = ‵pair
                  (‵lam (‵pair
                    (‵fst (wk d) ‵$ ‵fst 0)
                    (‵fst (wk e) ‵$ ‵snd 0)))
                  (‵lam (‵pair
                    (‵snd (wk d) ‵$ ‵fst 0)
                    (‵snd (wk e) ‵$ ‵snd 0)))

  ⫗cong∨ : ∀ {A A′ B B′} → Þ / Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ B ‵⫗ B′ →
              Þ / Γ ⊢ A ‵∨ B ‵⫗ A′ ‵∨ B′
  ⫗cong∨ d e = ‵pair
                  (‵lam (‵either 0
                    (‵left (‵fst (wk (wk d)) ‵$ 0))
                    (‵right (‵fst (wk (wk e)) ‵$ 0))))
                  (‵lam (‵either 0
                    (‵left (‵snd (wk (wk d)) ‵$ 0))
                    (‵right (‵snd (wk (wk e)) ‵$ 0))))

  ⫗cong∀ : ∀ {A A′} → Þ / wkFm§ Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ (‵∀ A) ‵⫗ (‵∀ A′)
  ⫗cong∀ d = ‵pair
                (‵lam (‵all (twk? (wk⊑ id⊑) (‵fst d) ‵$ ‵one (‵var zero) TODO1 0)))
                (‵lam (‵all (twk? (wk⊑ id⊑) (‵snd d) ‵$ ‵one (‵var zero) TODO1 0)))

  ⫗cong∃ : ∀ {A A′} → Þ / wkFm§ Γ ⊢ A ‵⫗ A′ → Þ / Γ ⊢ (‵∃ A) ‵⫗ (‵∃ A′)
  ⫗cong∃ d = ‵pair
                (‵lam (‵some 0 (‵this (‵var zero) TODO1 (‵fst (wk (wk d)) ‵$ 0))))
                (‵lam (‵some 0 (‵this (‵var zero) TODO1 (‵snd (wk (wk d)) ‵$ 0))))

  ≡→⫗ : ∀ {A B} → A ≡ B → Þ / Γ ⊢ A ‵⫗ B
  ≡→⫗ refl = ⫗refl

module ⫗-Reasoning {Þ k} {Γ : Fm§ k} where
  infix  1 begin_
  infixr 2 _⫗⟨⟩_ _⫗⟨_⟩_ _⫗˘⟨_⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {A B} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ A ‵⫗ B
  begin d = d

  _⫗⟨⟩_ : ∀ A {B} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ A ‵⫗ B
  A ⫗⟨⟩ d = d

  _⫗⟨_⟩_ : ∀ A {B C} → Þ / Γ ⊢ A ‵⫗ B → Þ / Γ ⊢ B ‵⫗ C → Þ / Γ ⊢ A ‵⫗ C
  A ⫗⟨ d ⟩ e = ⫗trans d e

  _⫗˘⟨_⟩_ : ∀ A {B C} → Þ / Γ ⊢ B ‵⫗ A → Þ / Γ ⊢ B ‵⫗ C → Þ / Γ ⊢ A ‵⫗ C
  A ⫗˘⟨ d ⟩ e = ⫗trans (⫗sym d) e

  _≡⟨_⟩_ : ∀ A {B C} → A ≡ B → Þ / Γ ⊢ B ‵⫗ C → Þ / Γ ⊢ A ‵⫗ C
  A ≡⟨ d ⟩ e = ⫗trans (≡→⫗ d) e

  _≡˘⟨_⟩_ : ∀ A {B C} → B ≡ A → Þ / Γ ⊢ B ‵⫗ C → Þ / Γ ⊢ A ‵⫗ C
  A ≡˘⟨ d ⟩ e = ⫗trans (≡→⫗ (d ⁻¹)) e

  _∎ : ∀ A → Þ / Γ ⊢ A ‵⫗ A
  A ∎ = ⫗refl


----------------------------------------------------------------------------------------------------

-- meta-level continuation/double negation monad/applicative/functor
-- TODO: laws?

-- TODO: delete?
-- module ContinuationMonad where
--   infixl 4 _⊛_ _<$>_
--   infixl 1 _>>=_
--
--   return : ∀ {𝓍} {A : Set 𝓍} → A → ¬ ¬ A
--   return x = λ k → k x
--
--   _>>=_ : ∀ {𝓍 𝓎} {A : Set 𝓍} {B : Set 𝓎} → ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B
--   mx >>= f = λ k → mx (λ x → f x k)
--
--   join : ∀ {𝓍} {A : Set 𝓍} → ¬ ¬ ¬ ¬ A → ¬ ¬ A
--   join mmx = mmx >>= λ mx → mx
--
--   _⊛_ : ∀ {𝓍 𝓎} {A : Set 𝓍} {B : Set 𝓎} → ¬ ¬ (A → B) → ¬ ¬ A → ¬ ¬ B
--   mf ⊛ mx = mf >>= λ f → mx >>= λ x → return (f x)
--
--   _<$>_ : ∀ {𝓍 𝓎} {A : Set 𝓍} {B : Set 𝓎} → (A → B) → ¬ ¬ A → ¬ ¬ B
--   f <$> mx = return f ⊛ mx
--
--   dnem : ∀ {𝓍} {A : Set 𝓍} → ¬ ¬ (A ⊎ ¬ A)
--   dnem = λ k → k (right λ k′ → k (left k′))


----------------------------------------------------------------------------------------------------

-- object-level continuation/double negation monad/applicative/functor
-- ⊃-prefixed versions use object-level implication
-- ‵-prefixed versions use meta-level implication, for general ease of use
-- ⫗-prefixed versions use object-level equivalence, for use in ⫗-reasoning
-- TODO: laws?

infixl 4 _⊛_ _<$>_
infixl 1 _>>=_

⊃return : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A ‵⊃ ‵¬ ‵¬ A
⊃return = ‵lam (‵lam (0 ‵$ 1))

return : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A → Þ / Γ ⊢ ‵¬ ‵¬ A
return d = ⊃return ‵$ d

⊃bind : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ ‵¬ ‵¬ A ‵⊃ (A ‵⊃ ‵¬ ‵¬ B) ‵⊃ ‵¬ ‵¬ B
⊃bind = ‵lam (‵lam (‵lam (2 ‵$ ‵lam ((2 ‵$ 0) ‵$ 1))))

_>>=_ : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ ‵¬ ‵¬ A → Þ / Γ ⊢ A ‵⊃ ‵¬ ‵¬ B → Þ / Γ ⊢ ‵¬ ‵¬ B
d >>= e = (⊃bind ‵$ d) ‵$ e

⊃join : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ ‵¬ ‵¬ ‵¬ ‵¬ A ‵⊃ ‵¬ ‵¬ A
⊃join = ‵lam (0 >>= ⊃id)

join : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ ‵¬ ‵¬ ‵¬ ‵¬ A → Þ / Γ ⊢ ‵¬ ‵¬ A
join d = ⊃join ‵$ d

⊃apply : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ ‵¬ ‵¬ (A ‵⊃ B) ‵⊃ ‵¬ ‵¬ A ‵⊃ ‵¬ ‵¬ B
⊃apply = ‵lam (‵lam (1 >>= ‵lam (1 >>= ‵lam (return (1 ‵$ 0)))))

_⊛_ : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ ‵¬ ‵¬ (A ‵⊃ B) → Þ / Γ ⊢ ‵¬ ‵¬ A → Þ / Γ ⊢ ‵¬ ‵¬ B
d ⊛ e = d >>= ‵lam (wk e >>= ‵lam (return (1 ‵$ 0)))

⊃map : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ (A ‵⊃ B) ‵⊃ ‵¬ ‵¬ A ‵⊃ ‵¬ ‵¬ B
⊃map = ‵lam (‵lam (return 1 ⊛ 0))

_<$>_ : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ ⊢ A ‵⊃ B → Þ / Γ ⊢ ‵¬ ‵¬ A → Þ / Γ ⊢ ‵¬ ‵¬ B
d <$> e = (⊃map ‵$ d) ‵$ e

dnem : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ ‵¬ ‵¬ (A ‵∨ ‵¬ A)
dnem = ‵lam (0 ‵$ ‵right (‵lam (1 ‵$ ‵left 0)))


----------------------------------------------------------------------------------------------------

-- extended middle

⊃dne : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ ‵¬ ‵¬ A ‵⊃ A
⊃dne = ‵lam (‵magic (1 ‵$ 0))

dne : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ ‵¬ ‵¬ A → PA / Γ ⊢ A
dne d = ⊃dne ‵$ d

⫗dn : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ ‵¬ ‵¬ A ‵⫗ A
⫗dn = ‵pair ⊃dne ⊃return

em : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ A ‵∨ ‵¬ A
em = dne dnem


----------------------------------------------------------------------------------------------------

-- de Morgan’s laws

-- constructive
module _ {Þ k} {Γ : Fm§ k} where
  ⊃pdm1a : ∀ {A B} → Þ / Γ ⊢ ‵¬ A ‵∧ ‵¬ B ‵⊃ ‵¬ (A ‵∨ B)
  ⊃pdm1a = ‵lam (‵lam (‵either 0
             (‵fst 2 ‵$ 0)
             (‵snd 2 ‵$ 0)))

  ⊃qdm1a : ∀ {A} → Þ / Γ ⊢ ‵∀ (‵¬ A) ‵⊃ ‵¬ (‵∃ A)
  ⊃qdm1a = ‵lam (‵lam (‵some 0
             (‵one (‵var zero) TODO1 2 ‵$ 0)))

  ⊃npdm1a : ∀ {A B} → Þ / Γ ⊢ A ‵∧ B ‵⊃ ‵¬ (‵¬ A ‵∨ ‵¬ B)
  ⊃npdm1a = ‵lam (‵lam (abort (‵either 0
              (0 ‵$ ‵fst 2)
              (0 ‵$ ‵snd 2))))

  ⊃nqdm1a : ∀ {A} → Þ / Γ ⊢ ‵∀ A ‵⊃ ‵¬ (‵∃ (‵¬ A))
  ⊃nqdm1a = ‵lam (‵lam (abort (‵some 0
              (0 ‵$ ‵one (‵var zero) TODO1 2))))

  ⊃pdm2a : ∀ {A B} → Þ / Γ ⊢ ‵¬ A ‵∨ ‵¬ B ‵⊃ ‵¬ (A ‵∧ B)
  ⊃pdm2a = ‵lam (‵lam (‵either 1
             (0 ‵$ ‵fst 1)
             (0 ‵$ ‵snd 1)))

  ⊃qdm2a : ∀ {A} → Þ / Γ ⊢ ‵∃ (‵¬ A) ‵⊃ ‵¬ (‵∀ A)
  ⊃qdm2a = ‵lam (‵lam (‵some 1
             (0 ‵$ ‵one (‵var zero) TODO1 1)))

  ⊃npdm2a : ∀ {A B} → Þ / Γ ⊢ A ‵∨ B ‵⊃ ‵¬ (‵¬ A ‵∧ ‵¬ B)
  ⊃npdm2a = ‵lam (‵lam (abort (‵either 1
              (‵fst 1 ‵$ 0)
              (‵snd 1 ‵$ 0))))

  ⊃nqdm2a : ∀ {A} → Þ / Γ ⊢ ‵∃ A ‵⊃ ‵¬ (‵∀ (‵¬ A))
  ⊃nqdm2a = ‵lam (‵lam (abort (‵some 1
              (‵one (‵var zero) TODO1 1 ‵$ 0))))

  ⊃pdm1b : ∀ {A B} → Þ / Γ ⊢ ‵¬ (A ‵∨ B) ‵⊃ ‵¬ A ‵∧ ‵¬ B
  ⊃pdm1b = ‵lam (‵pair
             (‵lam (1 ‵$ ‵left 0))
             (‵lam (1 ‵$ ‵right 0)))

  ⊃qdm1b : ∀ {A} → Þ / Γ ⊢ ‵¬ (‵∃ A) ‵⊃ ‵∀ (‵¬ A)
  ⊃qdm1b = ‵lam (‵all (‵lam
             (1 ‵$ ‵this (‵var zero) TODO1 0)))

  ⫗pdm1 : ∀ {A B} → Þ / Γ ⊢ ‵¬ A ‵∧ ‵¬ B ‵⫗ ‵¬ (A ‵∨ B)
  ⫗pdm1 = ‵pair ⊃pdm1a ⊃pdm1b

  ⫗qdm1 : ∀ {A} → Þ / Γ ⊢ ‵∀ (‵¬ A) ‵⫗ ‵¬ (‵∃ A)
  ⫗qdm1 = ‵pair ⊃qdm1a ⊃qdm1b

-- TODO: non-constructive
-- module _ {k} {Γ : Fm§ k} where
--   ⊃npdm1b : ∀ {A B} → PA / Γ ⊢ ‵¬ (‵¬ A ‵∨ ‵¬ B) ‵⊃ A ‵∧ B
--   ⊃npdm1b = {!!}
--
--   ⊃nqdm1b : ∀ {A} → PA / Γ ⊢ ‵¬ (‵∃ (‵¬ A)) ‵⊃ ‵∀ A
--   ⊃nqdm1b = {!!}
--
--   ⊃pdm2b : ∀ {A B} → PA / Γ ⊢ ‵¬ (A ‵∧ B) ‵⊃ ‵¬ A ‵∨ ‵¬ B
--   ⊃pdm2b = {!!}
--
--   ⊃qdm2b : ∀ {A} → PA / Γ ⊢ ‵¬ (‵∀ A) ‵⊃ ‵∃ (‵¬ A)
--   ⊃qdm2b = {!!}
--
--   ⊃npdm2b : ∀ {A B} → PA / Γ ⊢ ‵¬ (‵¬ A ‵∧ ‵¬ B) ‵⊃ A ‵∨ B
--   ⊃npdm2b = {!!}
--
--   ⊃nqdm2b : ∀ {A} → PA / Γ ⊢ ‵¬ (‵∀ (‵¬ A)) ‵⊃ ‵∃ A
--   ⊃nqdm2b = {!!}
--
--   ⫗npdm1 : ∀ {A B} → PA / Γ ⊢ A ‵∧ B ‵⫗ ‵¬ (‵¬ A ‵∨ ‵¬ B)
--   ⫗npdm1 = ‵pair ⊃npdm1a ⊃npdm1b
--
--   ⫗nqdm1 : ∀ {A} → PA / Γ ⊢ ‵∀ A ‵⫗ ‵¬ (‵∃ (‵¬ A))
--   ⫗nqdm1 = ‵pair ⊃nqdm1a ⊃nqdm1b
--
--   ⫗pdm2 : ∀ {A B} → PA / Γ ⊢ ‵¬ A ‵∨ ‵¬ B ‵⫗ ‵¬ (A ‵∧ B)
--   ⫗pdm2 = ‵pair ⊃pdm2a ⊃pdm2b
--
--   ⫗qdm2 : ∀ {A} → PA / Γ ⊢ ‵∃ (‵¬ A) ‵⫗ ‵¬ (‵∀ A)
--   ⫗qdm2 = ‵pair ⊃qdm2a ⊃qdm2b
--
--   ⫗npdm2 : ∀ {A B} → PA / Γ ⊢ A ‵∨ B ‵⫗ ‵¬ (‵¬ A ‵∧ ‵¬ B)
--   ⫗npdm2 = ‵pair ⊃npdm2a ⊃npdm2b
--
--   ⫗nqdm2 : ∀ {A} → PA / Γ ⊢ ‵∃ A ‵⫗ ‵¬ (‵∀ (‵¬ A))
--   ⫗nqdm2 = ‵pair ⊃nqdm2a ⊃nqdm2b


----------------------------------------------------------------------------------------------------

-- TODO: other non-constructive tautologies

{-A     B    ¬A    ¬B    A∧B   A∨B   A⊃B   A⫗B ¬A∧B  ¬A∨B  ¬A⊃B  ¬A⫗B  A∧¬B  A∨¬B  A⊃¬B A⫗¬B
----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- -----
  0     0     1     1     0     0     1     1     0     1     0     0     0     1     1     0
  0     1     1     0     0     1     1     0     1     1     1     1     0     0     1     1
  1     0     0     1     0     1     0     0     0     0     1     1     1     1     1     1
  1     1     0     0     1     1     1     1     0     1     1     0     0     1     0     0-}

-- module _ where
--   ⫗tau1 : ∀ {A B} → PA / Γ ⊢ A ‵⊃ B ‵⫗ ‵¬ A ‵∨ B
--   ⫗tau1 = {!!}
--
--   ⫗tau2 : ∀ {A B} → PA / Γ ⊢ (‵¬ A ‵⫗ B) ‵⫗ (A ‵⫗ ‵¬ B)
--   ⫗tau2 = {!!}


----------------------------------------------------------------------------------------------------

-- quantifier-free formulas

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
--            Þ / Γ ⊢ A ‵⫗ ‵fun f (tab ‵var) ‵= ‵zero
--   lem3 (A ‵⊃ B) = {!!}
--   lem3 (A ‵∧ B) = {!!}
--   lem3 (A ‵∨ B) = {!!}
--   lem3 ‵⊥      = const 1 , ‵pair (‵lam (‵abort 0)) (‵lam (‵dis ‵$ (‵lam goal) ‵$ 0))
--                   where
--                     goal : ∀ {Þ k} {Γ : Fm§ k} →
--                              Þ / ‵fun (const 1) (tab ‵var) ‵= Γ , ‵zero ⊢ ‵suc ‵zero ‵= ‵zero
--                     goal = begin
--                              ‵suc ‵zero
--                            =⟨⟩
--                              ‵fun suc (∙ , ‵fun zero ∙)
--                            =⟨ ‵cong suc zero (
--                                begin
--                                  ‵fun zero ∙
--                                =˘⟨ ‵comp zero ∙ ⟩
--                                  ‵fun (comp zero ∙) (tab ‵var)
--                                ∎)
--                              ⟩
--                              ‵fun suc (∙ , ‵fun (comp zero ∙) (tab ‵var))
--                            =˘⟨ ‵comp suc (∙ , comp zero ∙) ⟩
--                              ‵fun (comp suc (∙ , comp zero ∙)) (tab ‵var)
--                            =⟨⟩
--                              ‵fun (const 1) (tab ‵var)
--                            =⟨ 0 ⟩
--                              ‵zero
--                            ∎
--   lem3 (t ‵= u) = {!!}


----------------------------------------------------------------------------------------------------

-- TODO: definition of Π⁰₂

-- TODO: lemma 4


----------------------------------------------------------------------------------------------------

-- double negation translation

_° : ∀ {k} → Fm k → Fm k
(A ‵⊃ B) ° = A ° ‵⊃ B °
(A ‵∧ B) ° = A ° ‵∧ B °
(A ‵∨ B) ° = ‵¬ ‵¬ (A ° ‵∨ B °)
(‵∀ A)   ° = ‵∀ (A °)
(‵∃ A)   ° = ‵¬ ‵¬ ‵∃ (A °)
‵⊥      ° = ‵⊥
(t ‵= u) ° = ‵¬ ‵¬ (t ‵= u)

_°§ : ∀ {k} → Fm§ k → Fm§ k
∙       °§ = ∙
(Γ , A) °§ = Γ °§ , A °


-- TODO: interactions between DNT and renaming/substitution

postulate
  TODO2 : ∀ {k} {A : Fm (suc k)} {t} → (A [ t ]) ° ≡ (A °) [ t ]
  TODO3 : ∀ {Þ k} {Γ : Fm§ k} {A} →
            Þ / (wkFm§ Γ) °§ ⊢ A →
            Þ / wkFm§ (Γ °§) ⊢ A
  TODO4 : ∀ {Þ k} {Γ : Fm§ k} {A t} →
            Þ / Γ ⊢ (A [ t ]) ° →
            Þ / Γ ⊢ (A °) [ t ]
  TODO5 : ∀ {Þ k} {Γ : Fm§ k} {A t} →
            Þ / Γ ⊢ ‵∀ (A ° ‵⊃ (texFm (wkFm A) [ t ]) °) →
            Þ / Γ ⊢ ‵∀ (A ° ‵⊃ texFm (wkFm (A °)) [ t ])
  TODO6 : ∀ {Þ k} {Γ : Fm§ k} {A C} →
            Þ / (wkFm§ Γ) °§ , A ° ⊢ (wkFm C) ° →
            Þ / wkFm§ (Γ °§) , A ° ⊢ wkFm (C °)


-- TODO: lemma 5

module _ where
  open ⫗-Reasoning

  lem5-1 : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ A ° ‵⫗ A
  lem5-1 {A = A ‵⊃ B} = ⫗cong⊃ lem5-1 lem5-1
  lem5-1 {A = A ‵∧ B} = ⫗cong∧ lem5-1 lem5-1
  lem5-1 {A = A ‵∨ B} = begin
                          (A ‵∨ B) °
                        ⫗⟨ ⫗dn ⟩
                          A ° ‵∨ B °
                        ⫗⟨ ⫗cong∨ lem5-1 lem5-1 ⟩
                          A ‵∨ B
                        ∎
  lem5-1 {A = ‵∀ A}   = ⫗cong∀ lem5-1
  lem5-1 {A = ‵∃ A}   = begin
                          (‵∃ A) °
                        ⫗⟨ ⫗dn ⟩
                          ‵∃ (A °)
                        ⫗⟨ ⫗cong∃ lem5-1 ⟩
                          ‵∃ A
                        ∎
  lem5-1 {A = ‵⊥}    = ⫗refl
  lem5-1 {A = t ‵= u} = ⫗dn

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
lem5-2 {A = ‵∀ A}   = ‵lam (‵all (lem5-2 ‵$ ‵lam
                         (1 ‵$ ‵lam
                           (1 ‵$ ‵one (‵var zero) TODO1 0))))
lem5-2 {A = ‵∃ A}   = ‵lam (join 0)
lem5-2 {A = ‵⊥}    = ‵lam (0 ‵$ ⊃id)
lem5-2 {A = t ‵= u} = ‵lam (join 0)

lem5-3∋ : ∀ {k} {Γ : Fm§ k} {A} → Γ ∋ A → Γ °§ ∋ A °
lem5-3∋ zero    = zero
lem5-3∋ (suc i) = suc (lem5-3∋ i)

lem5-3 : ∀ {Þ k} {Γ : Fm§ k} {A} → PA / Γ ⊢ A → Þ / Γ °§ ⊢ A °
lem5-3 (‵var i)           = ‵var (lem5-3∋ i)
lem5-3 (‵lam d)           = ‵lam (lem5-3 d)
lem5-3 (d ‵$ e)           = lem5-3 d ‵$ lem5-3 e
lem5-3 (‵pair d e)        = ‵pair (lem5-3 d) (lem5-3 e)
lem5-3 (‵fst d)           = ‵fst (lem5-3 d)
lem5-3 (‵snd d)           = ‵snd (lem5-3 d)
lem5-3 (‵left d)          = return (‵left (lem5-3 d))
lem5-3 (‵right d)         = return (‵right (lem5-3 d))
lem5-3 (‵either c d e)    = lem5-2 ‵$ (lem5-3 c >>= ‵lam (‵either 0
                              (return (ex (wk (lem5-3 d))))
                              (return (ex (wk (lem5-3 e))))))
lem5-3 (‵all d)           = ‵all (TODO3 (lem5-3 d))
lem5-3 (‵one t refl d)    = ‵one t TODO2 (lem5-3 d)
lem5-3 (‵this t refl d)   = return (‵this t TODO2 (lem5-3 d))
lem5-3 (‵some d e)        = lem5-2 ‵$ (lem5-3 d >>= ‵lam (‵some 0
                              (return (ex (wk (TODO6 (lem5-3 e)))))))
lem5-3 (‵magic d)         = lem5-2 ‵$ ‵lam (lem5-3 d)
lem5-3 ‵refl              = return (‵refl)
lem5-3 (‵sym d)           = lem5-3 d >>= ‵lam
                              (return (‵sym 0))
lem5-3 (‵trans d e)       = lem5-3 d >>= ‵lam
                              (wk (lem5-3 e) >>= ‵lam
                                (return (‵trans 1 0)))
lem5-3 (‵cong f i d)      = lem5-3 d >>= ‵lam
                              (return (‵cong f i 0))
lem5-3 ‵dis               = return ‵dis
lem5-3 (‵inj d)           = lem5-3 d >>= ‵lam
                              (return (‵inj 0))
lem5-3 (‵ind d e)         = ‵ind (TODO4 (lem5-3 d)) (TODO5 (lem5-3 e))
lem5-3 (‵proj i)          = return (‵proj i)
lem5-3 (‵comp g φ)        = return (‵comp g φ)
lem5-3 (‵rec {t = t} f g) = ‵pair
                              (return (‵fst (‵rec {t = t} f g)))
                              (return (‵snd (‵rec f g)))

-- TODO: "Note that the converse of 3 trivially holds wih 1."
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

-- A-translation

_ᴬ⟨_⟩ : ∀ {k} → Fm k → Fm k → Fm k
(A ‵⊃ B) ᴬ⟨ T ⟩ = A ᴬ⟨ T ⟩ ‵⊃ B ᴬ⟨ T ⟩
(A ‵∧ B) ᴬ⟨ T ⟩ = A ᴬ⟨ T ⟩ ‵∧ B ᴬ⟨ T ⟩
(A ‵∨ B) ᴬ⟨ T ⟩ = A ᴬ⟨ T ⟩ ‵∨ B ᴬ⟨ T ⟩
(‵∀ A)   ᴬ⟨ T ⟩ = ‵∀ (A ᴬ⟨ wkFm T ⟩)
(‵∃ A)   ᴬ⟨ T ⟩ = ‵∃ (A ᴬ⟨ wkFm T ⟩)
‵⊥      ᴬ⟨ T ⟩ = T
(t ‵= u) ᴬ⟨ T ⟩ = (t ‵= u) ‵∨ T

_ᴬ⟨_⟩§ : ∀ {k} → Fm§ k → Fm k → Fm§ k
∙       ᴬ⟨ T ⟩§ = ∙
(Γ , A) ᴬ⟨ T ⟩§ = Γ ᴬ⟨ T ⟩§ , A ᴬ⟨ T ⟩


-- TODO: interactions between A-translation and renaming/substitution

postulate
  TODO12 : ∀ {k} {A : Fm (suc k)} {T t} → (A [ t ]) ᴬ⟨ T ⟩ ≡ (A ᴬ⟨ wkFm T ⟩) [ t ]


-- TODO: lemma 6

aux1 : ∀ {k} {Γ : Fm§ k} {A B C} → PA / Γ ⊢ (A ‵∨ C) ‵⊃ (B ‵∨ C) ‵⫗ (A ‵⊃ B) ‵∨ C
aux1 = ‵pair
         (‵lam {!!}) -- TODO: non-constructive?
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



-- TODO: clean these up

tren∋ : ∀ {k k′ Γ A} (η : k ≤ k′) → Γ ∋ A → renFm§ η Γ ∋ renFm η A
tren∋ η zero    = zero
tren∋ η (suc i) = suc (tren∋ η i)

tren : ∀ {Þ k k′ Γ A} (η : k ≤ k′) → Þ / Γ ⊢ A → Þ / renFm§ η Γ ⊢ renFm η A
tren η (‵var i)         = ‵var (tren∋ η i)
tren η (‵lam d)         = ‵lam (tren η d)
tren η (d ‵$ e)         = tren η d ‵$ tren η e
tren η (‵pair d e)      = ‵pair (tren η d) (tren η e)
tren η (‵fst d)         = ‵fst (tren η d)
tren η (‵snd d)         = ‵snd (tren η d)
tren η (‵left d)        = ‵left (tren η d)
tren η (‵right d)       = ‵right (tren η d)
tren η (‵either c d e)  = ‵either (tren η c) (tren η d) (tren η e)

tren η (‵all d)         = ‵all {!tren (lift≤ η) d!}
-- Goal: Þ / twkFm§ (trenFm§ η Γ)         ⊢ trenFm (lift≤ η) A
-- Have: Þ / trenFm§ (lift≤ η) (twkFm§ Γ) ⊢ trenFm (lift≤ η) A

tren η (‵one t refl d)  = ‵one (renTm η t) {!!} (tren η d)
-- Goal: trenFm η (A [ t ]) ≡ (renFm (lift≤ η) A [ renTm η t ])

tren η (‵this t refl d) = ‵this (renTm η t) {!!} (tren η d)
-- Goal: trenFm η (A [ t ]) ≡ (renFm (lift≤ η) A [ renTm η t ])

tren η (‵some d e)      = ‵some (tren η d) {!tren (lift≤ η) e!}
-- Goal: Þ / trenFm (lift≤ η) twkFm§ (trenFm§ η Γ) , C         ⊢ twkFm (trenFm η A)
-- Have: Þ / trenFm (lift≤ η) trenFm§ (lift≤ η) (twkFm§ Γ) , C ⊢ trenFm (lift≤ η) (twkFm A)

tren η (‵abort d)       = ‵abort (tren η d)
tren η (‵magic d)       = ‵magic (tren η d)
tren η ‵refl            = ‵refl
tren η (‵sym d)         = ‵sym (tren η d)
tren η (‵trans d e)     = ‵trans (tren η d) (tren η e)
tren η (‵cong f i d)    = {!‵cong ? ? ?!}
tren η ‵dis             = ‵dis
tren η (‵inj d)         = ‵inj (tren η d)
tren η (‵ind d e)       = ‵ind {!tren (lift≤ η) ?!} {!tren (lift≤ η) ?!}
tren η (‵proj i)        = {!‵proj i!}
tren η (‵comp g φ)      = {!!}
tren η (‵rec f g)       = ‵rec f g

twk : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A → Þ / wkFm§ Γ ⊢ wkFm A
twk d = tren (wk≤ id≤) d

hmm : ∀ {k} {Γ : Fm§ k} {A C} → PA / Γ ⊢ ‵∀ (A ‵∨ wkFm C) → PA / Γ ⊢ ‵¬ C →
        PA / Γ ⊢ ‵∀ A
hmm d e = ‵all (‵either (‵one (‵var zero) TODO1 (twk d)) 0 (abort (wk (twk e) ‵$ 0)))

{-
roconnor got:
    (‵lam
      (‵all
        (twk (wk⊑ id⊑)
          (‵lam
            (‵either 0
              0
              (abort (wk (wk {!e!}) ‵$ 0))))
          ‵$ ‵one (‵var zero) TODO1 0)))
    ‵$ d

-}

aux4 : ∀ {k} {Γ : Fm§ k} {A C} → PA / Γ ⊢ ‵∀ (A ‵∨ wkFm C) ‵⫗ (‵∀ A) ‵∨ C
aux4 {Γ = Γ} {A} {C} = ‵pair
         (‵lam (‵either (em {A = C})
           (‵right 0)
           (‵left (hmm 1 0))))
         (‵lam (‵either 0
           (‵all (‵left (‵one (‵var zero) TODO1 0)))
           (‵all (‵right 0))))

aux5 : ∀ {Þ k} {Γ : Fm§ k} {A C} → Þ / Γ ⊢ ‵∃ (A ‵∨ wkFm C) ‵⫗ (‵∃ A) ‵∨ C
aux5 = ‵pair
         (‵lam (‵some 0 (‵either 0
           (‵left (‵this (‵var zero) TODO1 0))
           (‵right 0))))
         (‵lam (‵either 0
           (‵some 0
             (‵this (‵var zero) TODO9 (‵left 0)))
           (‵this 𝟘 TODO8 (‵right 0)))) -- NOTE: could also be any other number

aux6 : ∀ {Þ k} {Γ : Fm§ k} {C} → Þ / Γ ⊢ C ‵⫗ ‵⊥ ‵∨ C
aux6 = ‵pair
         (‵lam (‵right 0))
         (‵lam (‵either 0 (abort 0) (id 0)))

module _ where
  open ⫗-Reasoning

  lem6-1 : ∀ {k} {Γ : Fm§ k} {A T} → PA / Γ ⊢ A ᴬ⟨ T ⟩ ‵⫗ A ‵∨ T
  lem6-1 {A = A ‵⊃ B} {T} = begin
                              A ᴬ⟨ T ⟩ ‵⊃ B ᴬ⟨ T ⟩
                            ⫗⟨ ⫗cong⊃ lem6-1 lem6-1 ⟩
                              (A ‵∨ T) ‵⊃ (B ‵∨ T)
                            ⫗⟨ aux1 ⟩
                              (A ‵⊃ B) ‵∨ T
                            ∎
  lem6-1 {A = A ‵∧ B} {T} = begin
                              A ᴬ⟨ T ⟩ ‵∧ B ᴬ⟨ T ⟩
                            ⫗⟨ ⫗cong∧ lem6-1 lem6-1 ⟩
                              (A ‵∨ T) ‵∧ (B ‵∨ T)
                            ⫗⟨ aux2 ⟩
                              (A ‵∧ B) ‵∨ T
                            ∎
  lem6-1 {A = A ‵∨ B} {T} = begin
                              A ᴬ⟨ T ⟩ ‵∨ B ᴬ⟨ T ⟩
                            ⫗⟨ ⫗cong∨ lem6-1 lem6-1 ⟩
                              (A ‵∨ T) ‵∨ (B ‵∨ T)
                            ⫗⟨ aux3 ⟩
                              (A ‵∨ B) ‵∨ T
                            ∎
  lem6-1 {A = ‵∀ A}   {T} = begin
                              ‵∀ (A ᴬ⟨ wkFm T ⟩)
                            ⫗⟨ ⫗cong∀ lem6-1 ⟩
                              ‵∀ (A ‵∨ wkFm T)
                            ⫗⟨ aux4 ⟩
                              (‵∀ A) ‵∨ T
                            ∎
  lem6-1 {A = ‵∃ A}   {T} = begin
                              ‵∃ (A ᴬ⟨ wkFm T ⟩)
                            ⫗⟨ ⫗cong∃ lem6-1 ⟩
                              ‵∃ (A ‵∨ wkFm T)
                            ⫗⟨ aux5 ⟩
                              (‵∃ A) ‵∨ T
                            ∎
  lem6-1 {A = ‵⊥}    {T} = aux6
  lem6-1 {A = t ‵= u} {T} = ⫗refl

lem6-2 : ∀ {Þ k} {Γ : Fm§ k} {A T} → Þ / Γ ⊢ T ‵⊃ A ᴬ⟨ T ⟩
lem6-2 {A = A ‵⊃ B} = ‵lam (‵lam (lem6-2 ‵$ 1)) -- NOTE: function argument ignored
lem6-2 {A = A ‵∧ B} = ‵lam (‵pair (lem6-2 ‵$ 0) (lem6-2 ‵$ 0))
lem6-2 {A = A ‵∨ B} = ‵lam (‵left (lem6-2 ‵$ 0)) -- NOTE: could also be ‵right
lem6-2 {A = ‵∀ A}   = ‵lam (‵all (lem6-2 ‵$ 0))
lem6-2 {A = ‵∃ A}   = {!!}
-- ‵lam (‵this Z TODO12 (lem6-2 {A = A [ Z ]} ‵$ 0)) -- TODO: termination failure
lem6-2 {A = ‵⊥}    = ⊃id
lem6-2 {A = t ‵= u} = ‵lam (‵right 0)

lem6-3∋ : ∀ {k} {Γ : Fm§ k} {A T} → Γ ∋ A → Γ ᴬ⟨ T ⟩§ ∋ A ᴬ⟨ T ⟩
lem6-3∋ zero    = zero
lem6-3∋ (suc i) = suc (lem6-3∋ i)

-- TODO: "The proof of 3 is a bit tricky where eigenvariable conditions are involved."
lem6-3 : ∀ {Þ k} {Γ : Fm§ k} {A T} → Þ / Γ ⊢ A → Þ / Γ ᴬ⟨ T ⟩§ ⊢ A ᴬ⟨ T ⟩
lem6-3 (‵var i)        = ‵var (lem6-3∋ i)
lem6-3 (‵lam d)        = ‵lam (lem6-3 d)
lem6-3 (d ‵$ e)        = lem6-3 d ‵$ lem6-3 e
lem6-3 (‵pair d e)     = ‵pair (lem6-3 d) (lem6-3 e)
lem6-3 (‵fst d)        = ‵fst (lem6-3 d)
lem6-3 (‵snd d)        = ‵snd (lem6-3 d)
lem6-3 (‵left d)       = ‵left (lem6-3 d)
lem6-3 (‵right d)      = ‵right (lem6-3 d)
lem6-3 (‵either c d e) = ‵either (lem6-3 c) (lem6-3 d) (lem6-3 e)
lem6-3 (‵all d)        = {!!}
lem6-3 (‵one t p d)    = {!!}
lem6-3 (‵this t p d)   = {!!}
lem6-3 (‵some d e)     = {!!}
lem6-3 (‵abort d)      = {!lem6-3 d!}
lem6-3 (‵magic d)      = {!!}
lem6-3 ‵refl           = ‵left ‵refl
lem6-3 (‵sym d)        = ‵either (lem6-3 d)
                           (‵left (‵sym 0))
                           (‵right 0)
lem6-3 (‵trans d e)    = ‵either (lem6-3 d)
                           (‵either (wk (lem6-3 e))
                             (‵left (‵trans 1 0))
                             (‵right 0))
                           (‵right 0)
lem6-3 (‵cong f i d)   = {!!}
lem6-3 ‵dis            = {!!}
lem6-3 (‵inj d)        = {!!}
lem6-3 (‵ind d e)      = {!!}
lem6-3 (‵proj i)       = {!!}
lem6-3 (‵comp g φ)     = {!!}
lem6-3 (‵rec f g)      = {!!}

-- TODO: "A counterexample for 4 is A = ¬¬T."
-- lem6-4 : ∀ {k} {Γ : Fm§ k} → ¬ (∀ {T} → HA / Γ , ‵¬ ‵¬ T ⊢ (‵¬ ‵¬ T) ᴬ⟨ T ⟩)
-- lem6-4 = {!!}


----------------------------------------------------------------------------------------------------

-- TODO: lemma 7

-- TODO: corollary 8

-- TODO: theorem 1


----------------------------------------------------------------------------------------------------
