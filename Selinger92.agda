-- 2025-03-21
-- Friedman’s A-Translation
-- https://www.mscs.dal.ca/~selinger/papers/friedman.pdf
-- thanks to ncf and roconnor

module Selinger92 where

open import Agda.Builtin.FromNat using (Number ; fromNat)

open import Data.Empty using (⊥)

import Data.Fin as Fin
open Fin using (Fin ; zero ; suc)

import Data.List as List
open List using (List ; [] ; _∷_)

import Data.Nat as Nat
open Nat using (zero ; suc)
  renaming (ℕ to Nat)

open import Data.Product using (Σ ; _,_ ; _×_)
  renaming (proj₁ to fst ; proj₂ to snd)

open import Data.Sum using (_⊎_)
  renaming (inj₁ to left ; inj₂ to right)

open import Data.Unit using (⊤ ; tt)

import Data.Vec as Vec
open Vec using (Vec ; [] ; _∷_)
  renaming (tabulate to tab)

import Data.Vec.Properties as Vec

open import Function using (_∘_ ; _$_ ; const ; flip ; id)

import Level
open Level using (_⊔_ ; Level)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; subst ; cong ; cong₂ ; module ≡-Reasoning)

open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
  renaming (contradiction to _↯_)

open import Relation.Nullary.Decidable using (True)


----------------------------------------------------------------------------------------------------

-- missing things

coe : ∀ {𝒶} {A A′ : Set 𝒶} → A ≡ A′ → A → A′
coe = subst id

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

-- vector things

get : ∀ {𝒶} {A : Set 𝒶} {n} → Fin n → Vec A n → A
get i xs = Vec.lookup xs i

put : ∀ {𝒶} {A : Set 𝒶} {n} → Fin n → Vec A n → A → Vec A n
put i xs y = xs Vec.[ i ]≔ y

for : ∀ {𝒶 𝒷} {A : Set 𝒶} {B : Set 𝒷} {n} → Vec A n → (A → B) → Vec B n
for xs f = Vec.map f xs


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

renFin : ∀ {k k′} → k ≤ k′ → Fin k → Fin k′
renFin stop      i       = i
renFin (wk≤ η)   i       = suc (renFin η i)
renFin (lift≤ η) zero    = zero
renFin (lift≤ η) (suc i) = renFin (wk≤ η) i

wkFin : ∀ {k} → Fin k → Fin (suc k)
wkFin = renFin (wk≤ id≤)


----------------------------------------------------------------------------------------------------

-- primitive recursive n-ary functions on naturals
-- Troelstra (1973) §1.3.4

mutual
  data Prim : Nat → Set where
    zero : Prim 0
    suc  : Prim 1
    proj : ∀ {n} (i : Fin n) → Prim n
    comp : ∀ {n m} (g : Prim m) (fs : Prim§ n m) → Prim n
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
#zero [] = zero

#suc : Fun 1
#suc (x ∷ []) = suc x

#proj : ∀ {n} → Fin n → Fun n
#proj i xs = get i xs

#comp : ∀ {n m} → Fun m → Fun§ n m → Fun n
#comp g fs xs = g (for fs (_$ xs))

#rec : ∀ {n} → Fun n → Fun (suc (suc n)) → Fun (suc n)
#rec f g (zero  ∷ ys) = f ys
#rec f g (suc x ∷ ys) = g (#rec f g (x ∷ ys) ∷ x ∷ ys)

mutual
  ⟦_⟧ : ∀ {n} → Prim n → Fun n
  ⟦ zero ⟧      = #zero
  ⟦ suc ⟧       = #suc
  ⟦ proj i ⟧    = #proj i
  ⟦ comp g fs ⟧ = #comp ⟦ g ⟧ ⟦ fs ⟧§
  ⟦ rec f g ⟧   = #rec ⟦ f ⟧ ⟦ g ⟧

  ⟦_⟧§ : ∀ {n m} → Prim§ n m → Fun§ n m
  ⟦ [] ⟧§     = []
  ⟦ f ∷ fs ⟧§ = ⟦ f ⟧ ∷ ⟦ fs ⟧§


----------------------------------------------------------------------------------------------------

-- some primitive recursive n-ary functions on naturals
-- Troelstra and van Dalen (1988) §1.3

ƒconst : ∀ {n} → Nat → Prim n
ƒconst zero    = comp zero []
ƒconst (suc x) = comp suc (ƒconst x ∷ [])

ok-const : ∀ x → ⟦ ƒconst x ⟧ [] ≡ const {B = Nat§ 0} x []
ok-const zero    = refl
ok-const (suc x) = cong suc (ok-const x)

-- NOTE: for reference only
-- _+_ : Nat → Nat → Nat
-- zero  + y = y
-- suc x + y = suc (x + y)

ƒadd : Prim 2
ƒadd = rec (proj 0)
         (comp suc (proj 0 ∷ []))

ok-add : ∀ x y → ⟦ ƒadd ⟧ (x ∷ y ∷ []) ≡ x Nat.+ y
ok-add zero    y = refl
ok-add (suc x) y = cong suc (ok-add x y)

-- NOTE: for reference only
-- _*_ : Nat → Nat → Nat
-- zero  * y = zero
-- suc x * y = y + x * y

ƒmul : Prim 2
ƒmul = rec (ƒconst 0)
         (comp ƒadd (proj 2 ∷ proj 0 ∷ []))

module _ where
  open ≡-Reasoning

  ok-mul : ∀ x y → ⟦ ƒmul ⟧ (x ∷ y ∷ []) ≡ x Nat.* y
  ok-mul zero    y = refl
  ok-mul (suc x) y = begin
                       ⟦ ƒadd ⟧ (y ∷ ⟦ ƒmul ⟧ (x ∷ y ∷ []) ∷ [])
                     ≡⟨ cong (⟦ ƒadd ⟧ ∘ (y ∷_)) (cong (_∷ []) (ok-mul x y))  ⟩
                       ⟦ ƒadd ⟧ (y ∷ x Nat.* y ∷ [])
                     ≡⟨ ok-add y (x Nat.* y) ⟩
                       y Nat.+ x Nat.* y
                     ∎

-- NOTE: for reference only
-- pred : Nat → Nat
-- pred x = x ∸ 1

ƒpred : Prim 1
ƒpred = rec (ƒconst 0)
          (proj 1)

ok-pred : ∀ x → ⟦ ƒpred ⟧ (x ∷ []) ≡ Nat.pred x
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

-- first-order predicate logic with one sort (naturals) and one predicate (equality)

infix  19 _‵=_ _‵≠_
infixl 18 _‵∧_
infixl 17 _‵∨_
infixr 16 _‵⊃_
infixr 15 _‵⫗_
infixr 14 _‵$_

-- terms, indexed by number of term variables
mutual
  data Tm (k : Nat) : Set where
    ‵tvar : ∀ (i : Fin k) → Tm k -- i-th term variable
    ‵fun  : ∀ {n} (f : Prim n) (ts : Tm§ k n) → Tm k

  Tm§ : Nat → Nat → Set
  Tm§ k n = Vec (Tm k) n

-- NOTE: literals for term variables in terms
-- TODO: delete?
-- instance
--   numberTm : ∀ {k} → Number (Tm k)
--   numberTm {k} = record
--     { Constraint = λ m → True (m Nat.<? k)
--     ; fromNat    = λ m {{p}} → ‵tvar ((Fin.# m) {k} {p})
--     }

Z : ∀ {k} → Tm k
Z = ‵fun zero []

S : ∀ {k} → Tm k → Tm k
S t = ‵fun suc (t ∷ [])

-- NOTE: literals for naturals encoded as object-level primitive recursive functions
-- TODO: delete?
-- module _ where
--   natTm : ∀ {k} → Nat → Tm k
--   natTm zero    = zeroTm
--   natTm (suc m) = sucTm (natTm m)
--
--   instance
--     numberTm : ∀ {k} → Number (Tm k)
--     numberTm {k} = record
--       { Constraint = λ _ → ⊤
--       ; fromNat    = λ m → natTm m
--       }

-- formulas, indexed by number of term variables
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

_‵⫗_ : ∀ {k} → Fm k → Fm k → Fm k
A ‵⫗ B = (A ‵⊃ B) ‵∧ (B ‵⊃ A)

‵¬_ : ∀ {k} → Fm k → Fm k
‵¬ A = A ‵⊃ ‵⊥

_‵≠_ : ∀ {k} → Tm k → Tm k → Fm k
t ‵≠ u = ‵¬ (t ‵= u)


----------------------------------------------------------------------------------------------------

-- typed de Bruijn indices and order-preserving embeddings for derivation variables

infix 3 _∋_
data _∋_ {k} : Fm§ k → Fm k → Set where
  zero : ∀ {Γ A} → A ∷ Γ ∋ A
  suc  : ∀ {Γ A C} (i : Γ ∋ A) → C ∷ Γ ∋ A

-- NOTE: literals for standalone derivation variables
module _ where
  infix 3 _∋⟨_⟩_
  data _∋⟨_⟩_ {k} : Fm§ k → Nat → Fm k → Set where
    instance
      zero : ∀ {Γ A} → A ∷ Γ ∋⟨ zero ⟩ A
    suc : ∀ {Γ m A C} (i : Γ ∋⟨ m ⟩ A) → C ∷ Γ ∋⟨ suc m ⟩ A

  instance
    suc∋# : ∀ {k} {Γ : Fm§ k} {m A C} {{i : Γ ∋⟨ m ⟩ A}} → C ∷ Γ ∋⟨ suc m ⟩ A
    suc∋# {{i}} = suc i

  ∋#→∋ : ∀ {m k} {Γ : Fm§ k} {A} → Γ ∋⟨ m ⟩ A → Γ ∋ A
  ∋#→∋ zero    = zero
  ∋#→∋ (suc i) = suc (∋#→∋ i)

  instance
    number∋ : ∀ {k} {Γ : Fm§ k} {A} → Number (Γ ∋ A)
    number∋ {Γ = Γ} {A} = record
      { Constraint = λ m → Γ ∋⟨ m ⟩ A
      ; fromNat    = λ m {{p}} → ∋#→∋ p
      }

infix 3 _⊆_
data _⊆_ {k} : Fm§ k → Fm§ k → Set where
  stop  : [] ⊆ []
  wk⊆   : ∀ {Γ Γ′ C} (η : Γ ⊆ Γ′) → Γ ⊆ C ∷ Γ′
  lift⊆ : ∀ {Γ Γ′ C} (η : Γ ⊆ Γ′) → C ∷ Γ ⊆ C ∷ Γ′

id⊆ : ∀ {k} {Γ : Fm§ k} → Γ ⊆ Γ
id⊆ {Γ = []}    = stop
id⊆ {Γ = A ∷ Γ} = lift⊆ id⊆

ren∋ : ∀ {k} {Γ Γ′ : Fm§ k} {A} → Γ ⊆ Γ′ → Γ ∋ A → Γ′ ∋ A
ren∋ stop      i       = i
ren∋ (wk⊆ η)   i       = suc (ren∋ η i)
ren∋ (lift⊆ η) zero    = zero
ren∋ (lift⊆ η) (suc i) = ren∋ (wk⊆ η) i

wk∋ : ∀ {k} {Γ : Fm§ k} {A C} → Γ ∋ A → C ∷ Γ ∋ A
wk∋ = ren∋ (wk⊆ id⊆)


----------------------------------------------------------------------------------------------------

-- renaming for terms and formulas

mutual
  trenTm : ∀ {k k′} → k ≤ k′ → Tm k → Tm k′
  trenTm η (‵tvar i)   = ‵tvar (renFin η i)
  trenTm η (‵fun f ts) = ‵fun f (trenTm§ η ts)

  trenTm§ : ∀ {k k′ n} → k ≤ k′ → Tm§ k n → Tm§ k′ n
  trenTm§ η []       = []
  trenTm§ η (t ∷ ts) = trenTm η t ∷ trenTm§ η ts

trenFm : ∀ {k k′} → k ≤ k′ → Fm k → Fm k′
trenFm η (A ‵⊃ B) = trenFm η A ‵⊃ trenFm η B
trenFm η (A ‵∧ B) = trenFm η A ‵∧ trenFm η B
trenFm η (A ‵∨ B) = trenFm η A ‵∨ trenFm η B
trenFm η (‵∀ A)   = ‵∀ trenFm (lift≤ η) A
trenFm η (‵∃ A)   = ‵∃ trenFm (lift≤ η) A
trenFm η ‵⊥      = ‵⊥
trenFm η (t ‵= u) = trenTm η t ‵= trenTm η u

trenFm§ : ∀ {k k′} → k ≤ k′ → Fm§ k → Fm§ k′
trenFm§ η []      = []
trenFm§ η (A ∷ Γ) = trenFm η A ∷ trenFm§ η Γ

-- weaken formula by adding one unused term variable
twkFm : ∀ {k} → Fm k → Fm (suc k)
twkFm = trenFm (wk≤ id≤)

-- weaken formulas by adding one unused term variable
twkFm§ : ∀ {k} → Fm§ k → Fm§ (suc k)
twkFm§ = trenFm§ (wk≤ id≤)

-- TODO: comment!
tren⊆ : ∀ {k k′ Γ Γ′} (η : k ≤ k′) → Γ ⊆ Γ′ → trenFm§ η Γ ⊆ trenFm§ η Γ′
tren⊆ η stop      = stop
tren⊆ η (wk⊆ ζ)   = wk⊆ (tren⊆ η ζ)
tren⊆ η (lift⊆ ζ) = lift⊆ (tren⊆ η ζ)

-- TODO: comment!
twk⊆ : ∀ {k} {Γ Γ′ : Fm§ k} → Γ ⊆ Γ′ → twkFm§ Γ ⊆ twkFm§ Γ′
twk⊆ = tren⊆ (wk≤ id≤)


----------------------------------------------------------------------------------------------------

-- TODO: substitution for terms and formulas

postulate
  -- exchange two topmost term variables in formula
  texFm : ∀ {k} (A : Fm (suc (suc k))) → Fm (suc (suc k))

  -- substitute topmost term variable in formula by term
  _[_] : ∀ {k} (A : Fm (suc k)) (s : Tm k) → Fm k

  TODO0 : ∀ {k} {A : Fm k} {t} → A ≡ twkFm A [ t ]
  TODO1 : ∀ {k} {A : Fm (suc k)} → A ≡ trenFm (lift≤ (wk≤ id≤)) A [ ‵tvar zero ]
  TODO7 : ∀ {k} {A : Fm (suc k)} {B t} → A [ t ] ‵∨ B [ t ] ≡ (A ‵∨ B) [ t ]

module _ where
  open ≡-Reasoning

  TODO8 : ∀ {k} {A : Fm (suc k)} {B t} → A [ t ] ‵∨ B ≡ (A ‵∨ twkFm B) [ t ]
  TODO8 {A = A} {B} {t} =
      begin
        A [ t ] ‵∨ B
      ≡⟨ cong₂ _‵∨_ refl TODO0 ⟩
        A [ t ] ‵∨ twkFm B [ t ]
      ≡⟨ TODO7 ⟩
        (A ‵∨ twkFm B) [ t ]
      ∎

  TODO9 : ∀ {k} {A : Fm (suc k)} {B} → A ‵∨ twkFm B ≡
            (trenFm (lift≤ (wk≤ id≤)) A ‵∨ trenFm (lift≤ (wk≤ id≤)) (twkFm B)) [ ‵tvar zero ]
  TODO9 {A = A} {B} =
      begin
        A ‵∨ twkFm B
      ≡⟨ cong₂ _‵∨_ TODO1 TODO1 ⟩
        (trenFm (lift≤ (wk≤ id≤)) A [ ‵tvar zero ]) ‵∨
          (trenFm (lift≤ (wk≤ id≤)) (twkFm B) [ ‵tvar zero ])
      ≡⟨ TODO7 ⟩
        (trenFm (lift≤ (wk≤ id≤)) A ‵∨ trenFm (lift≤ (wk≤ id≤)) (twkFm B)) [ ‵tvar zero ]
      ∎


----------------------------------------------------------------------------------------------------

-- Heyting and Peano arithmetic
data Theory : Set where
  HA : Theory
  PA : Theory

-- derivations, indexed by list of derivation variables
infix 3 _/_⊢_
data _/_⊢_ {k} : Theory → Fm§ k → Fm k → Set where
  ‵var     : ∀ {Θ Γ A} (i : Γ ∋ A) → Θ / Γ ⊢ A -- i-th derivation variable
  ‵lam     : ∀ {Θ Γ A B} (d : Θ / A ∷ Γ ⊢ B) → Θ / Γ ⊢ A ‵⊃ B
  _‵$_     : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A ‵⊃ B) (e : Θ / Γ ⊢ A) → Θ / Γ ⊢ B
  ‵pair    : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A) (e : Θ / Γ ⊢ B) → Θ / Γ ⊢ A ‵∧ B
  ‵fst     : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A ‵∧ B) → Θ / Γ ⊢ A
  ‵snd     : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A ‵∧ B) → Θ / Γ ⊢ B
  ‵left    : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A) → Θ / Γ ⊢ A ‵∨ B
  ‵right   : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ B) → Θ / Γ ⊢ A ‵∨ B
  ‵either  : ∀ {Θ Γ A B C} (c : Θ / Γ ⊢ A ‵∨ B) (d : Θ / A ∷ Γ ⊢ C) (e : Θ / B ∷ Γ ⊢ C) →
               Θ / Γ ⊢ C

  --     A(x₀)
  -- --------------
  --   ∀y.A[y/xₒ]
  ‵all     : ∀ {Θ Γ A} (d : Θ / twkFm§ Γ ⊢ A) → Θ / Γ ⊢ ‵∀ A

  --   ∀y.A[y/x₀]
  -- --------------
  --    A[t/x₀]
  ‵one     : ∀ {Θ Γ A A′} t (p : A′ ≡ A [ t ]) (d : Θ / Γ ⊢ ‵∀ A) → Θ / Γ ⊢ A′

  --    A[t/x₀]
  -- --------------
  --   ∃y.A[y/x₀]
  ‵this    : ∀ {Θ Γ A A′} t (p : A′ ≡ A [ t ]) (d : Θ / Γ ⊢ A′) → Θ / Γ ⊢ ‵∃ A

  --                 A(x₀)
  --                   ⋮
  --   ∃y.A[y/x₀]      C
  -- -----------------------
  --           C
  ‵some    : ∀ {Θ Γ A C} (d : Θ / Γ ⊢ ‵∃ A) (e : Θ / A ∷ twkFm§ Γ ⊢ twkFm C) → Θ / Γ ⊢ C

  -- explosion (ex falso quodlibet) as primitive in Heyting arithmetic
  ‵HAabort : ∀ {Γ C} (d : HA / Γ ⊢ ‵⊥) → HA / Γ ⊢ C

  -- double negation elimination (reductio ad absurdum) as primitive in Peano arithmetic
  ‵PAmagic : ∀ {Γ A} (d : PA / ‵¬ A ∷ Γ ⊢ ‵⊥) → PA / Γ ⊢ A

  ‵refl    : ∀ {Θ Γ t} → Θ / Γ ⊢ t ‵= t
  ‵sym     : ∀ {Θ Γ t u} (d : Θ / Γ ⊢ t ‵= u) → Θ / Γ ⊢ u ‵= t
  ‵trans   : ∀ {Θ Γ s t u} (d : Θ / Γ ⊢ s ‵= t) (e : Θ / Γ ⊢ t ‵= u) → Θ / Γ ⊢ s ‵= u

  ‵cong    : ∀ {Θ Γ n ts u} (f : Prim n) (i : Fin n) (d : Θ / Γ ⊢ get i ts ‵= u) →
               Θ / Γ ⊢ ‵fun f ts ‵= ‵fun f (put i ts u)

  ‵dis     : ∀ {Θ Γ t} → Θ / Γ ⊢ S t ‵≠ Z

  ‵inj     : ∀ {Θ Γ t u} (d : Θ / Γ ⊢ S t ‵= S u) → Θ / Γ ⊢ t ‵= u

  --   A[0/x₀]    ∀y.A[y/x₀]→A[y+1/x₀]
  -- ------------------------------------
  --              ∀y.A[y/x₀]
  ‵ind     : ∀ {Θ Γ A} (d : Θ / Γ ⊢ A [ Z ])
               (e : Θ / Γ ⊢ ‵∀ (A ‵⊃ (texFm (twkFm A)) [ S (‵tvar zero) ])) →
               Θ / Γ ⊢ ‵∀ A

  ‵proj    : ∀ {Θ Γ n ts} (i : Fin n) → Θ / Γ ⊢ ‵fun (proj i) ts ‵= get i ts

  ‵comp    : ∀ {Θ Γ n m ts} (g : Prim m) (fs : Prim§ n m) →
               Θ / Γ ⊢ ‵fun (comp g fs) ts ‵= ‵fun g (for fs λ f → ‵fun f ts)

  ‵rec     : ∀ {Θ Γ n s ts} (f : Prim n) (g : Prim (suc (suc n))) →
               Θ / Γ ⊢ ‵fun (rec f g) (Z ∷ ts) ‵= ‵fun f ts ‵∧
                 ‵fun (rec f g) (S s ∷ ts) ‵= ‵fun g (‵fun (rec f g) (s ∷ ts) ∷ s ∷ ts)

-- NOTE: literals for derivation variables in terms
instance
  number⊢ : ∀ {Θ k} {Γ : Fm§ k} {A} → Number (Θ / Γ ⊢ A)
  number⊢ {Γ = Γ} {A} = record
    { Constraint = λ m → Γ ∋⟨ m ⟩ A
    ; fromNat    = λ m {{p}} → ‵var (∋#→∋ p)
    }


----------------------------------------------------------------------------------------------------

-- renaming for derivations

ren : ∀ {Θ k} {Γ Γ′ : Fm§ k} {A} → Γ ⊆ Γ′ → Θ / Γ ⊢ A → Θ / Γ′ ⊢ A
ren η (‵var i)         = ‵var (ren∋ η i)
ren η (‵lam d)         = ‵lam (ren (lift⊆ η) d)
ren η (d ‵$ e)         = ren η d ‵$ ren η e
ren η (‵pair d e)      = ‵pair (ren η d) (ren η e)
ren η (‵fst d)         = ‵fst (ren η d)
ren η (‵snd d)         = ‵snd (ren η d)
ren η (‵left d)        = ‵left (ren η d)
ren η (‵right d)       = ‵right (ren η d)
ren η (‵either c d e)  = ‵either (ren η c) (ren (lift⊆ η) d) (ren (lift⊆ η) e)
ren η (‵all d)         = ‵all (ren (twk⊆ η) d)
ren η (‵one t refl d)  = ‵one t refl (ren η d)
ren η (‵this t refl d) = ‵this t refl (ren η d)
ren η (‵some d e)      = ‵some (ren η d) (ren (lift⊆ (twk⊆ η)) e)
ren η (‵HAabort d)     = ‵HAabort (ren η d)
ren η (‵PAmagic d)     = ‵PAmagic (ren (lift⊆ η) d)
ren η ‵refl            = ‵refl
ren η (‵sym d)         = ‵sym (ren η d)
ren η (‵trans d e)     = ‵trans (ren η d) (ren η e)
ren η (‵cong f i d)    = ‵cong f i (ren η d)
ren η ‵dis             = ‵dis
ren η (‵inj d)         = ‵inj (ren η d)
ren η (‵ind d e)       = ‵ind (ren η d) (ren η e)
ren η (‵proj i)        = ‵proj i
ren η (‵comp g fs)     = ‵comp g fs
ren η (‵rec f g)       = ‵rec f g

-- weaken derivation by adding one unused derivation variable
wk : ∀ {Θ k} {Γ : Fm§ k} {A C} → Θ / Γ ⊢ A → Θ / C ∷ Γ ⊢ A
wk = ren (wk⊆ id⊆)


-- TODO: fix these

tren? : ∀ {Θ k k′ Γ Γ′ A} (η : k ≤ k′) → Γ ⊆ Γ′ → Θ / trenFm§ η Γ ⊢ A → Θ / trenFm§ η Γ′ ⊢ A
tren? η ζ = ren (tren⊆ η ζ)

twk? : ∀ {Θ k} {Γ Γ′ : Fm§ k} {A} → Γ ⊆ Γ′ → Θ / twkFm§ Γ ⊢ A → Θ / twkFm§ Γ′ ⊢ A
twk? = tren? (wk≤ id≤)


----------------------------------------------------------------------------------------------------

-- various things

⊃id : ∀ {Θ k} {Γ : Fm§ k} {A} → Θ / Γ ⊢ A ‵⊃ A
⊃id = ‵lam 0

det : ∀ {Θ k} {Γ : Fm§ k} {A B} → Θ / Γ ⊢ A ‵⊃ B → Θ / A ∷ Γ ⊢ B
det d = wk d ‵$ 0

⊃ex : ∀ {Θ k} {Γ : Fm§ k} {A B C} → Θ / Γ ⊢ (A ‵⊃ B ‵⊃ C) ‵⊃ B ‵⊃ A ‵⊃ C
⊃ex = ‵lam (‵lam (‵lam ((2 ‵$ 0) ‵$ 1)))

ex : ∀ {Θ k} {Γ : Fm§ k} {A B C} → Θ / B ∷ A ∷ Γ ⊢ C → Θ / A ∷ B ∷ Γ ⊢ C
ex d = det (det (⊃ex ‵$ ‵lam (‵lam d)))

abort : ∀ {Θ k} {Γ : Fm§ k} {C} → Θ / Γ ⊢ ‵⊥ → Θ / Γ ⊢ C
abort {HA} d = ‵HAabort d
abort {PA} d = ‵PAmagic (wk d)


----------------------------------------------------------------------------------------------------

-- lemma 2

lem2 : ∀ {Θ k} {Γ : Fm§ k} {A} → Θ / Γ ⊢ A → PA / Γ ⊢ A
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
lem2 (‵HAabort d)     = abort (lem2 d)
lem2 (‵PAmagic d)     = ‵PAmagic (lem2 d)
lem2 ‵refl            = ‵refl
lem2 (‵sym d)         = ‵sym (lem2 d)
lem2 (‵trans d e)     = ‵trans (lem2 d) (lem2 e)
lem2 (‵cong f i d)    = ‵cong f i (lem2 d)
lem2 ‵dis             = ‵dis
lem2 (‵inj d)         = ‵inj (lem2 d)
lem2 (‵ind d e)       = ‵ind (lem2 d) (lem2 e)
lem2 (‵proj i)        = ‵proj i
lem2 (‵comp g fs)     = ‵comp g fs
lem2 (‵rec f g)       = ‵rec f g


----------------------------------------------------------------------------------------------------

module _ {Θ k} {Γ : Fm§ k} where
  ≡→= : ∀ {t u} → t ≡ u → Θ / Γ ⊢ t ‵= u
  ≡→= refl = ‵refl

module =-Reasoning {Θ k} {Γ : Fm§ k} where
  infix  1 begin_
  infixr 2 _=⟨⟩_ _=⟨_⟩_ _=˘⟨_⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {t u} → Θ / Γ ⊢ t ‵= u → Θ / Γ ⊢ t ‵= u
  begin d = d

  _=⟨⟩_ : ∀ t {u} → Θ / Γ ⊢ t ‵= u → Θ / Γ ⊢ t ‵= u
  t =⟨⟩ d = d

  _=⟨_⟩_ : ∀ s {t u} → Θ / Γ ⊢ s ‵= t → Θ / Γ ⊢ t ‵= u → Θ / Γ ⊢ s ‵= u
  s =⟨ d ⟩ e = ‵trans d e

  _=˘⟨_⟩_ : ∀ s {t u} → Θ / Γ ⊢ t ‵= s → Θ / Γ ⊢ t ‵= u → Θ / Γ ⊢ s ‵= u
  s =˘⟨ d ⟩ e = ‵trans (‵sym d) e

  _≡⟨_⟩_ : ∀ s {t u} → s ≡ t → Θ / Γ ⊢ t ‵= u → Θ / Γ ⊢ s ‵= u
  s ≡⟨ d ⟩ e = ‵trans (≡→= d) e

  _≡˘⟨_⟩_ : ∀ s {t u} → t ≡ s → Θ / Γ ⊢ t ‵= u → Θ / Γ ⊢ s ‵= u
  s ≡˘⟨ d ⟩ e = ‵trans (≡→= (sym d)) e

  _∎ : ∀ t → Θ / Γ ⊢ t ‵= t
  t ∎ = ‵refl


----------------------------------------------------------------------------------------------------

module _ {Θ k} {Γ : Fm§ k} where
  ⫗refl : ∀ {A} → Θ / Γ ⊢ A ‵⫗ A
  ⫗refl {A} = ‵pair ⊃id ⊃id

  ⫗sym : ∀ {A B} → Θ / Γ ⊢ A ‵⫗ B → Θ / Γ ⊢ B ‵⫗ A
  ⫗sym d = ‵pair (‵snd d) (‵fst d)

  ⫗trans : ∀ {A B C} → Θ / Γ ⊢ A ‵⫗ B → Θ / Γ ⊢ B ‵⫗ C → Θ / Γ ⊢ A ‵⫗ C
  ⫗trans d e = ‵pair
                  (‵lam (‵fst (wk e) ‵$ ‵fst (wk d) ‵$ 0))
                  (‵lam (‵snd (wk d) ‵$ ‵snd (wk e) ‵$ 0))

  ⫗cong⊃ : ∀ {A A′ B B′} → Θ / Γ ⊢ A ‵⫗ A′ → Θ / Γ ⊢ B ‵⫗ B′ →
              Θ / Γ ⊢ (A ‵⊃ B) ‵⫗ (A′ ‵⊃ B′)
  ⫗cong⊃ d e = ‵pair
                  (‵lam (‵lam
                    (‵fst (wk (wk e)) ‵$ 1 ‵$ ‵snd (wk (wk d)) ‵$ 0)))
                  (‵lam (‵lam
                    (‵snd (wk (wk e)) ‵$ 1 ‵$ ‵fst (wk (wk d)) ‵$ 0)))

  ⫗cong∧ : ∀ {A A′ B B′} → Θ / Γ ⊢ A ‵⫗ A′ → Θ / Γ ⊢ B ‵⫗ B′ →
              Θ / Γ ⊢ A ‵∧ B ‵⫗ A′ ‵∧ B′
  ⫗cong∧ d e = ‵pair
                  (‵lam (‵pair
                    (‵fst (wk d) ‵$ ‵fst 0)
                    (‵fst (wk e) ‵$ ‵snd 0)))
                  (‵lam (‵pair
                    (‵snd (wk d) ‵$ ‵fst 0)
                    (‵snd (wk e) ‵$ ‵snd 0)))

  ⫗cong∨ : ∀ {A A′ B B′} → Θ / Γ ⊢ A ‵⫗ A′ → Θ / Γ ⊢ B ‵⫗ B′ →
              Θ / Γ ⊢ A ‵∨ B ‵⫗ A′ ‵∨ B′
  ⫗cong∨ d e = ‵pair
                  (‵lam (‵either 0
                    (‵left (‵fst (wk (wk d)) ‵$ 0))
                    (‵right (‵fst (wk (wk e)) ‵$ 0))))
                  (‵lam (‵either 0
                    (‵left (‵snd (wk (wk d)) ‵$ 0))
                    (‵right (‵snd (wk (wk e)) ‵$ 0))))

  ⫗cong∀ : ∀ {A A′} → Θ / twkFm§ Γ ⊢ A ‵⫗ A′ → Θ / Γ ⊢ (‵∀ A) ‵⫗ (‵∀ A′)
  ⫗cong∀ d = ‵pair
                (‵lam (‵all (twk? (wk⊆ id⊆) (‵fst d) ‵$ ‵one (‵tvar zero) TODO1 0)))
                (‵lam (‵all (twk? (wk⊆ id⊆) (‵snd d) ‵$ ‵one (‵tvar zero) TODO1 0)))

  ⫗cong∃ : ∀ {A A′} → Θ / twkFm§ Γ ⊢ A ‵⫗ A′ → Θ / Γ ⊢ (‵∃ A) ‵⫗ (‵∃ A′)
  ⫗cong∃ d = ‵pair
                (‵lam (‵some 0 (‵this (‵tvar zero) TODO1 (‵fst (wk (wk d)) ‵$ 0))))
                (‵lam (‵some 0 (‵this (‵tvar zero) TODO1 (‵snd (wk (wk d)) ‵$ 0))))

  ≡→⫗ : ∀ {A B} → A ≡ B → Θ / Γ ⊢ A ‵⫗ B
  ≡→⫗ refl = ⫗refl

module ⫗-Reasoning {Θ k} {Γ : Fm§ k} where
  infix  1 begin_
  infixr 2 _⫗⟨⟩_ _⫗⟨_⟩_ _⫗˘⟨_⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {A B} → Θ / Γ ⊢ A ‵⫗ B → Θ / Γ ⊢ A ‵⫗ B
  begin d = d

  _⫗⟨⟩_ : ∀ A {B} → Θ / Γ ⊢ A ‵⫗ B → Θ / Γ ⊢ A ‵⫗ B
  A ⫗⟨⟩ d = d

  _⫗⟨_⟩_ : ∀ A {B C} → Θ / Γ ⊢ A ‵⫗ B → Θ / Γ ⊢ B ‵⫗ C → Θ / Γ ⊢ A ‵⫗ C
  A ⫗⟨ d ⟩ e = ⫗trans d e

  _⫗˘⟨_⟩_ : ∀ A {B C} → Θ / Γ ⊢ B ‵⫗ A → Θ / Γ ⊢ B ‵⫗ C → Θ / Γ ⊢ A ‵⫗ C
  A ⫗˘⟨ d ⟩ e = ⫗trans (⫗sym d) e

  _≡⟨_⟩_ : ∀ A {B C} → A ≡ B → Θ / Γ ⊢ B ‵⫗ C → Θ / Γ ⊢ A ‵⫗ C
  A ≡⟨ d ⟩ e = ⫗trans (≡→⫗ d) e

  _≡˘⟨_⟩_ : ∀ A {B C} → B ≡ A → Θ / Γ ⊢ B ‵⫗ C → Θ / Γ ⊢ A ‵⫗ C
  A ≡˘⟨ d ⟩ e = ⫗trans (≡→⫗ (sym d)) e

  _∎ : ∀ A → Θ / Γ ⊢ A ‵⫗ A
  A ∎ = ⫗refl


----------------------------------------------------------------------------------------------------

-- meta-level continuation/double negation monad/applicative/functor
-- TODO: laws?

-- TODO: delete?
-- module ContinuationMonad where
--   infixl 4 _⊛_ _<$>_
--   infixl 1 _>>=_
--
--   return : ∀ {𝒶} {A : Set 𝒶} → A → ¬ ¬ A
--   return x = λ k → k x
--
--   _>>=_ : ∀ {𝒶 𝒷} {A : Set 𝒶} {B : Set 𝒷} → ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B
--   mx >>= f = λ k → mx (λ x → f x k)
--
--   join : ∀ {𝒶} {A : Set 𝒶} → ¬ ¬ ¬ ¬ A → ¬ ¬ A
--   join mmx = mmx >>= λ mx → mx
--
--   _⊛_ : ∀ {𝒶 𝒷} {A : Set 𝒶} {B : Set 𝒷} → ¬ ¬ (A → B) → ¬ ¬ A → ¬ ¬ B
--   mf ⊛ mx = mf >>= λ f → mx >>= λ x → return (f x)
--
--   _<$>_ : ∀ {𝒶 𝒷} {A : Set 𝒶} {B : Set 𝒷} → (A → B) → ¬ ¬ A → ¬ ¬ B
--   f <$> mx = return f ⊛ mx
--
--   dnem : ∀ {𝒶} {A : Set 𝒶} → ¬ ¬ (A ⊎ ¬ A)
--   dnem = λ k → k (right λ k′ → k (left k′))


----------------------------------------------------------------------------------------------------

-- object-level continuation/double negation monad/applicative/functor
-- ⊃-prefixed versions use object-level implication
-- ‵-prefixed versions use meta-level implication, for general ease of use
-- ⫗-prefixed versions use object-level equivalence, for use in ⫗-reasoning
-- TODO: laws?

infixl 4 _⊛_ _<$>_
infixl 1 _>>=_

⊃return : ∀ {Θ k} {Γ : Fm§ k} {A} → Θ / Γ ⊢ A ‵⊃ ‵¬ ‵¬ A
⊃return = ‵lam (‵lam (0 ‵$ 1))

return : ∀ {Θ k} {Γ : Fm§ k} {A} → Θ / Γ ⊢ A → Θ / Γ ⊢ ‵¬ ‵¬ A
return d = ⊃return ‵$ d

⊃bind : ∀ {Θ k} {Γ : Fm§ k} {A B} → Θ / Γ ⊢ ‵¬ ‵¬ A ‵⊃ (A ‵⊃ ‵¬ ‵¬ B) ‵⊃ ‵¬ ‵¬ B
⊃bind = ‵lam (‵lam (‵lam (2 ‵$ ‵lam ((2 ‵$ 0) ‵$ 1))))

_>>=_ : ∀ {Θ k} {Γ : Fm§ k} {A B} → Θ / Γ ⊢ ‵¬ ‵¬ A → Θ / Γ ⊢ A ‵⊃ ‵¬ ‵¬ B → Θ / Γ ⊢ ‵¬ ‵¬ B
d >>= e = (⊃bind ‵$ d) ‵$ e

⊃join : ∀ {Θ k} {Γ : Fm§ k} {A} → Θ / Γ ⊢ ‵¬ ‵¬ ‵¬ ‵¬ A ‵⊃ ‵¬ ‵¬ A
⊃join = ‵lam (0 >>= ⊃id)

join : ∀ {Θ k} {Γ : Fm§ k} {A} → Θ / Γ ⊢ ‵¬ ‵¬ ‵¬ ‵¬ A → Θ / Γ ⊢ ‵¬ ‵¬ A
join d = ⊃join ‵$ d

⊃apply : ∀ {Θ k} {Γ : Fm§ k} {A B} → Θ / Γ ⊢ ‵¬ ‵¬ (A ‵⊃ B) ‵⊃ ‵¬ ‵¬ A ‵⊃ ‵¬ ‵¬ B
⊃apply = ‵lam (‵lam (1 >>= ‵lam (1 >>= ‵lam (return (1 ‵$ 0)))))

_⊛_ : ∀ {Θ k} {Γ : Fm§ k} {A B} → Θ / Γ ⊢ ‵¬ ‵¬ (A ‵⊃ B) → Θ / Γ ⊢ ‵¬ ‵¬ A → Θ / Γ ⊢ ‵¬ ‵¬ B
d ⊛ e = d >>= ‵lam (wk e >>= ‵lam (return (1 ‵$ 0)))

⊃map : ∀ {Θ k} {Γ : Fm§ k} {A B} → Θ / Γ ⊢ (A ‵⊃ B) ‵⊃ ‵¬ ‵¬ A ‵⊃ ‵¬ ‵¬ B
⊃map = ‵lam (‵lam (return 1 ⊛ 0))

_<$>_ : ∀ {Θ k} {Γ : Fm§ k} {A B} → Θ / Γ ⊢ A ‵⊃ B → Θ / Γ ⊢ ‵¬ ‵¬ A → Θ / Γ ⊢ ‵¬ ‵¬ B
d <$> e = (⊃map ‵$ d) ‵$ e

dnem : ∀ {Θ k} {Γ : Fm§ k} {A} → Θ / Γ ⊢ ‵¬ ‵¬ (A ‵∨ ‵¬ A)
dnem = ‵lam (0 ‵$ ‵right (‵lam (1 ‵$ ‵left 0)))


----------------------------------------------------------------------------------------------------

-- extended middle

⊃dne : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ ‵¬ ‵¬ A ‵⊃ A
⊃dne = ‵lam (‵PAmagic (1 ‵$ 0))

dne : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ ‵¬ ‵¬ A → PA / Γ ⊢ A
dne d = ⊃dne ‵$ d

⫗dn : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ ‵¬ ‵¬ A ‵⫗ A
⫗dn = ‵pair ⊃dne ⊃return

em : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ A ‵∨ ‵¬ A
em = dne dnem


----------------------------------------------------------------------------------------------------

-- de Morgan’s laws

-- constructive
module _ {Θ k} {Γ : Fm§ k} where
  ⊃pdm1a : ∀ {A B} → Θ / Γ ⊢ ‵¬ A ‵∧ ‵¬ B ‵⊃ ‵¬ (A ‵∨ B)
  ⊃pdm1a = ‵lam (‵lam (‵either 0
             (‵fst 2 ‵$ 0)
             (‵snd 2 ‵$ 0)))

  ⊃qdm1a : ∀ {A} → Θ / Γ ⊢ ‵∀ (‵¬ A) ‵⊃ ‵¬ (‵∃ A)
  ⊃qdm1a = ‵lam (‵lam (‵some 0
             (‵one (‵tvar zero) TODO1 2 ‵$ 0)))

  ⊃npdm1a : ∀ {A B} → Θ / Γ ⊢ A ‵∧ B ‵⊃ ‵¬ (‵¬ A ‵∨ ‵¬ B)
  ⊃npdm1a = ‵lam (‵lam (abort (‵either 0
              (0 ‵$ ‵fst 2)
              (0 ‵$ ‵snd 2))))

  ⊃nqdm1a : ∀ {A} → Θ / Γ ⊢ ‵∀ A ‵⊃ ‵¬ (‵∃ (‵¬ A))
  ⊃nqdm1a = ‵lam (‵lam (abort (‵some 0
              (0 ‵$ ‵one (‵tvar zero) TODO1 2))))

  ⊃pdm2a : ∀ {A B} → Θ / Γ ⊢ ‵¬ A ‵∨ ‵¬ B ‵⊃ ‵¬ (A ‵∧ B)
  ⊃pdm2a = ‵lam (‵lam (‵either 1
             (0 ‵$ ‵fst 1)
             (0 ‵$ ‵snd 1)))

  ⊃qdm2a : ∀ {A} → Θ / Γ ⊢ ‵∃ (‵¬ A) ‵⊃ ‵¬ (‵∀ A)
  ⊃qdm2a = ‵lam (‵lam (‵some 1
             (0 ‵$ ‵one (‵tvar zero) TODO1 1)))

  ⊃npdm2a : ∀ {A B} → Θ / Γ ⊢ A ‵∨ B ‵⊃ ‵¬ (‵¬ A ‵∧ ‵¬ B)
  ⊃npdm2a = ‵lam (‵lam (abort (‵either 1
              (‵fst 1 ‵$ 0)
              (‵snd 1 ‵$ 0))))

  ⊃nqdm2a : ∀ {A} → Θ / Γ ⊢ ‵∃ A ‵⊃ ‵¬ (‵∀ (‵¬ A))
  ⊃nqdm2a = ‵lam (‵lam (abort (‵some 1
              (‵one (‵tvar zero) TODO1 1 ‵$ 0))))

  ⊃pdm1b : ∀ {A B} → Θ / Γ ⊢ ‵¬ (A ‵∨ B) ‵⊃ ‵¬ A ‵∧ ‵¬ B
  ⊃pdm1b = ‵lam (‵pair
             (‵lam (1 ‵$ ‵left 0))
             (‵lam (1 ‵$ ‵right 0)))

  ⊃qdm1b : ∀ {A} → Θ / Γ ⊢ ‵¬ (‵∃ A) ‵⊃ ‵∀ (‵¬ A)
  ⊃qdm1b = ‵lam (‵all (‵lam
             (1 ‵$ ‵this (‵tvar zero) TODO1 0)))

  ⫗pdm1 : ∀ {A B} → Θ / Γ ⊢ ‵¬ A ‵∧ ‵¬ B ‵⫗ ‵¬ (A ‵∨ B)
  ⫗pdm1 = ‵pair ⊃pdm1a ⊃pdm1b

  ⫗qdm1 : ∀ {A} → Θ / Γ ⊢ ‵∀ (‵¬ A) ‵⫗ ‵¬ (‵∃ A)
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
--   lem3 : ∀ {Θ k} {Γ : Fm§ k} (A : Fm k) {{_ : IsQFree A}} → Σ (Prim k) λ f →
--            Θ / Γ ⊢ A ‵⫗ ‵fun f (tab ‵tvar) ‵= ‵zero
--   lem3 (A ‵⊃ B) = {!!}
--   lem3 (A ‵∧ B) = {!!}
--   lem3 (A ‵∨ B) = {!!}
--   lem3 ‵⊥      = const 1 , ‵pair (‵lam (‵abort 0)) (‵lam (‵dis ‵$ (‵lam goal) ‵$ 0))
--                   where
--                     goal : ∀ {Θ k} {Γ : Fm§ k} →
--                              Θ / ‵fun (const 1) (tab ‵tvar) ‵= ‵zero ∷ Γ ⊢ ‵suc ‵zero ‵= ‵zero
--                     goal = begin
--                              ‵suc ‵zero
--                            =⟨⟩
--                              ‵fun suc (‵fun zero [] ∷ [])
--                            =⟨ ‵cong suc zero (
--                                begin
--                                  ‵fun zero []
--                                =˘⟨ ‵comp zero [] ⟩
--                                  ‵fun (comp zero []) (tab ‵tvar)
--                                ∎)
--                              ⟩
--                              ‵fun suc (‵fun (comp zero []) (tab ‵tvar) ∷ [])
--                            =˘⟨ ‵comp suc (comp zero [] ∷ []) ⟩
--                              ‵fun (comp suc (comp zero [] ∷ [])) (tab ‵tvar)
--                            =⟨⟩
--                              ‵fun (const 1) (tab ‵tvar)
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
[]      °§ = []
(A ∷ Γ) °§ = A ° ∷ Γ °§


-- TODO: interactions between DNT and renaming/substitution

postulate
  TODO2 : ∀ {k} {A : Fm (suc k)} {t} → (A [ t ]) ° ≡ (A °) [ t ]
  TODO3 : ∀ {Θ k} {Γ : Fm§ k} {A} →
            Θ / (twkFm§ Γ) °§ ⊢ A →
            Θ / twkFm§ (Γ °§) ⊢ A
  TODO4 : ∀ {Θ k} {Γ : Fm§ k} {A t} →
            Θ / Γ ⊢ (A [ t ]) ° →
            Θ / Γ ⊢ (A °) [ t ]
  TODO5 : ∀ {Θ k} {Γ : Fm§ k} {A t} →
            Θ / Γ ⊢ ‵∀ (A ° ‵⊃ (texFm (twkFm A) [ t ]) °) →
            Θ / Γ ⊢ ‵∀ (A ° ‵⊃ texFm (twkFm (A °)) [ t ])
  TODO6 : ∀ {Θ k} {Γ : Fm§ k} {A C} →
            Θ / A ° ∷ (twkFm§ Γ) °§ ⊢ (twkFm C) ° →
            Θ / A ° ∷ twkFm§ (Γ °§) ⊢ twkFm (C °)


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

lem5-2 : ∀ {Θ k} {Γ : Fm§ k} {A} → Θ / Γ ⊢ ‵¬ ‵¬ (A °) ‵⊃ A °
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
                           (1 ‵$ ‵one (‵tvar zero) TODO1 0))))
lem5-2 {A = ‵∃ A}   = ‵lam (join 0)
lem5-2 {A = ‵⊥}    = ‵lam (0 ‵$ ⊃id)
lem5-2 {A = t ‵= u} = ‵lam (join 0)

lem5-3∋ : ∀ {k} {Γ : Fm§ k} {A} → Γ ∋ A → Γ °§ ∋ A °
lem5-3∋ zero    = zero
lem5-3∋ (suc i) = suc (lem5-3∋ i)

lem5-3 : ∀ {Θ k} {Γ : Fm§ k} {A} → PA / Γ ⊢ A → Θ / Γ °§ ⊢ A °
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
lem5-3 (‵PAmagic d)       = lem5-2 ‵$ ‵lam (lem5-3 d)
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
lem5-3 (‵comp g fs)       = return (‵comp g fs)
lem5-3 (‵rec {s = s} f g) = ‵pair
                              (return (‵fst (‵rec {s = s} f g)))
                              (return (‵snd (‵rec f g)))

-- TODO: "Note that the converse of 3 trivially holds wih 1."
lem5-3⁻¹ : ∀ {Θ k} {Γ : Fm§ k} {A} → Θ / Γ °§ ⊢ A ° → PA / Γ ⊢ A
lem5-3⁻¹ d = aux (‵fst lem5-1 ‵$ lem2 d)
  where
    aux : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ °§ ⊢ A → PA / Γ ⊢ A
    aux {Γ = []}    d = d
    aux {Γ = B ∷ Γ} d = wk (aux (‵lam d)) ‵$ (‵snd lem5-1 ‵$ 0)

-- TODO: "A counterexample for 4 is ¬∀y.A[y/x₀]."
-- lem5-4 : ∀ {k} {Γ : Fm§ k} → ¬ (∀ {A} → HA / ‵¬ (‵∀ A) ∷ Γ ⊢ (‵¬ (‵∀ A)) °)
-- lem5-4 = {!!}


----------------------------------------------------------------------------------------------------

-- A-translation

_ᴬ⟨_⟩ : ∀ {k} → Fm k → Fm k → Fm k
(A ‵⊃ B) ᴬ⟨ T ⟩ = A ᴬ⟨ T ⟩ ‵⊃ B ᴬ⟨ T ⟩
(A ‵∧ B) ᴬ⟨ T ⟩ = A ᴬ⟨ T ⟩ ‵∧ B ᴬ⟨ T ⟩
(A ‵∨ B) ᴬ⟨ T ⟩ = A ᴬ⟨ T ⟩ ‵∨ B ᴬ⟨ T ⟩
(‵∀ A)   ᴬ⟨ T ⟩ = ‵∀ (A ᴬ⟨ twkFm T ⟩)
(‵∃ A)   ᴬ⟨ T ⟩ = ‵∃ (A ᴬ⟨ twkFm T ⟩)
‵⊥      ᴬ⟨ T ⟩ = T
(t ‵= u) ᴬ⟨ T ⟩ = (t ‵= u) ‵∨ T

_ᴬ⟨_⟩§ : ∀ {k} → Fm§ k → Fm k → Fm§ k
[]      ᴬ⟨ T ⟩§ = []
(A ∷ Γ) ᴬ⟨ T ⟩§ = A ᴬ⟨ T ⟩ ∷ Γ ᴬ⟨ T ⟩§


-- TODO: interactions between A-translation and renaming/substitution

postulate
  TODO12 : ∀ {k} {A : Fm (suc k)} {T t} → (A [ t ]) ᴬ⟨ T ⟩ ≡ (A ᴬ⟨ twkFm T ⟩) [ t ]


-- TODO: lemma 6

aux1 : ∀ {k} {Γ : Fm§ k} {A B C} → PA / Γ ⊢ (A ‵∨ C) ‵⊃ (B ‵∨ C) ‵⫗ (A ‵⊃ B) ‵∨ C
aux1 = ‵pair
         (‵lam {!!}) -- TODO: non-constructive?
         (‵lam (‵lam (‵either 0
           (‵either 2
             (‵left (0 ‵$ 1))
             (‵right 0))
           (‵right 0))))

aux2 : ∀ {Θ k} {Γ : Fm§ k} {A B C} → Θ / Γ ⊢ (A ‵∨ C) ‵∧ (B ‵∨ C) ‵⫗ (A ‵∧ B) ‵∨ C
aux2 = ‵pair
         (‵lam (‵either (‵fst 0)
           (‵either (‵snd 1)
             (‵left (‵pair 1 0))
             (‵right 0))
           (‵right 0)))
         (‵lam (‵either 0
           (‵pair (‵left (‵fst 0)) (‵left (‵snd 0)))
           (‵pair (‵right 0) (‵right 0))))

aux3 : ∀ {Θ k} {Γ : Fm§ k} {A B C} → Θ / Γ ⊢ (A ‵∨ C) ‵∨ (B ‵∨ C) ‵⫗ (A ‵∨ B) ‵∨ C
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

tren∋ : ∀ {k k′ Γ A} (η : k ≤ k′) → Γ ∋ A → trenFm§ η Γ ∋ trenFm η A
tren∋ η zero    = zero
tren∋ η (suc i) = suc (tren∋ η i)

tren : ∀ {Θ k k′ Γ A} (η : k ≤ k′) → Θ / Γ ⊢ A → Θ / trenFm§ η Γ ⊢ trenFm η A
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
-- Goal: Θ / twkFm§ (trenFm§ η Γ)         ⊢ trenFm (lift≤ η) A
-- Have: Θ / trenFm§ (lift≤ η) (twkFm§ Γ) ⊢ trenFm (lift≤ η) A

tren η (‵one t refl d)  = ‵one (trenTm η t) {!!} (tren η d)
-- Goal: trenFm η (A [ t ]) ≡ (trenFm (lift≤ η) A [ trenTm η t ])

tren η (‵this t refl d) = ‵this (trenTm η t) {!!} (tren η d)
-- Goal: trenFm η (A [ t ]) ≡ (trenFm (lift≤ η) A [ trenTm η t ])

tren η (‵some d e)      = ‵some (tren η d) {!tren (lift≤ η) e!}
-- Goal: Θ / trenFm (lift≤ η) A₁ ∷ twkFm§ (trenFm§ η Γ)         ⊢ twkFm (trenFm η A)
-- Have: Θ / trenFm (lift≤ η) A₁ ∷ trenFm§ (lift≤ η) (twkFm§ Γ) ⊢ trenFm (lift≤ η) (twkFm A)

tren η (‵HAabort d)     = ‵HAabort (tren η d)
tren η (‵PAmagic d)     = ‵PAmagic (tren η d)
tren η ‵refl            = ‵refl
tren η (‵sym d)         = ‵sym (tren η d)
tren η (‵trans d e)     = ‵trans (tren η d) (tren η e)
tren η (‵cong f i d)    = {!!}
tren η ‵dis             = ‵dis
tren η (‵inj d)         = ‵inj (tren η d)
tren η (‵ind d e)       = {!!}
tren η (‵proj i)        = {!!}
tren η (‵comp g fs)     = {!!}
tren η (‵rec f g)       = ‵rec f g

twk : ∀ {Θ k} {Γ : Fm§ k} {A} → Θ / Γ ⊢ A → Θ / twkFm§ Γ ⊢ twkFm A
twk d = tren (wk≤ id≤) d

hmm : ∀ {k} {Γ : Fm§ k} {A C} → PA / Γ ⊢ ‵∀ (A ‵∨ twkFm C) → PA / Γ ⊢ ‵¬ C →
        PA / Γ ⊢ ‵∀ A
hmm d e = ‵all (‵either (‵one (‵tvar zero) TODO1 (twk d)) 0 (abort (wk (twk e) ‵$ 0)))


{-
roconnor got:
    (‵lam
      (‵all
        (twk (wk⊆ id⊆)
          (‵lam
            (‵either 0
              0
              (abort (wk (wk {!e!}) ‵$ 0))))
          ‵$ ‵one (‵tvar zero) TODO1 0)))
    ‵$ d

-}

aux4 : ∀ {k} {Γ : Fm§ k} {A C} → PA / Γ ⊢ ‵∀ (A ‵∨ twkFm C) ‵⫗ (‵∀ A) ‵∨ C
aux4 {Γ = Γ} {A} {C} = ‵pair
         (‵lam (‵either (em {A = C})
           (‵right 0)
           (‵left (hmm 1 0))))
         (‵lam (‵either 0
           (‵all (‵left (‵one (‵tvar zero) TODO1 0)))
           (‵all (‵right 0))))

aux5 : ∀ {Θ k} {Γ : Fm§ k} {A C} → Θ / Γ ⊢ ‵∃ (A ‵∨ twkFm C) ‵⫗ (‵∃ A) ‵∨ C
aux5 = ‵pair
         (‵lam (‵some 0 (‵either 0
           (‵left (‵this (‵tvar zero) TODO1 0))
           (‵right 0))))
         (‵lam (‵either 0
           (‵some 0
             (‵this (‵tvar zero) TODO9 (‵left 0)))
           (‵this Z TODO8 (‵right 0)))) -- NOTE: could also be any other number

aux6 : ∀ {Θ k} {Γ : Fm§ k} {C} → Θ / Γ ⊢ C ‵⫗ ‵⊥ ‵∨ C
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
                              ‵∀ (A ᴬ⟨ twkFm T ⟩)
                            ⫗⟨ ⫗cong∀ lem6-1 ⟩
                              ‵∀ (A ‵∨ twkFm T)
                            ⫗⟨ aux4 ⟩
                              (‵∀ A) ‵∨ T
                            ∎
  lem6-1 {A = ‵∃ A}   {T} = begin
                              ‵∃ (A ᴬ⟨ twkFm T ⟩)
                            ⫗⟨ ⫗cong∃ lem6-1 ⟩
                              ‵∃ (A ‵∨ twkFm T)
                            ⫗⟨ aux5 ⟩
                              (‵∃ A) ‵∨ T
                            ∎
  lem6-1 {A = ‵⊥}    {T} = aux6
  lem6-1 {A = t ‵= u} {T} = ⫗refl

lem6-2 : ∀ {Θ k} {Γ : Fm§ k} {A T} → Θ / Γ ⊢ T ‵⊃ A ᴬ⟨ T ⟩
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
lem6-3 : ∀ {Θ k} {Γ : Fm§ k} {A T} → Θ / Γ ⊢ A → Θ / Γ ᴬ⟨ T ⟩§ ⊢ A ᴬ⟨ T ⟩
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
lem6-3 (‵HAabort d)    = {!lem6-3 d!}
lem6-3 (‵PAmagic d)    = {!!}
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
lem6-3 (‵comp g fs)    = {!!}
lem6-3 (‵rec f g)      = {!!}

-- TODO: "A counterexample for 4 is A = ¬¬T."
-- lem6-4 : ∀ {k} {Γ : Fm§ k} → ¬ (∀ {T} → HA / ‵¬ ‵¬ T ∷ Γ ⊢ (‵¬ ‵¬ T) ᴬ⟨ T ⟩)
-- lem6-4 = {!!}


----------------------------------------------------------------------------------------------------

-- TODO: lemma 7

-- TODO: corollary 8

-- TODO: theorem 1


----------------------------------------------------------------------------------------------------
