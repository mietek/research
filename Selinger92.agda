-- 2025-03-21
-- Friedman’s A-Translation
-- https://www.mscs.dal.ca/~selinger/papers/friedman.pdf

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

import Function as Fun
open Fun using (_∘_ ; _$_ ; flip)

import Level
open Level using (_⊔_ ; Level)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; subst ; cong ; cong₂ ; module ≡-Reasoning)

open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
  renaming (contradiction to _↯_)

open import Relation.Nullary.Decidable using (True)


----------------------------------------------------------------------------------------------------

-- missing things

instance
  numberNat : Number Nat
  numberNat = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ n → n
    }

instance
  numberFin : ∀ {n} → Number (Fin n)
  numberFin {n} = record
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


----------------------------------------------------------------------------------------------------

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

const : ∀ {n} → Nat → Prim n
const zero    = comp zero []
const (suc x) = comp suc (const x ∷ [])

ok-const : ∀ x → ⟦ const x ⟧ [] ≡ Fun.const {B = Nat§ 0} x []
ok-const zero    = refl
ok-const (suc x) = cong suc (ok-const x)

-- _+_ : Nat → Nat → Nat
-- zero  + y = y
-- suc x + y = suc (x + y)

add : Prim 2
add = rec (proj 0)
          (comp suc (proj 0 ∷ []))

ok-add : ∀ x y → ⟦ add ⟧ (x ∷ y ∷ []) ≡ x Nat.+ y
ok-add zero    y = refl
ok-add (suc x) y = cong suc (ok-add x y)

-- _*_ : Nat → Nat → Nat
-- zero  * y = zero
-- suc x * y = y + x * y

mul : Prim 2
mul = rec (const 0)
          (comp add (proj 2 ∷ proj 0 ∷ []))

module _ where
  open ≡-Reasoning

  ok-mul : ∀ x y → ⟦ mul ⟧ (x ∷ y ∷ []) ≡ x Nat.* y
  ok-mul zero    y = refl
  ok-mul (suc x) y = begin
                       ⟦ add ⟧ (y ∷ ⟦ mul ⟧ (x ∷ y ∷ []) ∷ [])
                     ≡⟨ cong (⟦ add ⟧ ∘ (y ∷_)) (cong (_∷ []) (ok-mul x y))  ⟩
                       ⟦ add ⟧ (y ∷ x Nat.* y ∷ [])
                     ≡⟨ ok-add y (x Nat.* y) ⟩
                       y Nat.+ x Nat.* y
                     ∎

-- pred : Nat → Nat
-- pred x = x ∸ 1

pred : Prim 1
pred = rec (const 0)
           (proj 1)

ok-pred : ∀ x → ⟦ pred ⟧ (x ∷ []) ≡ Nat.pred x
ok-pred zero    = refl
ok-pred (suc x) = refl

-- TODO: subtraction

-- _∸_ : Nat → Nat → Nat
-- x     ∸ zero  = x
-- zero  ∸ suc y = zero
-- suc x ∸ suc y = x ∸ y

-- _-_ : Nat → Nat → Nat
-- x - zero  = x
-- x - suc y = pred (x - y)


----------------------------------------------------------------------------------------------------

infix  19 _‵=_ _‵≠_
infixl 18 _‵∧_ _‵∨_
infixr 17 _‵→_ _‵↔_
infixr 16 _‵$_

-- terms, indexed by number of term variables
mutual
  data Tm (k : Nat) : Set where
    ‵var : ∀ (i : Fin k) → Tm k -- i-th term variable
    ‵fun : ∀ {n} (f : Prim n) (ts : Tm§ k n) → Tm k

  Tm§ : Nat → Nat → Set
  Tm§ k n = Vec (Tm k) n

instance
  numberTm : ∀ {k} → Number (Tm k)
  numberTm {k} = record
    { Constraint = λ m → True (m Nat.<? k)
    ; fromNat    = λ m {{p}} → ‵var ((Fin.# m) {k} {p})
    }

‵zero : ∀ {k} → Tm k
‵zero = ‵fun zero []

‵suc : ∀ {k} → Tm k → Tm k
‵suc t = ‵fun suc (t ∷ [])

-- formulas, indexed by number of term variables
data Fm (k : Nat) : Set where
  _‵→_ : ∀ (A B : Fm k) → Fm k
  _‵∧_  : ∀ (A B : Fm k) → Fm k
  _‵∨_  : ∀ (A B : Fm k) → Fm k
  ‵∀_   : ∀ (A : Fm (suc k)) → Fm k
  ‵∃_   : ∀ (A : Fm (suc k)) → Fm k
  ‵⊥   : Fm k
  _‵=_  : ∀ (t u : Tm k) → Fm k

Fm§ : Nat → Set
Fm§ k = List (Fm k)

_‵↔_ : ∀ {k} → Fm k → Fm k → Fm k
A ‵↔ B = (A ‵→ B) ‵∧ (B ‵→ A)

‵¬_ : ∀ {k} → Fm k → Fm k
‵¬ A = A ‵→ ‵⊥

_‵≠_ : ∀ {k} → Tm k → Tm k → Fm k
t ‵≠ u = ‵¬ (t ‵= u)


----------------------------------------------------------------------------------------------------

-- untyped de Bruijn indices and order-preserving embeddings for term variables

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

frenFin : ∀ {k k′} → k ≤ k′ → Fin k → Fin k′
frenFin stop      i       = i
frenFin (wk≤ η)   i       = suc (frenFin η i)
frenFin (lift≤ η) zero    = zero
frenFin (lift≤ η) (suc i) = frenFin (wk≤ η) i

fwkFin : ∀ {k} → Fin k → Fin (suc k)
fwkFin = frenFin (wk≤ id≤)


----------------------------------------------------------------------------------------------------

-- typed de Bruijn indices and order-preserving embeddings for derivation variables

infix 3 _∋_
data _∋_ {k} : Fm§ k → Fm k → Set where
  zero : ∀ {Γ A} → A ∷ Γ ∋ A
  suc  : ∀ {Γ A C} (i : Γ ∋ A) → C ∷ Γ ∋ A

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

-- literals for typed de Bruijn indices

infix 3 _∋⟨_⟩_
data _∋⟨_⟩_ {k} : Fm§ k → Nat → Fm k → Set where
  instance
    zero : ∀ {Γ A} → A ∷ Γ ∋⟨ zero ⟩ A
  suc : ∀ {Γ m A C} (i : Γ ∋⟨ m ⟩ A) → C ∷ Γ ∋⟨ suc m ⟩ A

instance
  suc∋ : ∀ {k} {Γ : Fm§ k} {m A C} {{i : Γ ∋⟨ m ⟩ A}} → C ∷ Γ ∋⟨ suc m ⟩ A
  suc∋ {{i}} = suc i

strip∋ : ∀ {m k} {Γ : Fm§ k} {A} → Γ ∋⟨ m ⟩ A → Γ ∋ A
strip∋ zero    = zero
strip∋ (suc i) = suc (strip∋ i)

instance
  number∋ : ∀ {k} {Γ : Fm§ k} {A} → Number (Γ ∋ A)
  number∋ {Γ = Γ} {A} = record
    { Constraint = λ m → Γ ∋⟨ m ⟩ A
    ; fromNat    = λ m {{p}} → strip∋ p
    }


----------------------------------------------------------------------------------------------------

-- renaming for terms and formulas

mutual
  frenTm : ∀ {k k′} → k ≤ k′ → Tm k → Tm k′
  frenTm η (‵var i)    = ‵var (frenFin η i)
  frenTm η (‵fun f ts) = ‵fun f (frenTm§ η ts)

  frenTm§ : ∀ {k k′ n} → k ≤ k′ → Tm§ k n → Tm§ k′ n
  frenTm§ η []       = []
  frenTm§ η (t ∷ ts) = frenTm η t ∷ frenTm§ η ts

frenFm : ∀ {k k′} → k ≤ k′ → Fm k → Fm k′
frenFm η (A ‵→ B) = frenFm η A ‵→ frenFm η B
frenFm η (A ‵∧ B)  = frenFm η A ‵∧ frenFm η B
frenFm η (A ‵∨ B)  = frenFm η A ‵∨ frenFm η B
frenFm η (‵∀ A)    = ‵∀ frenFm (lift≤ η) A
frenFm η (‵∃ A)    = ‵∃ frenFm (lift≤ η) A
frenFm η ‵⊥       = ‵⊥
frenFm η (t ‵= u)  = frenTm η t ‵= frenTm η u

frenFm§ : ∀ {k k′} → k ≤ k′ → Fm§ k → Fm§ k′
frenFm§ η []      = []
frenFm§ η (A ∷ Γ) = frenFm η A ∷ frenFm§ η Γ

-- weaken formula by adding one unused term variable
fwkFm : ∀ {k} → Fm k → Fm (suc k)
fwkFm = frenFm (wk≤ id≤)

-- weaken formulas by adding one unused term variable
fwkFm§ : ∀ {k} → Fm§ k → Fm§ (suc k)
fwkFm§ = frenFm§ (wk≤ id≤)


----------------------------------------------------------------------------------------------------

-- TODO: substitution for terms and formulas

postulate
  -- exchange two topmost term variables in formula
  ↕ : ∀ {k} (A : Fm (suc (suc k))) → Fm (suc (suc k))

  -- substitute topmost term variable in formula by term
  _[_] : ∀ {k} (A : Fm (suc k)) (s : Tm k) → Fm k

  -- TODO: this should follow from one of the substitution lemmas
  later : ∀ {k} {A : Fm (suc k)} → A ≡ (frenFm (lift≤ (wk≤ id≤)) A [ 0 ])


----------------------------------------------------------------------------------------------------

-- Heyting and Peano arithmetic
data Theory : Set where
  HA : Theory
  PA : Theory

-- derivations, indexed by list of derivation variables
infix 3 _/_⊢_
data _/_⊢_ {k} : Theory → Fm§ k → Fm k → Set where
  ‵var    : ∀ {Θ Γ A} (i : Γ ∋ A) → Θ / Γ ⊢ A -- i-th derivation variable
  ‵lam    : ∀ {Θ Γ A B} (d : Θ / A ∷ Γ ⊢ B) → Θ / Γ ⊢ A ‵→ B
  _‵$_    : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A ‵→ B) (e : Θ / Γ ⊢ A) → Θ / Γ ⊢ B
  ‵pair   : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A) (e : Θ / Γ ⊢ B) → Θ / Γ ⊢ A ‵∧ B
  ‵fst    : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A ‵∧ B) → Θ / Γ ⊢ A
  ‵snd    : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A ‵∧ B) → Θ / Γ ⊢ B
  ‵left   : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A) → Θ / Γ ⊢ A ‵∨ B
  ‵right  : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ B) → Θ / Γ ⊢ A ‵∨ B
  ‵case   : ∀ {Θ Γ A B C} (c : Θ / Γ ⊢ A ‵∨ B) (d : Θ / A ∷ Γ ⊢ C) (e : Θ / B ∷ Γ ⊢ C) →
               Θ / Γ ⊢ C

  --     A(x₀)
  -- --------------
  --   ∀y.A[y/xₒ]
  ‵∀intro : ∀ {Θ Γ A} (d : Θ / fwkFm§ Γ ⊢ A) → Θ / Γ ⊢ ‵∀ A

  --   ∀y.A[y/x₀]
  -- --------------
  --    A[t/x₀]
  ‵∀elim  : ∀ {Θ Γ A t A[t]} (d : Θ / Γ ⊢ ‵∀ A) (p : A[t] ≡ A [ t ]) → Θ / Γ ⊢ A[t]

  --    A[t/x₀]
  -- --------------
  --   ∃y.A[y/x₀]
  ‵∃intro : ∀ {Θ Γ A t A[t]} (d : Θ / Γ ⊢ A[t]) (p : A[t] ≡ A [ t ]) → Θ / Γ ⊢ ‵∃ A

 --                  A(x₀)
  --                   ⋮
  --   ∃y.A[y/x₀]      C
  -- -----------------------
  --           C
  ‵∃elim  : ∀ {Θ Γ A C} (d : Θ / Γ ⊢ ‵∃ A) (e : Θ / A ∷ fwkFm§ Γ ⊢ fwkFm C) → Θ / Γ ⊢ C

  -- explosion (ex falso quodlibet) as primitive in Heyting arithmetic
  ‵abort  : ∀ {Γ C} (d : HA / Γ ⊢ ‵⊥) → HA / Γ ⊢ C

  -- double negation elimination (reductio ad absurdum) as primitive in Peano arithmetic
  ‵magic  : ∀ {Γ A} (d : PA / ‵¬ A ∷ Γ ⊢ ‵⊥) → PA / Γ ⊢ A

  ‵refl   : ∀ {Θ Γ t} → Θ / Γ ⊢ t ‵= t
  ‵sym    : ∀ {Θ Γ t u} (d : Θ / Γ ⊢ t ‵= u) → Θ / Γ ⊢ u ‵= t
  ‵trans  : ∀ {Θ Γ s t u} (d : Θ / Γ ⊢ s ‵= t) (e : Θ / Γ ⊢ t ‵= u) → Θ / Γ ⊢ s ‵= u

  ‵cong   : ∀ {Θ Γ n ts u} (f : Prim n) (i : Fin n) (d : Θ / Γ ⊢ get i ts ‵= u) →
               Θ / Γ ⊢ ‵fun f ts ‵= ‵fun f (put i ts u)

  ‵dis    : ∀ {Θ Γ t} → Θ / Γ ⊢ ‵suc t ‵≠ ‵zero

  ‵inj    : ∀ {Θ Γ t u} (d : Θ / Γ ⊢ ‵suc t ‵= ‵suc u) → Θ / Γ ⊢ t ‵= u

   --   A[0/x₀]    ∀y.A[y/x₀]→A[y+1/x₀]
   -- ------------------------------------
   --              ∀y.A[y/x₀]
  ‵ind    : ∀ {Θ Γ A} (d : Θ / Γ ⊢ A [ ‵zero ])
               (e : Θ / Γ ⊢ ‵∀ (A ‵→ (↕ (fwkFm A)) [ ‵suc 0 ])) →
               Θ / Γ ⊢ ‵∀ A

  ‵proj   : ∀ {Θ Γ n ts} (i : Fin n) → Θ / Γ ⊢ ‵fun (proj i) ts ‵= get i ts

  ‵comp   : ∀ {Θ Γ n m ts} (g : Prim m) (fs : Prim§ n m) →
               Θ / Γ ⊢ ‵fun (comp g fs) ts ‵= ‵fun g (for fs λ f → ‵fun f ts)

  ‵rec    : ∀ {Θ Γ n s ts} (f : Prim n) (g : Prim (suc (suc n))) →
               Θ / Γ ⊢ ‵fun (rec f g) (‵zero ∷ ts) ‵= ‵fun f ts ‵∧
                 ‵fun (rec f g) (‵suc s ∷ ts) ‵= ‵fun g (‵fun (rec f g) (s ∷ ts) ∷ s ∷ ts)

instance
  number⊢ : ∀ {Θ k} {Γ : Fm§ k} {A} → Number (Θ / Γ ⊢ A)
  number⊢ {Γ = Γ} {A} = record
    { Constraint = λ m → Γ ∋⟨ m ⟩ A
    ; fromNat    = λ m {{p}} → ‵var (strip∋ p)
    }

‵congsuc : ∀ {Θ k} {Γ : Fm§ k} {t u} → Θ / Γ ⊢ t ‵= u → Θ / Γ ⊢ ‵suc t ‵= ‵suc u
‵congsuc d = ‵cong suc 0 d


----------------------------------------------------------------------------------------------------

-- renaming for derivations

fren⊆ : ∀ {k k′ Γ Γ′} (η : k ≤ k′) → Γ ⊆ Γ′ → frenFm§ η Γ ⊆ frenFm§ η Γ′
fren⊆ η stop      = stop
fren⊆ η (wk⊆ ζ)   = wk⊆ (fren⊆ η ζ)
fren⊆ η (lift⊆ ζ) = lift⊆ (fren⊆ η ζ)

fwk⊆ : ∀ {k} {Γ Γ′ : Fm§ k} → Γ ⊆ Γ′ → fwkFm§ Γ ⊆ fwkFm§ Γ′
fwk⊆ = fren⊆ (wk≤ id≤)

ren : ∀ {Θ k} {Γ Γ′ : Fm§ k} {A} → Γ ⊆ Γ′ → Θ / Γ ⊢ A → Θ / Γ′ ⊢ A
ren η (‵var i)         = ‵var (ren∋ η i)
ren η (‵lam d)         = ‵lam (ren (lift⊆ η) d)
ren η (d ‵$ e)         = ren η d ‵$ ren η e
ren η (‵pair d e)      = ‵pair (ren η d) (ren η e)
ren η (‵fst d)         = ‵fst (ren η d)
ren η (‵snd d)         = ‵snd (ren η d)
ren η (‵left d)        = ‵left (ren η d)
ren η (‵right d)       = ‵right (ren η d)
ren η (‵case c d e)    = ‵case (ren η c) (ren (lift⊆ η) d) (ren (lift⊆ η) e)
ren η (‵∀intro d)      = ‵∀intro (ren (fwk⊆ η) d)
ren η (‵∀elim d refl)  = ‵∀elim (ren η d) refl
ren η (‵∃intro d refl) = ‵∃intro (ren η d) refl
ren η (‵∃elim d e)     = ‵∃elim (ren η d) (ren (lift⊆ (fwk⊆ η)) e)
ren η (‵abort d)       = ‵abort (ren η d)
ren η (‵magic d)       = ‵magic (ren (lift⊆ η) d)
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

fren : ∀ {Θ k k′ Γ Γ′ A} (η : k ≤ k′) → Γ ⊆ Γ′ → Θ / frenFm§ η Γ ⊢ A → Θ / frenFm§ η Γ′ ⊢ A
fren η ζ = ren (fren⊆ η ζ)

fwk : ∀ {Θ k} {Γ Γ′ : Fm§ k} {A} → Γ ⊆ Γ′ → Θ / fwkFm§ Γ ⊢ A → Θ / fwkFm§ Γ′ ⊢ A
fwk = fren (wk≤ id≤)


----------------------------------------------------------------------------------------------------

abort : ∀ {Θ k} {Γ : Fm§ k} {C} → Θ / Γ ⊢ ‵⊥ → Θ / Γ ⊢ C
abort {HA} d = ‵abort d
abort {PA} d = ‵magic (wk d)

lem2 : ∀ {k} {Γ : Fm§ k} {A} → HA / Γ ⊢ A → PA / Γ ⊢ A
lem2 (‵var i)         = ‵var i
lem2 (‵lam d)         = ‵lam (lem2 d)
lem2 (d ‵$ e)         = lem2 d ‵$ lem2 e
lem2 (‵pair d e)      = ‵pair (lem2 d) (lem2 e)
lem2 (‵fst d)         = ‵fst (lem2 d)
lem2 (‵snd d)         = ‵snd (lem2 d)
lem2 (‵left d)        = ‵left (lem2 d)
lem2 (‵right d)       = ‵right (lem2 d)
lem2 (‵case c d e)    = ‵case (lem2 c) (lem2 d) (lem2 e)
lem2 (‵∀intro d)      = ‵∀intro (lem2 d)
lem2 (‵∀elim d refl)  = ‵∀elim (lem2 d) refl
lem2 (‵∃intro d refl) = ‵∃intro (lem2 d) refl
lem2 (‵∃elim d e)     = ‵∃elim (lem2 d) (lem2 e)
lem2 (‵abort d)       = abort (lem2 d)
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
  ↔refl : ∀ {A} → Θ / Γ ⊢ A ‵↔ A
  ↔refl {A} = ‵pair (‵lam 0) (‵lam 0)

  ↔sym : ∀ {A B} → Θ / Γ ⊢ A ‵↔ B → Θ / Γ ⊢ B ‵↔ A
  ↔sym d = ‵pair (‵snd d) (‵fst d)

  ↔trans : ∀ {A B C} → Θ / Γ ⊢ A ‵↔ B → Θ / Γ ⊢ B ‵↔ C → Θ / Γ ⊢ A ‵↔ C
  ↔trans d e = ‵pair
                  (‵lam (‵fst (wk e) ‵$ ‵fst (wk d) ‵$ 0))
                  (‵lam (‵snd (wk d) ‵$ ‵snd (wk e) ‵$ 0))

  ↔cong→ : ∀ {A A′ B B′} → Θ / Γ ⊢ A ‵↔ A′ → Θ / Γ ⊢ B ‵↔ B′ →
               Θ / Γ ⊢ (A ‵→ B) ‵↔ (A′ ‵→ B′)
  ↔cong→ d e = ‵pair
                   (‵lam (‵lam
                     (‵fst (wk (wk e)) ‵$ 1 ‵$ ‵snd (wk (wk d)) ‵$ 0)))
                   (‵lam (‵lam
                     (‵snd (wk (wk e)) ‵$ 1 ‵$ ‵fst (wk (wk d)) ‵$ 0)))

  ↔cong∧ : ∀ {A A′ B B′} → Θ / Γ ⊢ A ‵↔ A′ → Θ / Γ ⊢ B ‵↔ B′ →
              Θ / Γ ⊢ A ‵∧ B ‵↔ A′ ‵∧ B′
  ↔cong∧ d e = ‵pair
                  (‵lam (‵pair
                    (‵fst (wk d) ‵$ ‵fst 0)
                    (‵fst (wk e) ‵$ ‵snd 0)))
                  (‵lam (‵pair
                    (‵snd (wk d) ‵$ ‵fst 0)
                    (‵snd (wk e) ‵$ ‵snd 0)))

  ↔cong∨ : ∀ {A A′ B B′} → Θ / Γ ⊢ A ‵↔ A′ → Θ / Γ ⊢ B ‵↔ B′ →
              Θ / Γ ⊢ A ‵∨ B ‵↔ A′ ‵∨ B′
  ↔cong∨ d e = ‵pair
                  (‵lam (‵case 0
                    (‵left (‵fst (wk (wk d)) ‵$ 0))
                    (‵right (‵fst (wk (wk e)) ‵$ 0))))
                  (‵lam (‵case 0
                    (‵left (‵snd (wk (wk d)) ‵$ 0))
                    (‵right (‵snd (wk (wk e)) ‵$ 0))))

  ↔cong∀ : ∀ {A A′} → Θ / fwkFm§ Γ ⊢ A ‵↔ A′ → Θ / Γ ⊢ (‵∀ A) ‵↔ (‵∀ A′)
  ↔cong∀ d = ‵pair
                (‵lam (‵∀intro (fwk (wk⊆ id⊆) (‵fst d) ‵$ ‵∀elim 0 later)))
                (‵lam (‵∀intro (fwk (wk⊆ id⊆) (‵snd d) ‵$ ‵∀elim 0 later)))

  ↔cong∃ : ∀ {A A′} → Θ / fwkFm§ Γ ⊢ A ‵↔ A′ → Θ / Γ ⊢ (‵∃ A) ‵↔ (‵∃ A′)
  ↔cong∃ d = ‵pair
                (‵lam (‵∃elim 0 (‵∃intro (‵fst (wk (wk d)) ‵$ 0) later)))
                (‵lam (‵∃elim 0 (‵∃intro (‵snd (wk (wk d)) ‵$ 0) later)))

  ≡→↔ : ∀ {A B} → A ≡ B → Θ / Γ ⊢ A ‵↔ B
  ≡→↔ refl = ↔refl

module ↔-Reasoning {Θ k} {Γ : Fm§ k} where
  infix  1 begin_
  infixr 2 _↔⟨⟩_ _↔⟨_⟩_ _↔˘⟨_⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {A B} → Θ / Γ ⊢ A ‵↔ B → Θ / Γ ⊢ A ‵↔ B
  begin d = d

  _↔⟨⟩_ : ∀ A {B} → Θ / Γ ⊢ A ‵↔ B → Θ / Γ ⊢ A ‵↔ B
  A ↔⟨⟩ d = d

  _↔⟨_⟩_ : ∀ A {B C} → Θ / Γ ⊢ A ‵↔ B → Θ / Γ ⊢ B ‵↔ C → Θ / Γ ⊢ A ‵↔ C
  A ↔⟨ d ⟩ e = ↔trans d e

  _↔˘⟨_⟩_ : ∀ A {B C} → Θ / Γ ⊢ B ‵↔ A → Θ / Γ ⊢ B ‵↔ C → Θ / Γ ⊢ A ‵↔ C
  A ↔˘⟨ d ⟩ e = ↔trans (↔sym d) e

  _≡⟨_⟩_ : ∀ A {B C} → A ≡ B → Θ / Γ ⊢ B ‵↔ C → Θ / Γ ⊢ A ‵↔ C
  A ≡⟨ d ⟩ e = ↔trans (≡→↔ d) e

  _≡˘⟨_⟩_ : ∀ A {B C} → B ≡ A → Θ / Γ ⊢ B ‵↔ C → Θ / Γ ⊢ A ‵↔ C
  A ≡˘⟨ d ⟩ e = ↔trans (≡→↔ (sym d)) e

  _∎ : ∀ A → Θ / Γ ⊢ A ‵↔ A
  A ∎ = ↔refl


----------------------------------------------------------------------------------------------------

-- extended middle

-- constructive
module _ {Θ k} {Γ : Fm§ k} where
  ¬¬em : ∀ {A} → Θ / Γ ⊢ ‵¬ ‵¬ (A ‵∨ ‵¬ A)
  ¬¬em = ‵lam (0 ‵$ ‵right (‵lam (1 ‵$ ‵left 0)))

  dni : ∀ {A} → Θ / Γ ⊢ A ‵→ ‵¬ ‵¬ A
  dni = ‵lam (‵lam (0 ‵$ 1))

-- non-constructive
module _ {k} {Γ : Fm§ k} where
  dne : ∀ {A} → PA / Γ ⊢ ‵¬ ‵¬ A ‵→ A
  dne = ‵lam (‵magic (1 ‵$ 0))

  dn : ∀ {A} → PA / Γ ⊢ ‵¬ ‵¬ A ‵↔ A
  dn = ‵pair dne dni

  em : ∀ {A} → PA / Γ ⊢ A ‵∨ ‵¬ A
  em = dne ‵$ ¬¬em


----------------------------------------------------------------------------------------------------

-- TODO: other non-constructive tautologies

{-A     B    ¬A    ¬B    A∧B   A∨B   A→B  A↔B ¬A∧B  ¬A∨B  ¬A→B ¬A↔B  A∧¬B  A∨¬B A→¬B A↔¬B
----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- -----
  0     0     1     1     0     0     1     1     0     1     0     0     0     1     1     0
  0     1     1     0     0     1     1     0     1     1     1     1     0     0     1     1
  1     0     0     1     0     1     0     0     0     0     1     1     1     1     1     1
  1     1     0     0     1     1     1     1     0     1     1     0     0     1     0     0-}

-- module _ where
--   ↔tau1 : ∀ {A B} → PA / Γ ⊢ A ‵→ B ‵↔ ‵¬ A ‵∨ B
--   ↔tau1 = {!!}
--
--   ↔tau2 : ∀ {A B} → PA / Γ ⊢ (‵¬ A ‵↔ B) ‵↔ (A ‵↔ ‵¬ B)
--   ↔tau2 = {!!}


----------------------------------------------------------------------------------------------------

-- de Morgan’s laws

-- constructive
module _ {Θ k} {Γ : Fm§ k} where
  pdm1 : ∀ {A B} → Θ / Γ ⊢ ‵¬ A ‵∨ ‵¬ B ‵→ ‵¬ (A ‵∧ B)
  pdm1 = ‵lam (‵lam (‵case 1
           (0 ‵$ ‵fst 1)
           (0 ‵$ ‵snd 1)))

  qdm1 : ∀ {A} → Θ / Γ ⊢ ‵∃ (‵¬ A) ‵→ ‵¬ (‵∀ A)
  qdm1 = ‵lam (‵lam (‵∃elim 1
           (0 ‵$ ‵∀elim 1 later)))

  npdm1 : ∀ {A B} → Θ / Γ ⊢ A ‵∨ B ‵→ ‵¬ (‵¬ A ‵∧ ‵¬ B)
  npdm1 = ‵lam (‵lam (abort (‵case 1
            (‵fst 1 ‵$ 0)
            (‵snd 1 ‵$ 0))))

  nqdm1 : ∀ {A} → Θ / Γ ⊢ ‵∃ A ‵→ ‵¬ (‵∀ (‵¬ A))
  nqdm1 = ‵lam (‵lam (abort (‵∃elim 1
            (‵∀elim 1 later ‵$ 0))))

  pdm2 : ∀ {A B} → Θ / Γ ⊢ ‵¬ A ‵∧ ‵¬ B ‵→ ‵¬ (A ‵∨ B)
  pdm2 = ‵lam (‵lam (‵case 0
           (‵fst 2 ‵$ 0)
           (‵snd 2 ‵$ 0)))

  qdm2 : ∀ {A} → Θ / Γ ⊢ ‵∀ (‵¬ A) ‵→ ‵¬ (‵∃ A)
  qdm2 = ‵lam (‵lam (‵∃elim 0
           (‵∀elim 2 later ‵$ 0)))

  npdm2 : ∀ {A B} → Θ / Γ ⊢ A ‵∧ B ‵→ ‵¬ (‵¬ A ‵∨ ‵¬ B)
  npdm2 = ‵lam (‵lam (abort (‵case 0
            (0 ‵$ ‵fst 2)
            (0 ‵$ ‵snd 2))))

  nqdm2 : ∀ {A} → Θ / Γ ⊢ ‵∀ A ‵→ ‵¬ (‵∃ (‵¬ A))
  nqdm2 = ‵lam (‵lam (abort (‵∃elim 0
            (0 ‵$ ‵∀elim 2 later))))

  pdm3 : ∀ {A B} → Θ / Γ ⊢ ‵¬ (A ‵∨ B) ‵→ ‵¬ A ‵∧ ‵¬ B
  pdm3 = ‵lam (‵pair
           (‵lam (1 ‵$ ‵left 0))
           (‵lam (1 ‵$ ‵right 0)))

  qdm3 : ∀ {A} → Θ / Γ ⊢ ‵¬ (‵∃ A) ‵→ ‵∀ (‵¬ A)
  qdm3 = ‵lam (‵∀intro (‵lam
           (1 ‵$ ‵∃intro 0 later)))

-- TODO: non-constructive
-- module _ {k} {Γ : Fm§ k} where
--   npdm3 : ∀ {A B} → PA / Γ ⊢ ‵¬ (‵¬ A ‵∨ ‵¬ B) ‵→ A ‵∧ B
--   npdm3 = {!!}
--
--   nqdm3 : ∀ {A} → PA / Γ ⊢ ‵¬ (‵∃ (‵¬ A)) ‵→ ‵∀ A
--   nqdm3 = {!!}
--
--   pdm4 : ∀ {A B} → PA / Γ ⊢ ‵¬ (A ‵∧ B) ‵→ ‵¬ A ‵∨ ‵¬ B
--   pdm4 = {!!}
--
--   qdm4 : ∀ {A} → PA / Γ ⊢ ‵¬ (‵∀ A) ‵→ ‵∃ (‵¬ A)
--   qdm4 = {!!}
--
--   npdm4 : ∀ {A B} → PA / Γ ⊢ ‵¬ (‵¬ A ‵∧ ‵¬ B) ‵→ A ‵∨ B
--   npdm4 = {!!}
--
--   nqdm4 : ∀ {A} → PA / Γ ⊢ ‵¬ (‵∀ (‵¬ A)) ‵→ ‵∃ A
--   nqdm4 = {!!}


----------------------------------------------------------------------------------------------------

-- quantifier-free formulas

data IsQFree {k} : Fm k → Set where
  _‵→_ : ∀ {A B} (p : IsQFree A) (q : IsQFree B) → IsQFree (A ‵→ B)
  _‵∧_  : ∀ {A B} (p : IsQFree A) (q : IsQFree B) → IsQFree (A ‵∧ B)
  _‵∨_  : ∀ {A B} (p : IsQFree A) (q : IsQFree B) → IsQFree (A ‵∨ B)
  ‵⊥   : IsQFree ‵⊥
  _‵=_  : ∀ {t u} → IsQFree (t ‵= u)

module _ where
  open =-Reasoning

  goal goal′ : ∀ {Θ k} {Γ : Fm§ k} → Θ / Γ ⊢
                 ‵fun (const 1) (tab ‵var) ‵= ‵zero ‵→ ‵suc ‵zero ‵= ‵zero

  goal = ‵lam
           (‵trans
             (‵trans
               (‵cong suc zero
                 (‵sym (‵comp zero [])))
               (‵sym (‵comp suc (comp zero [] ∷ []))))
             (‵var 0))

  goal′ = ‵lam
            (begin
              ‵suc ‵zero
            =⟨⟩
              ‵fun suc (‵fun zero [] ∷ [])
            =⟨ ‵cong suc zero (
                begin
                  ‵fun zero []
                =˘⟨ ‵comp zero [] ⟩
                  ‵fun (comp zero []) (tab ‵var)
                ∎)
              ⟩
              ‵fun suc (‵fun (comp zero []) (tab ‵var) ∷ [])
            =˘⟨ ‵comp suc (comp zero [] ∷ []) ⟩
              ‵fun (comp suc (comp zero [] ∷ [])) (tab ‵var)
            =⟨⟩
              ‵fun (const 1) (tab ‵var)
            =⟨ ‵var 0 ⟩
              ‵zero
            ∎)


-- TODO: lemma 3

-- lem3 : ∀ {Θ k} {Γ : Fm§ k} (A : Fm k) {{_ : IsQFree A}} → Σ (Prim k) λ f →
--          Θ / Γ ⊢ A ‵↔ ‵fun f (tab ‵var) ‵= ‵zero
-- lem3 (A ‵→ B) = {!!}
-- lem3 (A ‵∧ B)  = {!!}
-- lem3 (A ‵∨ B)  = {!!}
-- lem3 ‵⊥       = const 1 , ‵pair (‵lam (abort 0)) (‵lam (‵dis ‵$ goal ‵$ 0))
-- lem3 (t ‵= u)  = {!!}


----------------------------------------------------------------------------------------------------

-- TODO: definition of Π⁰₂


-- TODO: lemma 4


----------------------------------------------------------------------------------------------------

-- double negation translation

_° : ∀ {k} → Fm k → Fm k
(A ‵→ B) ° = A ° ‵→ B °
(A ‵∧ B) °  = A ° ‵∧ B °
(A ‵∨ B) °  = ‵¬ ‵¬ (A ° ‵∨ B °)
(‵∀ A) °    = ‵∀ (A °)
(‵∃ A) °    = ‵¬ ‵¬ ‵∃ (A °)
‵⊥ °       = ‵⊥
(t ‵= u) °  = ‵¬ ‵¬ (t ‵= u)

_°§ : ∀ {k} → Fm§ k → Fm§ k
[] °§      = []
(A ∷ Γ) °§ = A ° ∷ Γ °§


-- TODO
postulate
  probably : ∀ {k} {A : Fm (suc k)} {t} → (A [ t ]) ° ≡ (A °) [ t ]


-- TODO: lemma 5

module _ where
  open ↔-Reasoning

  lem5-1 : ∀ {k} {Γ : Fm§ k} A → PA / Γ ⊢ A ° ‵↔ A
  lem5-1 (A ‵→ B) = ↔cong→ (lem5-1 A) (lem5-1 B)
  lem5-1 (A ‵∧ B)  = ↔cong∧ (lem5-1 A) (lem5-1 B)
  lem5-1 (A ‵∨ B)  = begin
                       ‵¬ ‵¬ (A ° ‵∨ B °)
                     ↔⟨ dn ⟩
                       A ° ‵∨ B °
                     ↔⟨ ↔cong∨ (lem5-1 A) (lem5-1 B) ⟩
                       A ‵∨ B
                     ∎
  lem5-1 (‵∀ A)    = ↔cong∀ (lem5-1 A)
  lem5-1 (‵∃ A)    = begin
                       ‵¬ ‵¬ ‵∃ (A °)
                     ↔⟨ dn ⟩
                       ‵∃ (A °)
                     ↔⟨ ↔cong∃ (lem5-1 A) ⟩
                       ‵∃ A
                     ∎
  lem5-1 ‵⊥       = ↔refl
  lem5-1 (t ‵= u)  = dn

  join : ∀ {Θ k} {Γ : Fm§ k} {A} → Θ / ‵¬ ‵¬ ‵¬ ‵¬ A ∷ Γ ⊢ ‵¬ ‵¬ A
  join = ‵lam (1 ‵$ ‵lam (0 ‵$ 1))

  lem5-2 : ∀ {k} {Γ : Fm§ k} A → HA / ‵¬ ‵¬ (A °) ∷ Γ ⊢ A °
  lem5-2 (A ‵→ B) = ‵lam (‵lam (lem5-2 B) ‵$ ‵lam
                       (2 ‵$ ‵lam
                         (1 ‵$ 0 ‵$ 2)))
  lem5-2 (A ‵∧ B)  = ‵pair
                       (‵lam (lem5-2 A) ‵$ ‵lam
                         (1 ‵$ ‵lam
                           (1 ‵$ ‵fst 0)))
                       (‵lam (lem5-2 B) ‵$ ‵lam
                         (1 ‵$ ‵lam
                           (1 ‵$ ‵snd 0)))
  lem5-2 (A ‵∨ B)  = join
  lem5-2 (‵∀ A)    = ‵∀intro (‵lam (lem5-2 A) ‵$ ‵lam
                       (1 ‵$ ‵lam
                         (1 ‵$ ‵∀elim 0 later)))
  lem5-2 (‵∃ A)    = join
  lem5-2 ‵⊥       = 0 ‵$ ‵lam 0
  lem5-2 (t ‵= u)  = join

  lem5-3∋ : ∀ {k} {Γ : Fm§ k} {A} → Γ ∋ A → Γ °§ ∋ A °
  lem5-3∋ zero    = zero
  lem5-3∋ (suc i) = suc (lem5-3∋ i)

--   lem5-3 : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ A → HA / Γ °§ ⊢ A °
--   lem5-3 (‵var i)         = ‵var (lem5-3∋ i)
--   lem5-3 (‵lam d)         = ‵lam (lem5-3 d)
--   lem5-3 (d ‵$ e)         = lem5-3 d ‵$ lem5-3 e
--   lem5-3 (‵pair d e)      = ‵pair (lem5-3 d) (lem5-3 e)
--   lem5-3 (‵fst d)         = ‵fst (lem5-3 d)
--   lem5-3 (‵snd d)         = ‵snd (lem5-3 d)
--   lem5-3 (‵left d)        = {!!}
--   lem5-3 (‵right d)       = {!!}
--   lem5-3 (‵case c d e)    = {!!}
--   lem5-3 (‵∀intro d)      = {!!}
--   lem5-3 (‵∀elim d refl)  = ‵∀elim (lem5-3 d) probably
--   lem5-3 (‵∃intro d refl) = {!!}
--   lem5-3 (‵∃elim d e)     = {!!}
--   lem5-3 (‵magic d)       = {!!}
--   lem5-3 ‵refl            = {!!}
--   lem5-3 (‵sym d)         = {!!}
--   lem5-3 (‵trans d e)     = {!!}
--   lem5-3 (‵cong f i d)    = {!!}
--   lem5-3 ‵dis             = {!!}
--   lem5-3 (‵inj d)         = {!!}
--   lem5-3 (‵ind d e)       = {!!}
--   lem5-3 (‵proj i)        = {!!}
--   lem5-3 (‵comp g fs)     = {!!}
--   lem5-3 (‵rec f g)       = {!!}

--   lem5-3a : ∀ {k} {Γ : Fm§ k} {A} → HA / Γ °§ ⊢ A ° → PA / Γ ⊢ A
--   lem5-3a {A = A} d = {!‵snd (lem5-1 A)!}

-- --  lem5-4 : ∀ {k} {Γ : Fm§ k} {A}


-- ----------------------------------------------------------------------------------------------------

-- -- TODO: A-translation

-- -- TODO: lemma 6


-- ----------------------------------------------------------------------------------------------------

-- -- TODO: lemma 7

-- -- TODO: corollary 8

-- -- TODO: theorem 1


-- ----------------------------------------------------------------------------------------------------
