-- 2025-03-21
-- Friedman’s A-Translation
-- https://www.mscs.dal.ca/~selinger/papers/friedman.pdf

module Selinger92 where

open import Data.Fin using (Fin ; zero ; suc)

open import Data.List using (List ; [] ; _∷_)

import Data.Nat as Nat
open Nat using (zero ; suc)
  renaming (ℕ to Nat)

open import Data.Product using (Σ ; _,_ ; _×_)
  renaming (proj₁ to fst ; proj₂ to snd)

import Data.Vec as Vec
open Vec using (Vec ; [] ; _∷_ ; tabulate)

import Function as Fun
open Fun using (_∘_ ; _$_ ; flip)

open import Level using (_⊔_)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; subst ; cong ; cong₂ ; module ≡-Reasoning)

open import Relation.Nullary using (Dec ; yes ; no)


----------------------------------------------------------------------------------------------------

-- vector things

get : ∀ {a} {A : Set a} {n} → Fin n → Vec A n → A
get i xs = Vec.lookup xs i

put : ∀ {a} {A : Set a} {n} → Fin n → Vec A n → A → Vec A n
put i xs y = xs Vec.[ i ]≔ y

for : ∀ {a b} {A : Set a} {B : Set b} {n} → Vec A n → (A → B) → Vec B n
for xs f = Vec.map f xs


----------------------------------------------------------------------------------------------------

-- building blocks for the standard model of primitive recursive n-place functions on naturals
-- Troelstra (1973) §1.3.4

Nat§ : Nat → Set
Nat§ n = Vec Nat n

-- n-place functions on naturals
#Fun : Nat → Set
#Fun n = Nat§ n → Nat

#Fun§ : Nat → Nat → Set
#Fun§ n m = Vec (#Fun n) m

#zero : #Fun 0
#zero [] = zero

#suc : #Fun 1
#suc (x ∷ []) = suc x

#proj : ∀ {n} → Fin n → #Fun n
#proj i xs = get i xs

#comp : ∀ {n m} (ψ : #Fun m) (φs : #Fun§ n m) → #Fun n
#comp ψ φs xs = ψ (for φs (_$ xs))

#rec : ∀ {n} (φ : #Fun n) (ψ : #Fun (suc (suc n))) → #Fun (suc n)
#rec φ ψ (zero  ∷ ys) = φ ys
#rec φ ψ (suc x ∷ ys) = ψ (#rec φ ψ (x ∷ ys) ∷ x ∷ ys)


----------------------------------------------------------------------------------------------------

-- primitive recursive n-place functions on naturals
mutual
  data Prim : Nat → Set where
    zero : Prim zero
    suc  : Prim (suc zero)
    proj : ∀ {n} (i : Fin n) → Prim n
    comp : ∀ {n m} (g : Prim m) (fs : Prim§ n m) → Prim n
    rec  : ∀ {n} (f : Prim n) (g : Prim (suc (suc n))) → Prim (suc n)

  Prim§ : Nat → Nat → Set
  Prim§ n m = Vec (Prim n) m

mutual
  ⟦_⟧ : ∀ {n} → Prim n → #Fun n
  ⟦ zero ⟧      = #zero
  ⟦ suc ⟧       = #suc
  ⟦ proj i ⟧    = #proj i
  ⟦ comp g fs ⟧ = #comp ⟦ g ⟧ ⟦ fs ⟧§
  ⟦ rec f g ⟧   = #rec ⟦ f ⟧ ⟦ g ⟧

  ⟦_⟧§ : ∀ {n m} → Prim§ n m → #Fun§ n m
  ⟦ [] ⟧§     = []
  ⟦ f ∷ fs ⟧§ = ⟦ f ⟧ ∷ ⟦ fs ⟧§


----------------------------------------------------------------------------------------------------

-- TODO: probably pointless; delete this

_≐_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → (A → B) → Set (a ⊔ b)
f ≐ f′ = ∀ {x} → f x ≡ f′ x

mutual
  data IsPrim : ∀ {n} → #Fun n → Set where
    iszero : ∀ {ξ : #Fun zero} (h : ξ ≐ #zero) → IsPrim ξ
    issuc  : ∀ {ξ : #Fun (suc zero)} (h : ξ ≐ #suc) → IsPrim ξ
    isproj : ∀ {n} i {ξ : #Fun n} (h : ξ ≐ #proj i) → IsPrim ξ
    iscomp : ∀ {n m} {ξ : #Fun n} {ψ : #Fun m} {φs : #Fun§ n m} →
               (h : ξ ≐ #comp ψ φs) (e : IsPrim ψ) (ds : IsPrim§ φs) → IsPrim ξ
    isrec  : ∀ {n} {ξ : #Fun (suc n)} {φ : #Fun n} {ψ : #Fun (suc (suc n))} →
               (h : ξ ≐ #rec φ ψ) (d : IsPrim φ) (e : IsPrim ψ) → IsPrim ξ

  data IsPrim§ {n} : ∀ {m} → #Fun§ n m → Set where
    []  : IsPrim§ []
    _∷_ : ∀ {m} {φ : #Fun n} {φs : #Fun§ n m} (d : IsPrim φ) (ds : IsPrim§ φs) →
            IsPrim§ (φ ∷ φs)

mutual
  i→e : ∀ {n} (f : Prim n) → IsPrim ⟦ f ⟧
  i→e zero        = iszero refl
  i→e suc         = issuc refl
  i→e (proj i)    = isproj i refl
  i→e (comp g fs) = iscomp refl (i→e g) (i→e§ fs)
  i→e (rec f g)   = isrec refl (i→e f) (i→e g)

  i→e§ : ∀ {n m} (φs : Prim§ n m) → IsPrim§ ⟦ φs ⟧§
  i→e§ []       = []
  i→e§ (f ∷ fs) = i→e f ∷ i→e§ fs

module _ where
  open ≡-Reasoning

  mutual
    e→i : ∀ {n} {φ : #Fun n} → IsPrim φ → Σ (Prim n) λ f → φ ≐ ⟦ f ⟧
    e→i (iszero h)      = zero , h
    e→i (issuc h)       = suc , h
    e→i (isproj i h)    = proj i , h
    e→i (iscomp {ξ = ξ} {ψ} {φs} h e ds) with e→i e | e→i§ ds
    ... | g , h₁ | fs , hs₂ = comp g fs , do-comp
      where
        do-comp : ξ ≐ #comp ⟦ g ⟧ ⟦ fs ⟧§
        do-comp {xs} =
          begin
            ξ xs
          ≡⟨ h {xs} ⟩
            #comp ψ φs xs
          ≡⟨⟩
            ψ (for φs (_$ xs))
          ≡⟨ h₁ {for φs (_$ xs)} ⟩
            ⟦ g ⟧ (for φs (_$ xs))
          ≡⟨ cong ⟦ g ⟧ (hs₂ {xs}) ⟩
            ⟦ g ⟧ (for ⟦ fs ⟧§ (_$ xs))
          ≡⟨⟩
            #comp ⟦ g ⟧ ⟦ fs ⟧§ xs
          ∎
    e→i (isrec {n} {ξ} {φ} {ψ} h d e) with e→i d | e→i e
    ... | f , h₁ | g , h₂ = rec f g , do-rec f g h₁ h₂
      where
        do-rec : ∀ (f : Prim n) (g : Prim (suc (suc n))) (h₁ : φ ≐ ⟦ f ⟧) (h₂ : ψ ≐ ⟦ g ⟧) →
                   ξ ≐ #rec ⟦ f ⟧ ⟦ g ⟧
        do-rec f g h₁ h₂ {zero ∷ ys} =
          begin
            ξ (zero ∷ ys)
          ≡⟨ h {zero ∷ ys} ⟩
            #rec φ ψ (zero ∷ ys)
          ≡⟨⟩
            φ ys
          ≡⟨ h₁ {ys} ⟩
            ⟦ f ⟧ ys
          ≡⟨⟩
            #rec ⟦ f ⟧ ⟦ g ⟧ (zero ∷ ys)
          ∎
        do-rec f g h₁ h₂ {suc x ∷ ys} =
          begin
            ξ (suc x ∷ ys)
          ≡⟨ h {suc x ∷ ys} ⟩
            #rec φ ψ (suc x ∷ ys)
          ≡⟨⟩
            ψ (#rec φ ψ (x ∷ ys) ∷ x ∷ ys)
          ≡˘⟨ cong (ψ ∘ (_∷ x ∷ ys)) (h {x ∷ ys}) ⟩
            ψ (ξ (x ∷ ys) ∷ x ∷ ys)
          ≡⟨ h₂ {ξ (x ∷ ys) ∷ x ∷ ys} ⟩
            ⟦ g ⟧ (ξ (x ∷ ys) ∷ x ∷ ys)
          ≡⟨ cong (⟦ g ⟧ ∘ (_∷ x ∷ ys)) (do-rec f g h₁ h₂ {x ∷ ys}) ⟩
            ⟦ g ⟧ (#rec ⟦ f ⟧ ⟦ g ⟧ (x ∷ ys) ∷ x ∷ ys)
          ≡⟨⟩
            #rec ⟦ f ⟧ ⟦ g ⟧ (suc x ∷ ys)
          ∎

    e→i§ : ∀ {n m} {φs : #Fun§ n m} → IsPrim§ φs → Σ (Prim§ n m) λ fs →
              ∀ {xs} → for φs (_$ xs) ≡ for ⟦ fs ⟧§ (_$ xs)
    e→i§ []       = [] , refl
    e→i§ (d ∷ ds) with e→i d | e→i§ ds
    ... | f , h | fs , hs = f ∷ fs , cong₂ _∷_ h hs


----------------------------------------------------------------------------------------------------

-- TODO: clean this up

-- some primitive recursive n-place functions on naturals
-- Troelstra and van Dalen (1988) §1.3


-- TODO: delete this

-- #const : ∀ {n} → Nat → #Fun n
-- #const zero    = #comp #zero []
-- #const (suc x) = #comp #suc (#const x ∷ [])
--
-- ok-#const : ∀ {n} x (ys : Nat§ n) → #const x ys ≡ x
-- ok-#const zero    ys = refl
-- ok-#const (suc x) ys = cong suc (ok-#const x ys)
--
-- isprim-#const : ∀ {n} x → IsPrim (#const {n} x)
-- isprim-#const zero    = iscomp refl (iszero refl) []
-- isprim-#const (suc x) = iscomp refl (issuc refl) (isprim-#const x ∷ [])

const : ∀ {n} → Nat → Prim n
const zero    = comp zero []
const (suc x) = comp suc (const x ∷ [])

ok-const : ∀ x → ⟦ const x ⟧ [] ≡ Fun.const {B = Nat§ 0} x []
ok-const zero    = refl
ok-const (suc x) = cong suc (ok-const x)


-- _+_ : Nat → Nat → Nat
-- zero  + y = y
-- suc x + y = suc (x + y)

-- TODO: delete this

-- #add : #Fun 2
-- #add = #rec (#proj zero)
--             (#comp #suc (#proj zero ∷ []))
--
-- ok-#add : ∀ x y → #add (x ∷ y ∷ []) ≡ x + y
-- ok-#add zero    y = refl
-- ok-#add (suc x) y = cong suc (ok-#add x y)
--
-- isprim-#add : IsPrim #add
-- isprim-#add = isrec refl (isproj zero refl)
--                          (iscomp refl (issuc refl) (isproj zero refl ∷ []))

add : Prim 2
add = rec (proj zero)
          (comp suc (proj zero ∷ []))

ok-add : ∀ x y → ⟦ add ⟧ (x ∷ y ∷ []) ≡ x Nat.+ y
ok-add zero    y = refl
ok-add (suc x) y = cong suc (ok-add x y)


-- _*_ : Nat → Nat → Nat
-- zero  * y = zero
-- suc x * y = y + x * y

-- TODO: delete this

-- #mul : #Fun 2
-- #mul = #rec (#const 0)
--             (#comp #add (#proj (suc (suc zero)) ∷ #proj zero ∷ []))
--
-- module _ where
--   open ≡-Reasoning
--
--   ok-#mul : ∀ x y → #mul (x ∷ y ∷ []) ≡ x * y
--   ok-#mul zero    y = refl
--   ok-#mul (suc x) y = begin
--                         #add (y ∷ #mul (x ∷ y ∷ []) ∷ [])
--                       ≡⟨ cong (#add ∘ (y ∷_)) (cong (_∷ []) (ok-#mul x y)) ⟩
--                         #add (y ∷ x * y ∷ [])
--                       ≡⟨ ok-#add y (x * y) ⟩
--                         y + x * y
--                       ∎

mul : Prim 2
mul = rec (const 0)
          (comp add (proj (suc (suc zero)) ∷ proj zero ∷ []))

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

-- TODO: delete this

-- #pred : #Fun 1
-- #pred = #rec (#const 0)
--              (#proj (suc zero))
--
-- ok-#pred : ∀ x → #pred (x ∷ []) ≡ pred x
-- ok-#pred zero    = refl
-- ok-#pred (suc x) = refl

pred : Prim 1
pred = rec (const 0)
           (proj (suc zero))

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

infix  19 _‵=_
infixl 18 _‵∧_ _‵∨_
infixr 17 _‵→_ _‵↔_
infix  16 ‵∀_ ‵∃_
infix  15 ‵¬_
infixr 14 _‵$_

-- terms, indexed by number of potential numerical variables
mutual
  data Tm (k : Nat) : Set where
    ‵var : ∀ (i : Fin k) → Tm k -- i-th numerical variable
    ‵fun : ∀ {n} (φ : Prim n) (ts : Tm§ k n) → Tm k

  Tm§ : Nat → Nat → Set
  Tm§ k n = Vec (Tm k) n

‵zero : ∀ {k} → Tm k
‵zero = ‵fun zero []

‵suc : ∀ {k} → Tm k → Tm k
‵suc t = ‵fun suc (t ∷ [])

-- formulas, indexed by number of potential numerical variables
data Fm (k : Nat) : Set where
  _‵→_ : ∀ (A B : Fm k) → Fm k
  _‵∧_  : ∀ (A B : Fm k) → Fm k
  _‵∨_  : ∀ (A B : Fm k) → Fm k
  ‵∀_   : ∀ (B : Fm (suc k)) → Fm k
  ‵∃_   : ∀ (B : Fm (suc k)) → Fm k
  ‵⊥   : Fm k
  _‵=_  : ∀ (t u : Tm k) → Fm k

Fm§ : Nat → Set
Fm§ k = List (Fm k)

‵¬_ : ∀ {k} → Fm k → Fm k
‵¬ A = A ‵→ ‵⊥

_‵↔_ : ∀ {k} → Fm k → Fm k → Fm k
A ‵↔ B = (A ‵→ B) ‵∧ (B ‵→ A)

_‵≠_ : ∀ {k} → Tm k → Tm k → Fm k
t ‵≠ u = ‵¬ t ‵= u


----------------------------------------------------------------------------------------------------

-- TODO: usual things

infix 4 _∋_
postulate
  -- weaken formula by adding one unused numerical variable
  ↑ : ∀ {k} (A : Fm k) → Fm (suc k)

  -- weaken formulas by adding one unused numerical variable
  ↑§ : ∀ {k} (Γ : Fm§ k) → Fm§ (suc k)

  -- exchange two topomost numerical variables in formula
  ↕ : ∀ {k} (A : Fm (suc (suc k))) → Fm (suc (suc k))

  -- substitute topmost numerical variable in formula by term
  _[_] : ∀ {k} (A : Fm (suc k)) (s : Tm k) → Fm k

  -- assumptions, or typed de Bruijn indices
  _∋_ : ∀ {k} (Γ : Fm§ k) (A : Fm k) → Set

  top : ∀ {k} {Γ : Fm§ k} {A} → A ∷ Γ ∋ A
  pop : ∀ {k} {Γ : Fm§ k} {A C} → Γ ∋ A → C ∷ Γ ∋ A


----------------------------------------------------------------------------------------------------

-- Heyting and Peano arithmetic
data Theory : Set where
  HA : Theory
  PA : Theory

-- derivations, indexed by potential assumptions
infix 3 _/_⊢_
data _/_⊢_ {k} : Theory → Fm§ k → Fm k → Set where
  ‵var    : ∀ {Θ Γ A} (i : Γ ∋ A) → Θ / Γ ⊢ A -- i-th assumption
  ‵lam    : ∀ {Θ Γ A B} (d : Θ / A ∷ Γ ⊢ B) → Θ / Γ ⊢ A ‵→ B
  _‵$_    : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A ‵→ B) (e : Θ / Γ ⊢ A) → Θ / Γ ⊢ B
  ‵pair   : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A) (e : Θ / Γ ⊢ B) → Θ / Γ ⊢ A ‵∧ B
  ‵fst    : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A ‵∧ B) → Θ / Γ ⊢ A
  ‵snd    : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A ‵∧ B) → Θ / Γ ⊢ B
  ‵left   : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A) → Θ / Γ ⊢ A ‵∨ B
  ‵right  : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ B) → Θ / Γ ⊢ A ‵∨ B
  ‵case   : ∀ {Θ Γ A B C} (c : Θ / Γ ⊢ A ‵∨ B) (d : Θ / A ∷ Γ ⊢ C) (e : Θ / B ∷ Γ ⊢ C) →
              Θ / Γ ⊢ C

  --     B(x₀)
  -- --------------
  --   ∀y.B[y/xₒ]
  ‵∀intro : ∀ {Θ Γ B} (d : Θ / ↑§ Γ ⊢ B) → Θ / Γ ⊢ ‵∀ B

  --   ∀y.B[y/x₀]
  -- --------------
  --    B[t/x₀]
  ‵∀elim  : ∀ {Θ Γ B t} (d : Θ / Γ ⊢ ‵∀ B) → Θ / Γ ⊢ B [ t ]

  --    B[t/x₀]
  -- --------------
  --   ∃y.B[y/x₀]
  ‵∃intro : ∀ {Θ Γ B t} (d : Θ / Γ ⊢ B [ t ]) → Θ / Γ ⊢ ‵∃ B

 --                  B(x₀)
  --                   ⋮
  --   ∃x.B[x/x₀]      C
  -- -----------------------
  --           C
  ‵∃elim  : ∀ {Θ Γ B C} (d : Θ / Γ ⊢ ‵∃ B) (e : Θ / B ∷ ↑§ Γ ⊢ ↑ C) → Θ / Γ ⊢ C

  -- HA has explosion (ex falso quodlibet) as primitive
  ‵abort  : ∀ {Γ C} (d : HA / Γ ⊢ ‵⊥) → HA / Γ ⊢ C

  -- PA has double negation elimination (reductio ad absurdum) as primitive
  ‵magic  : ∀ {Γ A} (d : PA / ‵¬ A ∷ Γ ⊢ ‵⊥) → PA / Γ ⊢ A

  ‵refl   : ∀ {Θ Γ t} → Θ / Γ ⊢ t ‵= t
  ‵sym    : ∀ {Θ Γ t u} (d : Θ / Γ ⊢ t ‵= u) → Θ / Γ ⊢ u ‵= t
  ‵trans  : ∀ {Θ Γ s t u} (d : Θ / Γ ⊢ s ‵= t) (e : Θ / Γ ⊢ t ‵= u) → Θ / Γ ⊢ s ‵= u

  ‵cong   : ∀ {Θ Γ n ts u} (φ : Prim n) (i : Fin n) (d : Θ / Γ ⊢ get i ts ‵= u) →
              Θ / Γ ⊢ ‵fun φ ts ‵= ‵fun φ (put i ts u)

  ‵dis    : ∀ {Θ Γ t} → Θ / Γ ⊢ ‵suc t ‵≠ ‵zero

  ‵inj    : ∀ {Θ Γ t u} (d : Θ / Γ ⊢ ‵suc t ‵= ‵suc u) → Θ / Γ ⊢ t ‵= u

   --   B[0/x₀]    ∀y.B[y/x₀]→B[y+1/x₀]
   -- ------------------------------------
   --              ∀y.B[y/x₀]
  ‵ind    : ∀ {Θ Γ B} (d : Θ / Γ ⊢ B [ ‵zero ])
              (e : Θ / Γ ⊢ ‵∀ B ‵→ (↕ (↑ B)) [ ‵suc (‵var zero) ]) →
              Θ / Γ ⊢ ‵∀ B

  ‵proj   : ∀ {Θ Γ n ts} (i : Fin n) → Θ / Γ ⊢ ‵fun (proj i) ts ‵= get i ts

  ‵comp   : ∀ {Θ Γ n m ts} (ψ : Prim m) (φs : Prim§ n m) →
              Θ / Γ ⊢ ‵fun (comp ψ φs) ts ‵= ‵fun ψ (for φs λ φ → ‵fun φ ts)

  ‵rec    : ∀ {Θ Γ n s ts} (φ : Prim n) (ψ : Prim (suc (suc n))) →
              Θ / Γ ⊢ ‵fun (rec φ ψ) (‵zero ∷ ts) ‵= ‵fun φ ts ‵∧
                ‵fun (rec φ ψ) (‵suc s ∷ ts) ‵= ‵fun ψ (‵fun (rec φ ψ) (s ∷ ts) ∷ s ∷ ts)

‵congsuc : ∀ {Θ k} {Γ : Fm§ k} {t u} → Θ / Γ ⊢ t ‵= u → Θ / Γ ⊢ ‵suc t ‵= ‵suc u
‵congsuc d = ‵cong suc zero d


----------------------------------------------------------------------------------------------------

-- TODO: more usual things

postulate
  -- weaken derivation by adding one unused assumption
  ⇑ : ∀ {Θ k} {Γ : Fm§ k} {A C} → Θ / Γ ⊢ A → Θ / C ∷ Γ ⊢ A


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
  ↔refl = ‵pair (‵lam (‵var top)) (‵lam (‵var top))

  ↔sym : ∀ {A B} → Θ / Γ ⊢ A ‵↔ B → Θ / Γ ⊢ B ‵↔ A
  ↔sym d = ‵pair (‵snd d) (‵fst d)

  ↔trans : ∀ {A B C} → Θ / Γ ⊢ A ‵↔ B → Θ / Γ ⊢ B ‵↔ C → Θ / Γ ⊢ A ‵↔ C
  ↔trans d e = ‵pair
                  (‵lam (‵fst (⇑ e) ‵$ ‵fst (⇑ d) ‵$ ‵var top))
                  (‵lam (‵snd (⇑ d) ‵$ ‵snd (⇑ e) ‵$ ‵var top))

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

PA-abort : ∀ {k} {Γ : Fm§ k} {C} → PA / Γ ⊢ ‵⊥ → PA / Γ ⊢ C
PA-abort d = ‵magic (⇑ d)

abort : ∀ {Θ k} {Γ : Fm§ k} {C} → Θ / Γ ⊢ ‵⊥ → Θ / Γ ⊢ C
abort {HA} d = ‵abort d
abort {PA} d = PA-abort d

lem2 : ∀ {k} {Γ : Fm§ k} {A} → HA / Γ ⊢ A → PA / Γ ⊢ A
lem2 (‵var i)      = ‵var i
lem2 (‵lam d)      = ‵lam (lem2 d)
lem2 (d ‵$ e)      = lem2 d ‵$ lem2 e
lem2 (‵pair d e)   = ‵pair (lem2 d) (lem2 e)
lem2 (‵fst d)      = ‵fst (lem2 d)
lem2 (‵snd d)      = ‵snd (lem2 d)
lem2 (‵left d)     = ‵left (lem2 d)
lem2 (‵right d)    = ‵right (lem2 d)
lem2 (‵case c d e) = ‵case (lem2 c) (lem2 d) (lem2 e)
lem2 (‵∀intro d)   = ‵∀intro (lem2 d)
lem2 (‵∀elim d)    = ‵∀elim (lem2 d)
lem2 (‵∃intro d)   = ‵∃intro (lem2 d)
lem2 (‵∃elim d e)  = ‵∃elim (lem2 d) (lem2 e)
lem2 (‵abort d)    = PA-abort (lem2 d)
lem2 ‵refl         = ‵refl
lem2 (‵sym d)      = ‵sym (lem2 d)
lem2 (‵trans d e)  = ‵trans (lem2 d) (lem2 e)
lem2 (‵cong φ i d) = ‵cong φ i (lem2 d)
lem2 ‵dis          = ‵dis
lem2 (‵inj d)      = ‵inj (lem2 d)
lem2 (‵ind d e)    = ‵ind (lem2 d) (lem2 e)
lem2 (‵proj i)     = ‵proj i
lem2 (‵comp ψ φs)  = ‵comp ψ φs
lem2 (‵rec φ ψ)    = ‵rec φ ψ


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
                 ‵fun (const 1) (tabulate ‵var) ‵= ‵zero ‵→ ‵suc ‵zero ‵= ‵zero

  goal = ‵lam
           (‵trans
             (‵trans
               (‵cong suc zero
                 (‵sym (‵comp zero [])))
               (‵sym (‵comp suc (comp zero [] ∷ []))))
             (‵var top))

  goal′ = ‵lam
            (begin
              ‵suc ‵zero
            =⟨⟩
              ‵fun suc (‵fun zero [] ∷ [])
            =⟨ ‵cong suc zero (
                begin
                  ‵fun zero []
                =˘⟨ ‵comp zero [] ⟩
                  ‵fun (comp zero []) (tabulate ‵var)
                ∎)
              ⟩
              ‵fun suc (‵fun (comp zero []) (tabulate ‵var) ∷ [])
            =˘⟨ ‵comp suc (comp zero [] ∷ []) ⟩
              ‵fun (comp suc (comp zero [] ∷ [])) (tabulate ‵var)
            =⟨⟩
              ‵fun (const 1) (tabulate ‵var)
            =⟨ ‵var top ⟩
              ‵zero
            ∎)


lem3 : ∀ {Θ k} {Γ : Fm§ k} (A : Fm k) {{_ : IsQFree A}} → Σ (Prim k) λ φ →
         Θ / Γ ⊢ A ‵↔ ‵fun φ (tabulate ‵var) ‵= ‵zero
lem3 (A ‵→ B) = {!!}
lem3 (A ‵∧ B) = {!!}
lem3 (A ‵∨ B) = {!!}
lem3 ‵⊥ = const 1 , ‵pair (‵lam (abort (‵var top))) (‵lam (‵dis ‵$ goal ‵$ ‵var top))
lem3 (t ‵= u) = {!!}


----------------------------------------------------------------------------------------------------

-- TODO: double-negation translation
-- TODO: A-translation


----------------------------------------------------------------------------------------------------
