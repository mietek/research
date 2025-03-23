-- 2025-03-21
-- Friedman’s A-Translation
-- https://www.mscs.dal.ca/~selinger/papers/friedman.pdf

module Selinger92 where

open import Data.Fin using (Fin ; zero ; suc)

open import Data.List using (List ; [] ; _∷_)

open import Data.Nat using (zero ; suc ; _+_ ; _*_ ; pred ; _∸_)
  renaming (ℕ to Nat)

open import Data.Product using (Σ ; _,_ ; _×_)
  renaming (proj₁ to fst ; proj₂ to snd)

import Data.Vec as Vec
open Vec using (Vec ; [] ; _∷_)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open ≡-Reasoning


----------------------------------------------------------------------------------------------------

-- propositional equality things

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} (f : A → B → C → D)
          {x x′ y y′ z z′} → x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl


----------------------------------------------------------------------------------------------------

-- vector things

get : ∀ {a} {A : Set a} {n} → Fin n → Vec A n → A
get i xs = Vec.lookup xs i

put : ∀ {a} {A : Set a} {n} → Fin n → Vec A n → A → Vec A n
put i xs y = xs Vec.[ i ]≔ y

for : ∀ {a b} {A : Set a} {B : Set b} {n} → Vec A n → (A → B) → Vec B n
for xs f = Vec.map f xs


----------------------------------------------------------------------------------------------------

-- natural things

rec : ∀ {a} {A : Set a} → Nat → A → (Nat → A → A) → A
rec zero    x f = x
rec (suc y) x f = f y (rec y x f)


----------------------------------------------------------------------------------------------------

-- building blocks for the standard model of primitive recursive n-place functions on naturals
-- Troelstra (1973) §1.3.4

-- n-place functions on naturals
#Fun : Nat → Set
#Fun n = Vec Nat n → Nat

#Fun* : Nat → Nat → Set
#Fun* n m = Vec (#Fun n) m

#zero : #Fun 0
#zero [] = zero

#suc : #Fun 1
#suc (x ∷ []) = suc x

#get : ∀ {n} → Fin n → #Fun n
#get i xs = get i xs

#comp : ∀ {n m} (ψ : #Fun m) (φs : #Fun* n m) → #Fun n
#comp ψ φs xs = ψ (for φs λ φ → φ xs)

#rec : ∀ {n} (φ : #Fun n) (ψ : #Fun (suc (suc n))) → #Fun (suc n)
-- TODO: maybe more clear to define #rec directly
-- #rec φ ψ (x ∷ ys) = rec x (φ ys) (λ x′ r → ψ (r ∷ x′ ∷ ys))
#rec φ ψ (zero  ∷ ys) = φ ys
#rec φ ψ (suc x ∷ ys) = ψ (#rec φ ψ (x ∷ ys) ∷ x ∷ ys)


----------------------------------------------------------------------------------------------------

-- some primitive recursive n-place functions on naturals
-- Troelstra and van Dalen (1988) §1.3

#const : ∀ {n} → Nat → #Fun n
#const zero    = #comp #zero []
#const (suc x) = #comp #suc (#const x ∷ [])

ok-#const : ∀ {n} x (ys : Vec Nat n) → #const x ys ≡ x
ok-#const zero    ys = refl
ok-#const (suc x) ys = cong suc (ok-#const x ys)

-- _+_ : Nat → Nat → Nat
-- zero  + y = y
-- suc x + y = suc (x + y)

#add : #Fun 2
#add = #rec (#get zero)
            (#comp #suc (#get zero ∷ []))

ok-#add : ∀ x y → #add (x ∷ y ∷ []) ≡ x + y
ok-#add zero    y = refl
ok-#add (suc x) y = cong suc (ok-#add x y)

-- _*_ : Nat → Nat → Nat
-- zero  * y = zero
-- suc x * y = y + x * y

#mul : #Fun 2
#mul = #rec (#const 0)
            (#comp #add (#get (suc (suc zero)) ∷ #get zero ∷ []))

ok-#mul : ∀ x y → #mul (x ∷ y ∷ []) ≡ x * y
ok-#mul zero    y = refl
ok-#mul (suc x) y = begin
                      #add (y ∷ #mul (x ∷ y ∷ []) ∷ [])
                    ≡⟨ cong (#add ∘ (y ∷_)) (cong (_∷ []) (ok-#mul x y)) ⟩
                      #add (y ∷ x * y ∷ [])
                    ≡⟨ ok-#add y (x * y) ⟩
                      y + x * y
                    ∎

-- pred : Nat → Nat
-- pred x = x ∸ 1

#pred : #Fun 1
#pred = #rec (#const 0)
             (#get (suc zero))

ok-#pred : ∀ x → #pred (x ∷ []) ≡ pred x
ok-#pred zero    = refl
ok-#pred (suc x) = refl


-- TODO: subtraction

-- _∸_ : Nat → Nat → Nat
-- x     ∸ zero  = x
-- zero  ∸ suc y = zero
-- suc x ∸ suc y = x ∸ y

_-_ : Nat → Nat → Nat
x - zero  = x
x - suc y = pred (x - y)


----------------------------------------------------------------------------------------------------

-- extensional characterization of primitive recursive n-place functions on naturals
mutual
  data IsPrim : ∀ {n} → #Fun n → Set where
    isprim-#zero : ∀ {ξ : #Fun zero} (h : ∀ {xs} → ξ xs ≡ #zero xs) → IsPrim ξ
    isprim-#suc  : ∀ {ξ : #Fun (suc zero)} (h : ∀ {xs} → ξ xs ≡ #suc xs) → IsPrim ξ
    isprim-#get  : ∀ {n i} {ξ : #Fun n} (h : ∀ {xs} → ξ xs ≡ #get i xs) → IsPrim ξ
    isprim-#comp : ∀ {n m} {ψ : #Fun m} {φs : #Fun* n m} {ξ : #Fun n} →
                     (h : ∀ {xs} → ξ xs ≡ #comp ψ φs xs) → IsPrim ψ → IsPrim* φs → IsPrim ξ
    isprim-#rec  : ∀ {n} {φ : #Fun n} {ψ : #Fun (suc (suc n))} {ξ : #Fun (suc n)} →
                     (h : ∀ {xs} → ξ xs ≡ #rec φ ψ xs) → IsPrim φ → IsPrim ψ → IsPrim ξ

  data IsPrim* {n} : ∀ {m} → #Fun* n m → Set where
    []  : IsPrim* []
    _∷_ : ∀ {m} {φ : #Fun n} {φs : #Fun* n m} → IsPrim φ → IsPrim* φs → IsPrim* (φ ∷ φs)


----------------------------------------------------------------------------------------------------

-- intensional characterization of primitive recursive n-place functions on naturals
data Prim : Nat → Set where
  ‵zero : Prim zero
  ‵suc  : Prim (suc zero)
  ‵get  : ∀ {n} (i : Fin n) → Prim n
  ‵comp : ∀ {n m} (ψ : Prim m) (φs : Vec (Prim n) m) → Prim n
  ‵rec  : ∀ {n} (φ : Prim n) (ψ : Prim (suc (suc n))) → Prim (suc n)

Prim* : Nat → Nat → Set
Prim* n m = Vec (Prim n) m

mutual
  ⟦_⟧ : ∀ {n} → Prim n → #Fun n
  ⟦ ‵zero ⟧      = #zero
  ⟦ ‵suc ⟧       = #suc
  ⟦ ‵get i ⟧     = #get i
  ⟦ ‵comp ψ φs ⟧ = #comp ⟦ ψ ⟧ ⟦ φs ⟧*
  ⟦ ‵rec φ ψ ⟧   = #rec ⟦ φ ⟧ ⟦ ψ ⟧

  ⟦_⟧* : ∀ {n m} → Prim* n m → #Fun* n m
  ⟦ [] ⟧*     = []
  ⟦ φ ∷ φs ⟧* = ⟦ φ ⟧ ∷ ⟦ φs ⟧*

mutual
  i→e : ∀ {n} (φ : Prim n) → IsPrim ⟦ φ ⟧
  i→e ‵zero        = isprim-#zero refl
  i→e ‵suc         = isprim-#suc refl
  i→e (‵get i)     = isprim-#get refl
  i→e (‵comp ψ φs) = isprim-#comp refl (i→e ψ) (i→e* φs)
  i→e (‵rec φ ψ)   = isprim-#rec refl (i→e φ) (i→e ψ)

  i→e* : ∀ {n m} (φs : Prim* n m) → IsPrim* ⟦ φs ⟧*
  i→e* []       = []
  i→e* (φ ∷ φs) = i→e φ ∷ i→e* φs

mutual
  e→i : ∀ {n} {φ : #Fun n} → IsPrim φ → Σ (Prim n) λ f → ∀ {xs} → φ xs ≡ ⟦ f ⟧ xs
  e→i (isprim-#zero h)      = ‵zero , h
  e→i (isprim-#suc h)       = ‵suc , h
  e→i (isprim-#get h)       = ‵get _ , h
  e→i (isprim-#comp h e ds) = {!!}
  e→i (isprim-#rec {φ = φ} {ψ} {ξ} h d e) =
    let (f , h₁) = e→i d in
    let (g , h₂) = e→i e in
    ‵rec f g , λ {xs} → -- TODO: this should be reasoning by pointwise equality, and not by identity
      begin
        ξ xs
      ≡⟨ h {xs} ⟩
        #rec φ ψ xs
      ≡⟨ cong₃ #rec {!!} {!!} refl ⟩
        #rec ⟦ f ⟧ ⟦ g ⟧ xs
      ∎

  e→i* : ∀ {n m} {φs : #Fun* n m} → IsPrim* φs → Σ (Prim* n m) λ fs →
            ∀ {xs} → for φs (λ φ → φ xs) ≡ for ⟦ fs ⟧* (λ f → f xs)
  e→i* = {!!}

-- -- -- ----------------------------------------------------------------------------------------------------

-- -- -- infix 16 ‵¬_
-- -- -- infix 17 ‵∀_ ‵∃_
-- -- -- infixr 18 _‵⊃_ _‵⫗_
-- -- -- infixl 19 _‵∧_ _‵∨_

-- -- -- -- terms, indexed by number of numerical variables
-- -- -- data Tm (k : Nat) : Set where
-- -- --   ‵var : ∀ (i : Fin k) → Tm k -- i-th numerical variable
-- -- --   ‵fun : ∀ {n} (φ : Prim n) (ts : Vec (Tm k) n) → Tm k

-- -- -- Tms : Nat → Nat → Set
-- -- -- Tms k n = Vec (Tm k) n

-- -- -- ‵zero : ∀ {k} → Tm k
-- -- -- ‵zero = ‵fun zero []

-- -- -- ‵suc : ∀ {k} → Tm k → Tm k
-- -- -- ‵suc t = ‵fun suc (t ∷ [])

-- -- -- -- formulas, indexed by number of numerical variables
-- -- -- data Fm (k : Nat) : Set where
-- -- --   _‵⊃_ : ∀ (A B : Fm k) → Fm k
-- -- --   _‵∧_ : ∀ (A B : Fm k) → Fm k
-- -- --   _‵∨_ : ∀ (A B : Fm k) → Fm k
-- -- --   ‵∀_  : ∀ (B : Fm (suc k)) → Fm k
-- -- --   ‵∃_  : ∀ (B : Fm (suc k)) → Fm k
-- -- --   ‵⊥  : Fm k
-- -- --   _‵=_ : ∀ (t u : Tm k) → Fm k

-- -- -- Fms : Nat → Set
-- -- -- Fms k = List (Fm k)

-- -- -- ‵¬_ : ∀ {k} → Fm k → Fm k
-- -- -- ‵¬ A = A ‵⊃ ‵⊥

-- -- -- _‵⫗_ : ∀ {k} → Fm k → Fm k → Fm k
-- -- -- A ‵⫗ B = (A ‵⊃ B) ‵∧ (B ‵⊃ A)

-- -- -- _‵≠_ : ∀ {k} → Tm k → Tm k → Fm k
-- -- -- t ‵≠ u = ‵¬ t ‵= u


-- -- -- ----------------------------------------------------------------------------------------------------

-- -- -- -- TODO: usual things
-- -- -- postulate
-- -- --   -- weaken formula by adding one numerical variable
-- -- --   ↑ : ∀ {k} (A : Fm k) → Fm (suc k)

-- -- --   -- weaken formulas by adding one numerical variable
-- -- --   ↑* : ∀ {k} (Γ : Fms k) → Fms (suc k)

-- -- --   -- substitute topmost numerical variable in formula by term
-- -- --   _[_] : ∀ {k} (A : Fm (suc k)) (s : Tm k) → Fm k

-- -- --   -- typed de Bruijn indices
-- -- --   _∋_ : ∀ {k} (Γ : Fms k) (A : Fm k) → Set


-- -- -- ----------------------------------------------------------------------------------------------------

-- -- -- -- Heyting and Peano arithmetic
-- -- -- data Theory : Set where
-- -- --   HA : Theory
-- -- --   PA : Theory

-- -- -- -- derivations, indexed by assumptions
-- -- -- infix 3 _/_⊢_
-- -- -- data _/_⊢_ {k} : Theory → Fms k → Fm k → Set where
-- -- --   ‵var    : ∀ {Θ Γ A} (i : Γ ∋ A) → Θ / Γ ⊢ A -- i-th assumption
-- -- --   ‵lam    : ∀ {Θ Γ A B} (d : Θ / A ∷ Γ ⊢ B) → Θ / Γ ⊢ A ‵⊃ B
-- -- --   _‵$_    : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A ‵⊃ B) (e : Θ / Γ ⊢ A) → Θ / Γ ⊢ B
-- -- --   ‵pair   : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A) (e : Θ / Γ ⊢ B) → Θ / Γ ⊢ A ‵∧ B
-- -- --   ‵fst    : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A ‵∧ B) → Θ / Γ ⊢ A
-- -- --   ‵snd    : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A ‵∧ B) → Θ / Γ ⊢ B
-- -- --   ‵left   : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ A) → Θ / Γ ⊢ A ‵∨ B
-- -- --   ‵right  : ∀ {Θ Γ A B} (d : Θ / Γ ⊢ B) → Θ / Γ ⊢ A ‵∨ B
-- -- --   ‵case   : ∀ {Θ Γ A B C} (c : Θ / Γ ⊢ A ‵∨ B) (d : Θ / A ∷ Γ ⊢ C) (e : Θ / B ∷ Γ ⊢ C) →
-- -- --               Θ / Γ ⊢ C

-- -- --   --  B[x]
-- -- --   -- ------
-- -- --   -- ∀xB[x]
-- -- --   ‵∀intro : ∀ {Θ Γ B} (d : Θ / ↑* Γ ⊢ B) → Θ / Γ ⊢ ‵∀ B

-- -- --   -- ∀xB[x]
-- -- --   -- ------
-- -- --   --  B[t]
-- -- --   ‵∀elim  : ∀ {Θ Γ B} (t : Tm k) (d : Θ / Γ ⊢ ‵∀ B) → Θ / Γ ⊢ B [ t ]

-- -- --   --  B[t]
-- -- --   -- ------
-- -- --   -- ∃xB[x]
-- -- --   ‵∃intro : ∀ {Θ Γ B} (t : Tm k) (d : Θ / Γ ⊢ B [ t ]) → Θ / Γ ⊢ ‵∃ B

-- -- --   --          B[x]
-- -- --   --           ⋮
-- -- --   --   ∃xB[x]  C
-- -- --   -- -------------
-- -- --   --       C
-- -- --   ‵∃elim  : ∀ {Θ Γ B C} (d : Θ / Γ ⊢ ‵∃ B) (e : Θ / B ∷ ↑* Γ ⊢ ↑ C) → Θ / Γ ⊢ C

-- -- --   -- HA has explosion (EFQ) as primitive
-- -- --   ‵abort  : ∀ {Γ C} (d : HA / Γ ⊢ ‵⊥) → HA / Γ ⊢ C

-- -- --   -- PA has double negation elimination as primitive
-- -- --   ‵magic  : ∀ {Γ A} (d : PA / ‵¬ A ∷ Γ ⊢ ‵⊥) → PA / Γ ⊢ A

-- -- --   ‵refl   : ∀ {Θ Γ t} → Θ / Γ ⊢ t ‵= t
-- -- --   ‵sym    : ∀ {Θ Γ t u} (d : Θ / Γ ⊢ t ‵= u) → Θ / Γ ⊢ u ‵= t
-- -- --   ‵trans  : ∀ {Θ Γ s t u} (d : Θ / Γ ⊢ s ‵= t) (e : Θ / Γ ⊢ t ‵= u) → Θ / Γ ⊢ s ‵= u

-- -- --   ‵cong   : ∀ {Θ Γ n ts u} (φ : Prim n) (i : Fin n) (d : Θ / Γ ⊢ get i ts ‵= u) →
-- -- --               Θ / Γ ⊢ ‵fun φ ts ‵= ‵fun φ (put i ts u)

-- -- --   ‵sucpos : ∀ {Θ Γ t} → Θ / Γ ⊢ ‵suc t ‵≠ ‵zero
-- -- --   ‵sucinj : ∀ {Θ Γ t u} (d : Θ / Γ ⊢ ‵suc t ‵= ‵suc u) → Θ / Γ ⊢ t ‵= u

-- -- --   ‵ind    : ∀ {Θ Γ B} (d : Θ / ↑* Γ ⊢ B [ ‵zero ])
-- -- --               (e : Θ / Γ ⊢ ‵∀ B [ ‵var zero ] ‵⊃ B [ ‵suc (‵var zero) ]) →
-- -- --               Θ / Γ ⊢ ‵∀ B [ ‵var zero ]

-- -- --   ‵proj   : ∀ {Θ Γ n ts} (i : Fin n) → Θ / Γ ⊢ ‵fun (proj i) ts ‵= get i ts
-- -- --   ‵comp   : ∀ {Θ Γ n m ts} (φs : Vec (Prim n) m) (ψ : Prim m) →
-- -- --               Θ / Γ ⊢ ‵fun (comp φs ψ) ts ‵= ‵fun ψ (for φs λ φ → ‵fun φ ts)
-- -- --   ‵rec    : ∀ {Θ Γ n s ts} (φ : Prim n) (ψ : Prim (suc (suc n))) →
-- -- --               Θ / Γ ⊢ ‵fun (rec φ ψ) (‵zero ∷ ts) ‵= ‵fun φ ts ‵∧
-- -- --                 ‵fun (rec φ ψ) (‵suc s ∷ ts) ‵= ‵fun ψ (‵fun (rec φ ψ) (s ∷ ts) ∷ s ∷ ts)

-- -- -- ‵congsuc : ∀ {Θ k} {Γ : Fms k} {t u} → Θ / Γ ⊢ t ‵= u → Θ / Γ ⊢ ‵suc t ‵= ‵suc u
-- -- -- ‵congsuc d = ‵cong suc zero d


-- -- -- ----------------------------------------------------------------------------------------------------

-- -- -- -- TODO: usual things
-- -- -- postulate
-- -- --   -- weaken derivation by adding one assumption
-- -- --   ⇑ : ∀ {Θ k} {Γ : Fms k} {A C} → Θ / Γ ⊢ A → Θ / C ∷ Γ ⊢ A

-- -- -- PA/abort : ∀ {k} {Γ : Fms k} {C} → PA / Γ ⊢ ‵⊥ → PA / Γ ⊢ C
-- -- -- PA/abort d = ‵magic (⇑ d)

-- -- -- lem2 : ∀ {k} {Γ : Fms k} {A} → HA / Γ ⊢ A → PA / Γ ⊢ A
-- -- -- lem2 (‵var i)      = ‵var i
-- -- -- lem2 (‵lam d)      = ‵lam (lem2 d)
-- -- -- lem2 (d ‵$ e)      = lem2 d ‵$ lem2 e
-- -- -- lem2 (‵pair d e)   = ‵pair (lem2 d) (lem2 e)
-- -- -- lem2 (‵fst d)      = ‵fst (lem2 d)
-- -- -- lem2 (‵snd d)      = ‵snd (lem2 d)
-- -- -- lem2 (‵left d)     = ‵left (lem2 d)
-- -- -- lem2 (‵right d)    = ‵right (lem2 d)
-- -- -- lem2 (‵case c d e) = ‵case (lem2 c) (lem2 d) (lem2 e)
-- -- -- lem2 (‵∀intro d)   = ‵∀intro (lem2 d)
-- -- -- lem2 (‵∀elim t d)  = ‵∀elim t (lem2 d)
-- -- -- lem2 (‵∃intro t d) = ‵∃intro t (lem2 d)
-- -- -- lem2 (‵∃elim d e)  = ‵∃elim (lem2 d) (lem2 e)
-- -- -- lem2 (‵abort d)    = PA/abort (lem2 d)
-- -- -- lem2 ‵refl         = ‵refl
-- -- -- lem2 (‵sym d)      = ‵sym (lem2 d)
-- -- -- lem2 (‵trans d e)  = ‵trans (lem2 d) (lem2 e)
-- -- -- lem2 (‵cong φ i d) = ‵cong φ i (lem2 d)
-- -- -- lem2 ‵sucpos       = ‵sucpos
-- -- -- lem2 (‵sucinj d)   = ‵sucinj (lem2 d)
-- -- -- lem2 (‵ind d e)    = ‵ind (lem2 d) (lem2 e)
-- -- -- lem2 (‵proj i)     = ‵proj i
-- -- -- lem2 (‵comp φs ψ)  = ‵comp φs ψ
-- -- -- lem2 (‵rec φ ψ)    = ‵rec φ ψ


-- -- -- ----------------------------------------------------------------------------------------------------

-- -- -- -- quantifier-free formulas
-- -- -- data QFree {k} : Fm k → Set where
-- -- --   _‵⊃_ : ∀ {A B} (α : QFree A) (β : QFree B) → QFree (A ‵⊃ B)
-- -- --   _‵∧_ : ∀ {A B} (α : QFree A) (β : QFree B) → QFree (A ‵∧ B)
-- -- --   _‵∨_ : ∀ {A B} (α : QFree A) (β : QFree B) → QFree (A ‵∨ B)
-- -- --   ‵⊥  : QFree ‵⊥
-- -- --   _‵=_ : ∀ {t u} → QFree (t ‵= u)

-- -- -- lem3 : ∀ {k} {Γ : Fms k} {A ts} (α : QFree A) (φ : Prim k) →
-- -- --          HA / Γ ⊢ A ‵⫗ ‵fun φ ts ‵= ‵zero
-- -- -- lem3 α φ = {!!}


-- -- -- ----------------------------------------------------------------------------------------------------

-- -- -- -- TODO: double-negation translation
-- -- -- -- TODO: A-translation


-- -- -- ----------------------------------------------------------------------------------------------------
