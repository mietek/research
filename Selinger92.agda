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

open import Data.Sum using (_⊎_)
  renaming (inj₁ to left ; inj₂ to right)

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
    zero : Prim zero
    suc  : Prim (suc zero)
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

#comp : ∀ {n m} (ψ : Fun m) (φs : Fun§ n m) → Fun n
#comp ψ φs xs = ψ (for φs (_$ xs))

#rec : ∀ {n} (φ : Fun n) (ψ : Fun (suc (suc n))) → Fun (suc n)
#rec φ ψ (zero  ∷ ys) = φ ys
#rec φ ψ (suc x ∷ ys) = ψ (#rec φ ψ (x ∷ ys) ∷ x ∷ ys)

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

-- TODO: probably pointless; delete this

_≐_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → (A → B) → Set (a ⊔ b)
f ≐ f′ = ∀ {x} → f x ≡ f′ x

mutual
  data IsPrim : ∀ {n} → Fun n → Set where
    iszero : ∀ {ξ : Fun zero} (h : ξ ≐ #zero) → IsPrim ξ
    issuc  : ∀ {ξ : Fun (suc zero)} (h : ξ ≐ #suc) → IsPrim ξ
    isproj : ∀ {n} i {ξ : Fun n} (h : ξ ≐ #proj i) → IsPrim ξ
    iscomp : ∀ {n m} {ξ : Fun n} {ψ : Fun m} {φs : Fun§ n m} →
               (h : ξ ≐ #comp ψ φs) (e : IsPrim ψ) (ds : IsPrim§ φs) → IsPrim ξ
    isrec  : ∀ {n} {ξ : Fun (suc n)} {φ : Fun n} {ψ : Fun (suc (suc n))} →
               (h : ξ ≐ #rec φ ψ) (d : IsPrim φ) (e : IsPrim ψ) → IsPrim ξ

  data IsPrim§ {n} : ∀ {m} → Fun§ n m → Set where
    []  : IsPrim§ []
    _∷_ : ∀ {m} {φ : Fun n} {φs : Fun§ n m} (d : IsPrim φ) (ds : IsPrim§ φs) →
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
    e→i : ∀ {n} {φ : Fun n} → IsPrim φ → Σ (Prim n) λ f → φ ≐ ⟦ f ⟧
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

    e→i§ : ∀ {n m} {φs : Fun§ n m} → IsPrim§ φs → Σ (Prim§ n m) λ fs →
              ∀ {xs} → for φs (_$ xs) ≡ for ⟦ fs ⟧§ (_$ xs)
    e→i§ []       = [] , refl
    e→i§ (d ∷ ds) with e→i d | e→i§ ds
    ... | f , h | fs , hs = f ∷ fs , cong₂ _∷_ h hs


----------------------------------------------------------------------------------------------------

-- TODO: clean this up

-- some primitive recursive n-ary functions on naturals
-- Troelstra and van Dalen (1988) §1.3


-- TODO: delete this

-- #const : ∀ {n} → Nat → Fun n
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

-- #add : Fun 2
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

-- #mul : Fun 2
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

-- #pred : Fun 1
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

infix  19 _‵=_ _‵≠_
infixl 18 _‵∧_ _‵∨_
infixr 17 _‵→_ _‵↔_
infixr 16 _‵$_

-- terms, indexed by number of term variables
mutual
  data Tm (k : Nat) : Set where
    ‵var : ∀ (i : Fin k) → Tm k -- i-th term variable
    ‵fun : ∀ {n} (φ : Prim n) (ts : Tm§ k n) → Tm k

  Tm§ : Nat → Nat → Set
  Tm§ k n = Vec (Tm k) n

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

-- renaming for terms and formulas

mutual
  frenTm : ∀ {k k′} → k ≤ k′ → Tm k → Tm k′
  frenTm η (‵var i)    = ‵var (frenFin η i)
  frenTm η (‵fun φ ts) = ‵fun φ (frenTm§ η ts)

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
  later : ∀ {k} {A : Fm (suc k)} → A ≡ (frenFm (lift≤ (wk≤ id≤)) A [ ‵var zero ])


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

  ‵cong   : ∀ {Θ Γ n ts u} (φ : Prim n) (i : Fin n) (d : Θ / Γ ⊢ get i ts ‵= u) →
               Θ / Γ ⊢ ‵fun φ ts ‵= ‵fun φ (put i ts u)

  ‵dis    : ∀ {Θ Γ t} → Θ / Γ ⊢ ‵suc t ‵≠ ‵zero

  ‵inj    : ∀ {Θ Γ t u} (d : Θ / Γ ⊢ ‵suc t ‵= ‵suc u) → Θ / Γ ⊢ t ‵= u

   --   A[0/x₀]    ∀y.A[y/x₀]→A[y+1/x₀]
   -- ------------------------------------
   --              ∀y.A[y/x₀]
  ‵ind    : ∀ {Θ Γ A} (d : Θ / Γ ⊢ A [ ‵zero ])
               (e : Θ / Γ ⊢ ‵∀ (A ‵→ (↕ (fwkFm A)) [ ‵suc (‵var zero) ])) →
               Θ / Γ ⊢ ‵∀ A

  ‵proj   : ∀ {Θ Γ n ts} (i : Fin n) → Θ / Γ ⊢ ‵fun (proj i) ts ‵= get i ts

  ‵comp   : ∀ {Θ Γ n m ts} (ψ : Prim m) (φs : Prim§ n m) →
               Θ / Γ ⊢ ‵fun (comp ψ φs) ts ‵= ‵fun ψ (for φs λ φ → ‵fun φ ts)

  ‵rec    : ∀ {Θ Γ n s ts} (φ : Prim n) (ψ : Prim (suc (suc n))) →
               Θ / Γ ⊢ ‵fun (rec φ ψ) (‵zero ∷ ts) ‵= ‵fun φ ts ‵∧
                 ‵fun (rec φ ψ) (‵suc s ∷ ts) ‵= ‵fun ψ (‵fun (rec φ ψ) (s ∷ ts) ∷ s ∷ ts)

‵congsuc : ∀ {Θ k} {Γ : Fm§ k} {t u} → Θ / Γ ⊢ t ‵= u → Θ / Γ ⊢ ‵suc t ‵= ‵suc u
‵congsuc d = ‵cong suc zero d


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
ren η (‵cong φ i d)    = ‵cong φ i (ren η d)
ren η ‵dis             = ‵dis
ren η (‵inj d)         = ‵inj (ren η d)
ren η (‵ind d e)       = ‵ind (ren η d) (ren η e)
ren η (‵proj i)        = ‵proj i
ren η (‵comp ψ φs)     = ‵comp ψ φs
ren η (‵rec φ ψ)       = ‵rec φ ψ

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
lem2 (‵cong φ i d)    = ‵cong φ i (lem2 d)
lem2 ‵dis             = ‵dis
lem2 (‵inj d)         = ‵inj (lem2 d)
lem2 (‵ind d e)       = ‵ind (lem2 d) (lem2 e)
lem2 (‵proj i)        = ‵proj i
lem2 (‵comp ψ φs)     = ‵comp ψ φs
lem2 (‵rec φ ψ)       = ‵rec φ ψ


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
  ↔refl = ‵pair (‵lam (‵var zero)) (‵lam (‵var zero))

  ↔sym : ∀ {A B} → Θ / Γ ⊢ A ‵↔ B → Θ / Γ ⊢ B ‵↔ A
  ↔sym d = ‵pair (‵snd d) (‵fst d)

  ↔trans : ∀ {A B C} → Θ / Γ ⊢ A ‵↔ B → Θ / Γ ⊢ B ‵↔ C → Θ / Γ ⊢ A ‵↔ C
  ↔trans d e = ‵pair
                  (‵lam (‵fst (wk e) ‵$ ‵fst (wk d) ‵$ ‵var zero))
                  (‵lam (‵snd (wk d) ‵$ ‵snd (wk e) ‵$ ‵var zero))

  ↔cong→ : ∀ {A A′ B B′} → Θ / Γ ⊢ A ‵↔ A′ → Θ / Γ ⊢ B ‵↔ B′ →
               Θ / Γ ⊢ (A ‵→ B) ‵↔ (A′ ‵→ B′)
  ↔cong→ d e = ‵pair
                   (‵lam (‵lam
                     (‵fst (wk (wk e)) ‵$ ‵var (suc zero) ‵$ ‵snd (wk (wk d)) ‵$ ‵var zero)))
                   (‵lam (‵lam
                     (‵snd (wk (wk e)) ‵$ ‵var (suc zero) ‵$ ‵fst (wk (wk d)) ‵$ ‵var zero)))

  ↔cong∧ : ∀ {A A′ B B′} → Θ / Γ ⊢ A ‵↔ A′ → Θ / Γ ⊢ B ‵↔ B′ →
              Θ / Γ ⊢ A ‵∧ B ‵↔ A′ ‵∧ B′
  ↔cong∧ d e = ‵pair
                  (‵lam (‵pair
                    (‵fst (wk d) ‵$ ‵fst (‵var zero))
                    (‵fst (wk e) ‵$ ‵snd (‵var zero))))
                  (‵lam (‵pair
                    (‵snd (wk d) ‵$ ‵fst (‵var zero))
                    (‵snd (wk e) ‵$ ‵snd (‵var zero))))

  ↔cong∨ : ∀ {A A′ B B′} → Θ / Γ ⊢ A ‵↔ A′ → Θ / Γ ⊢ B ‵↔ B′ →
              Θ / Γ ⊢ A ‵∨ B ‵↔ A′ ‵∨ B′
  ↔cong∨ d e = ‵pair
                  (‵lam (‵case (‵var zero)
                    (‵left (‵fst (wk (wk d)) ‵$ ‵var zero))
                    (‵right (‵fst (wk (wk e)) ‵$ ‵var zero))))
                  (‵lam (‵case (‵var zero)
                    (‵left (‵snd (wk (wk d)) ‵$ ‵var zero))
                    (‵right (‵snd (wk (wk e)) ‵$ ‵var zero))))

  ↔cong∀ : ∀ {A A′} → Θ / fwkFm§ Γ ⊢ A ‵↔ A′ → Θ / Γ ⊢ (‵∀ A) ‵↔ (‵∀ A′)
  ↔cong∀ d = ‵pair
                (‵lam (‵∀intro (fwk (wk⊆ id⊆) (‵fst d) ‵$ ‵∀elim (‵var zero) later)))
                (‵lam (‵∀intro (fwk (wk⊆ id⊆) (‵snd d) ‵$ ‵∀elim (‵var zero) later)))

  ↔cong∃ : ∀ {A A′} → Θ / fwkFm§ Γ ⊢ A ‵↔ A′ → Θ / Γ ⊢ (‵∃ A) ‵↔ (‵∃ A′)
  ↔cong∃ d = ‵pair
                (‵lam (‵∃elim (‵var zero) (‵∃intro (‵fst (wk (wk d)) ‵$ ‵var zero) later)))
                (‵lam (‵∃elim (‵var zero) (‵∃intro (‵snd (wk (wk d)) ‵$ ‵var zero) later)))

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
  ¬¬em = ‵lam (‵var zero ‵$ ‵right (‵lam (‵var (suc zero) ‵$ ‵left (‵var zero))))

  dni : ∀ {A} → Θ / Γ ⊢ A ‵→ ‵¬ ‵¬ A
  dni = ‵lam (‵lam (‵var zero ‵$ ‵var (suc zero)))

-- non-constructive
module _ {k} {Γ : Fm§ k} where
  dne : ∀ {A} → PA / Γ ⊢ ‵¬ ‵¬ A ‵→ A
  dne = ‵lam (‵magic (‵var (suc zero) ‵$ ‵var zero))

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
  pdm1 = ‵lam (‵lam (‵case (‵var (suc zero))
           (‵var zero ‵$ ‵fst (‵var (suc zero)))
           (‵var zero ‵$ ‵snd (‵var (suc zero)))))

  qdm1 : ∀ {A} → Θ / Γ ⊢ ‵∃ (‵¬ A) ‵→ ‵¬ (‵∀ A)
  qdm1 = ‵lam (‵lam (‵∃elim (‵var (suc zero))
           (‵var zero ‵$ ‵∀elim (‵var (suc zero)) later)))

  npdm1 : ∀ {A B} → Θ / Γ ⊢ A ‵∨ B ‵→ ‵¬ (‵¬ A ‵∧ ‵¬ B)
  npdm1 = ‵lam (‵lam (abort (‵case (‵var (suc zero))
            (‵fst (‵var (suc zero)) ‵$ ‵var zero)
            (‵snd (‵var (suc zero)) ‵$ ‵var zero))))

  nqdm1 : ∀ {A} → Θ / Γ ⊢ ‵∃ A ‵→ ‵¬ (‵∀ (‵¬ A))
  nqdm1 = ‵lam (‵lam (abort (‵∃elim (‵var (suc zero))
            (‵∀elim (‵var (suc zero)) later ‵$ ‵var zero))))

  pdm2 : ∀ {A B} → Θ / Γ ⊢ ‵¬ A ‵∧ ‵¬ B ‵→ ‵¬ (A ‵∨ B)
  pdm2 = ‵lam (‵lam (‵case (‵var zero)
           (‵fst (‵var (suc (suc zero))) ‵$ ‵var zero)
           (‵snd (‵var (suc (suc zero))) ‵$ ‵var zero)))

  qdm2 : ∀ {A} → Θ / Γ ⊢ ‵∀ (‵¬ A) ‵→ ‵¬ (‵∃ A)
  qdm2 = ‵lam (‵lam (‵∃elim (‵var zero)
           (‵∀elim (‵var (suc (suc zero))) later ‵$ ‵var zero)))

  npdm2 : ∀ {A B} → Θ / Γ ⊢ A ‵∧ B ‵→ ‵¬ (‵¬ A ‵∨ ‵¬ B)
  npdm2 = ‵lam (‵lam (abort (‵case (‵var zero)
            (‵var zero ‵$ ‵fst (‵var (suc (suc zero))))
            (‵var zero ‵$ ‵snd (‵var (suc (suc zero)))))))

  nqdm2 : ∀ {A} → Θ / Γ ⊢ ‵∀ A ‵→ ‵¬ (‵∃ (‵¬ A))
  nqdm2 = ‵lam (‵lam (abort (‵∃elim (‵var zero)
            (‵var zero ‵$ ‵∀elim (‵var (suc (suc zero))) later))))

  pdm3 : ∀ {A B} → Θ / Γ ⊢ ‵¬ (A ‵∨ B) ‵→ ‵¬ A ‵∧ ‵¬ B
  pdm3 = ‵lam (‵pair
           (‵lam (‵var (suc zero) ‵$ ‵left (‵var zero)))
           (‵lam (‵var (suc zero) ‵$ ‵right (‵var zero))))

  qdm3 : ∀ {A} → Θ / Γ ⊢ ‵¬ (‵∃ A) ‵→ ‵∀ (‵¬ A)
  qdm3 = ‵lam (‵∀intro (‵lam
           (‵var (suc zero) ‵$ ‵∃intro (‵var zero) later)))

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
                 ‵fun (const 1) (tabulate ‵var) ‵= ‵zero ‵→ ‵suc ‵zero ‵= ‵zero

  goal = ‵lam
           (‵trans
             (‵trans
               (‵cong suc zero
                 (‵sym (‵comp zero [])))
               (‵sym (‵comp suc (comp zero [] ∷ []))))
             (‵var zero))

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
            =⟨ ‵var zero ⟩
              ‵zero
            ∎)


-- TODO: lemma 3

-- lem3 : ∀ {Θ k} {Γ : Fm§ k} (A : Fm k) {{_ : IsQFree A}} → Σ (Prim k) λ φ →
--          Θ / Γ ⊢ A ‵↔ ‵fun φ (tabulate ‵var) ‵= ‵zero
-- lem3 (A ‵→ B) = {!!}
-- lem3 (A ‵∧ B)  = {!!}
-- lem3 (A ‵∨ B)  = {!!}
-- lem3 ‵⊥       = const 1 , ‵pair (‵lam (abort (‵var zero))) (‵lam (‵dis ‵$ goal ‵$ ‵var zero))
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

  lem5-2 : ∀ {k} {Γ : Fm§ k} A → HA / Γ ⊢ ‵¬ ‵¬ (A °) ‵→ A °
  lem5-2 (A ‵→ B) = {!!}
  lem5-2 (A ‵∧ B)  = ‵lam (‵pair
                       (lem5-2 A ‵$ ‵lam
                         (‵var (suc zero) ‵$ ‵lam
                           (‵var (suc zero) ‵$ ‵fst (‵var zero))))
                       (lem5-2 B ‵$ ‵lam
                         (‵var (suc zero) ‵$ ‵lam
                           (‵var (suc zero) ‵$ ‵snd (‵var zero)))))
  lem5-2 (A ‵∨ B)  = {!!}
  lem5-2 (‵∀ A)    = {!!}
  lem5-2 (‵∃ A)    = {!!}
  lem5-2 ‵⊥       = ‵lam (‵var zero ‵$ ‵lam (‵var zero))
  lem5-2 (t ‵= u)  = {!!}

  lem5-3∋ : ∀ {k} {Γ : Fm§ k} {A} → Γ ∋ A → Γ °§ ∋ A °
  lem5-3∋ zero    = zero
  lem5-3∋ (suc i) = suc (lem5-3∋ i)

  lem5-3 : ∀ {k} {Γ : Fm§ k} {A} → PA / Γ ⊢ A → HA / Γ °§ ⊢ A °
  lem5-3 (‵var i)         = ‵var (lem5-3∋ i)
  lem5-3 (‵lam d)         = ‵lam (lem5-3 d)
  lem5-3 (d ‵$ e)         = lem5-3 d ‵$ lem5-3 e
  lem5-3 (‵pair d e)      = ‵pair (lem5-3 d) (lem5-3 e)
  lem5-3 (‵fst d)         = ‵fst (lem5-3 d)
  lem5-3 (‵snd d)         = ‵snd (lem5-3 d)
  lem5-3 (‵left d)        = {!!}
  lem5-3 (‵right d)       = {!!}
  lem5-3 (‵case c d e)    = {!!}
  lem5-3 (‵∀intro d)      = {!!}
  lem5-3 (‵∀elim d refl)  = ‵∀elim (lem5-3 d) probably
  lem5-3 (‵∃intro d refl) = {!!}
  lem5-3 (‵∃elim d e)     = {!!}
  lem5-3 (‵magic d)       = {!!}
  lem5-3 ‵refl            = {!!}
  lem5-3 (‵sym d)         = {!!}
  lem5-3 (‵trans d e)     = {!!}
  lem5-3 (‵cong φ i d)    = {!!}
  lem5-3 ‵dis             = {!!}
  lem5-3 (‵inj d)         = {!!}
  lem5-3 (‵ind d e)       = {!!}
  lem5-3 (‵proj i)        = {!!}
  lem5-3 (‵comp ψ φs)     = {!!}
  lem5-3 (‵rec φ ψ)       = {!!}

  lem5-3a : ∀ {k} {Γ : Fm§ k} {A} → HA / Γ °§ ⊢ A ° → PA / Γ ⊢ A
  lem5-3a {A = A} d = {!‵snd (lem5-1 A)!}

--  lem5-4 : ∀ {k} {Γ : Fm§ k} {A}


----------------------------------------------------------------------------------------------------

-- TODO: A-translation

-- TODO: lemma 6


----------------------------------------------------------------------------------------------------

-- TODO: lemma 7

-- TODO: corollary 8

-- TODO: theorem 1


----------------------------------------------------------------------------------------------------
