module Chapter3 where

module UniqueList where
  open import Data.Nat using (ℕ ; _+_ ; _≤_ ; z≤n ; s≤s)
  open import Data.Nat.Properties using (≤-refl ; ≤-step)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
  open import Relation.Nullary using (Dec ; yes ; no)
  open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)

  mutual
    data UniqueList {ℓ} (X : Set ℓ) : Set ℓ where
      []  : UniqueList X
      _∷_ : (x : X) (xs : UniqueList X) {{_ : xs ∌ x}} → UniqueList X

    infix 4 _∌_
    data _∌_ {ℓ} {X : Set ℓ} : UniqueList X → X → Set ℓ where
      instance
        unique-[] : ∀ {x} → [] ∌ x
        unique-∷  : ∀ {x xs y} {{_ : xs ∌ x}} → x ≢ y → xs ∌ y → x ∷ xs ∌ y

  [_] : ∀ {ℓ} {X : Set ℓ} → X → UniqueList X
  [ x ] = x ∷ []

  length : ∀ {ℓ} {X : Set ℓ} → UniqueList X → ℕ
  length []       = 0
  length (x ∷ xs) = 1 + length xs

  module DecUniqueList {ℓ} {X : Set ℓ} (_≡?_ : (x y : X) → Dec (x ≡ y)) where
    _∌?_ : (xs : UniqueList X) (y : X) → Dec (xs ∌ y)
    []       ∌? y = yes unique-[]
    (x ∷ xs) ∌? y with xs ∌? y | x ≡? y
    ...           | yes xs∌y | no x≢y   = yes (unique-∷ x≢y xs∌y)
    ...           | yes xs∌y | yes refl = no λ { (unique-∷ x≢x xs∌x) → refl ↯ x≢x }
    ...           | no xs∋y  | _        = no λ { (unique-∷ x≢y xs∌y) → xs∌y ↯ xs∋y }

    mutual
      infixl 5 _∪_
      _∪_ : UniqueList X → UniqueList X → UniqueList X
      []                  ∪ ys = ys
      ((x ∷ xs) {{xs∌x}}) ∪ ys with ys ∌? x
      ...                      | yes ys∌x = (x ∷ (xs ∪ ys)) {{∪-preserves-∌ xs∌x ys∌x}}
      ...                      | no ys∋x  = xs ∪ ys

      ∪-preserves-∌ : ∀ {xs ys z} → xs ∌ z → ys ∌ z → xs ∪ ys ∌ z
      ∪-preserves-∌ {[]}            unique-[]             ys∌z = ys∌z
      ∪-preserves-∌ {x′ ∷ xs′} {ys} (unique-∷ x′≢z xs′∌z) ys∌z with ys ∌? x′
      ...                                                      | yes ys∌x′ = unique-∷ x′≢z (∪-preserves-∌ xs′∌z ys∌z)
      ...                                                      | no ys∋x′  = ∪-preserves-∌ xs′∌z ys∌z

    ∪-length-+ : ∀ xs ys → length (xs ∪ ys) ≤ length xs + length ys -- TODO: find a better name
    ∪-length-+ []       ys = ≤-refl
    ∪-length-+ (x ∷ xs) ys with ys ∌? x
    ...                    | yes ys∌x = s≤s (∪-length-+ xs ys)
    ...                    | no ys∋x  = ≤-step (∪-length-+ xs ys)

module SquashedUniqueList where
  -- TODO: do it like Coquand

open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _⊔_ ; _≤_ ; z≤n ; s≤s ; _<_)
open import Data.Nat.Properties using (≤-trans ; ≤-step ; +-mono-≤ ; +-monoˡ-≤ ; module ≤-Reasoning)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open UniqueList

-- 3. Untyped arithmetic expressions

-- 3.1. Introduction

-- 3.2. Syntax

-- 3.2.1. Definition [Terms, inductively]

data Term : Set where
  true false zero  : Term
  succ pred iszero : (t₁ : Term) → Term
  if_then_else     : (t₁ t₂ t₃ : Term) → Term

_≡?_ : (r s : Term) → Dec (r ≡ s)
true                  ≡? true                  = yes refl
true                  ≡? false                 = no λ ()
true                  ≡? zero                  = no λ ()
true                  ≡? succ s₁               = no λ ()
true                  ≡? pred s₁               = no λ ()
true                  ≡? iszero s₁             = no λ ()
true                  ≡? if s₁ then s₂ else s₃ = no λ ()
false                 ≡? true                  = no λ ()
false                 ≡? false                 = yes refl
false                 ≡? zero                  = no λ ()
false                 ≡? succ s₁               = no λ ()
false                 ≡? pred s₁               = no λ ()
false                 ≡? iszero s₁             = no λ ()
false                 ≡? if s₁ then s₂ else s₃ = no λ ()
zero                  ≡? true                  = no λ ()
zero                  ≡? false                 = no λ ()
zero                  ≡? zero                  = yes refl
zero                  ≡? succ s₁               = no λ ()
zero                  ≡? pred s₁               = no λ ()
zero                  ≡? iszero s₁             = no λ ()
zero                  ≡? if s₁ then s₂ else s₃ = no λ ()
succ r₁               ≡? true                  = no λ ()
succ r₁               ≡? false                 = no λ ()
succ r₁               ≡? zero                  = no λ ()
succ r₁               ≡? succ s₁               with r₁ ≡? s₁
...                                            | yes refl = yes refl
...                                            | no r₁≢s₁ = no λ { refl → refl ↯ r₁≢s₁ }
succ r₁               ≡? pred s₁               = no λ ()
succ r₁               ≡? iszero s₁             = no λ ()
succ r₁               ≡? if s₁ then s₂ else s₃ = no λ ()
pred r₁               ≡? true                  = no λ ()
pred r₁               ≡? false                 = no λ ()
pred r₁               ≡? zero                  = no λ ()
pred r₁               ≡? succ s₁               = no λ ()
pred r₁               ≡? pred s₁               with r₁ ≡? s₁
...                                            | yes refl = yes refl
...                                            | no r₁≢s₁ = no λ { refl → refl ↯ r₁≢s₁ }
pred r₁               ≡? iszero s₁             = no λ ()
pred r₁               ≡? if s₁ then s₂ else s₃ = no λ ()
iszero r₁             ≡? true                  = no λ ()
iszero r₁             ≡? false                 = no λ ()
iszero r₁             ≡? zero                  = no λ ()
iszero r₁             ≡? succ s₁               = no λ ()
iszero r₁             ≡? pred s₁               = no λ ()
iszero r₁             ≡? iszero s₁             with r₁ ≡? s₁
...                                            | yes refl = yes refl
...                                            | no r₁≢s₁ = no λ { refl → refl ↯ r₁≢s₁ }
iszero r₁             ≡? if s₁ then s₂ else s₃ = no λ ()
if r₁ then r₂ else r₃ ≡? true                  = no λ ()
if r₁ then r₂ else r₃ ≡? false                 = no λ ()
if r₁ then r₂ else r₃ ≡? zero                  = no λ ()
if r₁ then r₂ else r₃ ≡? succ s₁               = no λ ()
if r₁ then r₂ else r₃ ≡? pred s₁               = no λ ()
if r₁ then r₂ else r₃ ≡? iszero s₁             = no λ ()
if r₁ then r₂ else r₃ ≡? if s₁ then s₂ else s₃ with r₁ ≡? s₁ | r₂ ≡? s₂ | r₃ ≡? s₃
...                                            | yes refl | yes refl | yes refl = yes refl
...                                            | no r₁≢s₁ | _        | _        = no λ { refl → refl ↯ r₁≢s₁ }
...                                            | _        | no r₂≢s₂ | _        = no λ { refl → refl ↯ r₂≢s₂ }
...                                            | _        | _        | no r₃≢s₃ = no λ { refl → refl ↯ r₃≢s₃ }

open module DecUniqueTerms = DecUniqueList _≡?_

-- 3.2.2. Definition [Terms, by inference rules] (redundant)

-- 3.2.3. Definition [Terms, concretely] (redundant)

-- 3.2.4. Exercise (skipped)

-- 3.2.5. Exercise (skipped)

-- 3.2.6. Proposition (skipped)

-- 3.3. Induction on terms

-- 3.3.1. Definition

consts : Term → UniqueList Term
consts true                    = [ true ]
consts false                   = [ false ]
consts zero                    = [ zero ]
consts (succ t₁)               = consts t₁
consts (pred t₁)               = consts t₁
consts (iszero t₁)             = consts t₁
consts (if t₁ then t₂ else t₃) = consts t₁ ∪ consts t₂ ∪ consts t₃

-- 3.3.2. Definition

size : Term → ℕ
size true                    = 1
size false                   = 1
size zero                    = 1
size (succ t₁)               = 1 + size t₁
size (pred t₁)               = 1 + size t₁
size (iszero t₁)             = 1 + size t₁
size (if t₁ then t₂ else t₃) = 1 + size t₁ + size t₂ + size t₃

depth : Term → ℕ
depth true                    = 1
depth false                   = 1
depth zero                    = 1
depth (succ t₁)               = 1 + depth t₁
depth (pred t₁)               = 1 + depth t₁
depth (iszero t₁)             = 1 + depth t₁
depth (if t₁ then t₂ else t₃) = 1 + depth t₁ ⊔ depth t₂ ⊔ depth t₃

-- 3.3.3. Lemma

lem-333 : ∀ (t : Term) → length (consts t) ≤ size t
lem-333 true                    = s≤s z≤n
lem-333 false                   = s≤s z≤n
lem-333 zero                    = s≤s z≤n
lem-333 (succ t₁)               = ≤-step (lem-333 t₁)
lem-333 (pred t₁)               = ≤-step (lem-333 t₁)
lem-333 (iszero t₁)             = ≤-step (lem-333 t₁)
lem-333 (if t₁ then t₂ else t₃) = ≤-step
    (begin
      length (consts t₁ ∪ consts t₂ ∪ consts t₃)
    ≤⟨ ∪-length-+ (consts t₁ ∪ consts t₂) (consts t₃) ⟩
      length (consts t₁ ∪ consts t₂) + length (consts t₃)
    ≤⟨ +-monoˡ-≤ (length (consts t₃)) (∪-length-+ (consts t₁) (consts t₂)) ⟩
      length (consts t₁) + length (consts t₂) + length (consts t₃)
    ≤⟨ +-mono-≤ (+-mono-≤ (lem-333 t₁) (lem-333 t₂)) (lem-333 t₃) ⟩
      size t₁ + size t₂ + size t₃
    ∎)
  where
    open ≤-Reasoning

-- 3.3.4. Theorem [Principles of induction on terms]

data Subterm : Term → Term → Set where
  subterm-succ   : ∀ {s₁} → Subterm s₁ (succ s₁)
  subterm-pred   : ∀ {s₁} → Subterm s₁ (pred s₁)
  subterm-iszero : ∀ {s₁} → Subterm s₁ (iszero s₁)
  subterm-if     : ∀ {s₁ s₂ s₃} → Subterm s₁ (if s₁ then s₂ else s₃)
  subterm-then   : ∀ {s₁ s₂ s₃} → Subterm s₂ (if s₁ then s₂ else s₃)
  subterm-else   : ∀ {s₁ s₂ s₃} → Subterm s₃ (if s₁ then s₂ else s₃)

ind-struct : ∀ (P : Term → Set) → (∀ {s} → (∀ {r} → Subterm r s → P r) → P s) → (∀ s → P s)
ind-struct P f true                    = f λ ()
ind-struct P f false                   = f λ ()
ind-struct P f zero                    = f λ ()
ind-struct P f (succ s₁)               = f λ { subterm-succ   → ind-struct P f s₁ }
ind-struct P f (pred s₁)               = f λ { subterm-pred   → ind-struct P f s₁ }
ind-struct P f (iszero s₁)             = f λ { subterm-iszero → ind-struct P f s₁ }
ind-struct P f (if s₁ then s₂ else s₃) = f λ { subterm-if     → ind-struct P f s₁
                                             ; subterm-then   → ind-struct P f s₂
                                             ; subterm-else   → ind-struct P f s₃
                                             }

SmallerSize : Term → Term → Set
SmallerSize r s = size r < size s

postulate -- TODO: use stdlib
  ind-size : ∀ (P : Term → Set) → (∀ {s} → (∀ {r} → SmallerSize r s → P r) → P s) → (∀ s → P s)

SmallerDepth : Term → Term → Set
SmallerDepth r s = depth r < depth s

postulate -- TODO: use stdlib
  ind-depth : ∀ (P : Term → Set) → (∀ {s} → (∀ {r} → SmallerDepth r s → P r) → P s) → (∀ s → P s)
