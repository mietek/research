module Chapter3 where

open import Data.Bool
open import Data.List using (List ; [] ; _∷_ ; [_] ; _++_ ; length)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _≤_ ;  _<_ ; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)


-- 3 Untyped Arithmetic Expressions

-- 3.1 Introduction

-- 3.2 Syntax

-- 3.2.1 Definition [Terms, inductively]

data Term : Set where
  true false zero  : Term
  succ pred iszero : (t₁ : Term) → Term
  if_then_else     : (t₁ t₂ t₃ : Term) → Term

-- 3.2.2 Definition [Terms, by inference rules] (redundant)

-- 3.2.3 Definition [Terms, concretely] (redundant)

-- 3.2.4 Exercise (skipped)

-- 3.2.5 Exercise (skipped)

-- 3.2.6 Proposition (skipped)

-- 3.3 Induction on Terms

-- 3.3.1 Definition

consts : Term → List Term
consts true                    = [ true ]
consts false                   = [ false ]
consts zero                    = [ zero ]
consts (succ t₁)               = consts t₁
consts (pred t₁)               = consts t₁
consts (iszero t₁)             = consts t₁
consts (if t₁ then t₂ else t₃) = consts t₁ ++ consts t₂ ++ consts t₃

-- 3.3.2 Definition

size : Term → ℕ
size true                    = 1
size false                   = 1
size zero                    = 1
size (succ t₁)               = size t₁ + 1
size (pred t₁)               = size t₁ + 1
size (iszero t₁)             = size t₁ + 1
size (if t₁ then t₂ else t₃) = size t₁ + size t₂ + size t₃ + 1

depth : Term → ℕ
depth true                    = 1
depth false                   = 1
depth zero                    = 1
depth (succ t₁)               = depth t₁ + 1
depth (pred t₁)               = depth t₁ + 1
depth (iszero t₁)             = depth t₁ + 1
depth (if t₁ then t₂ else t₃) = depth t₁ ⊔ depth t₂ ⊔ depth t₃ + 1

-- 3.3.3 Lemma

postulate
  lemma-3-3-3 : ∀ {t : Term} → length (consts t) ≤ size t

-- 3.3.4 Theorem [Principles of induction on terms]

data _IsImmediateSubterm_ : Term → Term → Set where
  of-succ   : ∀ {s₁ : Term} → s₁ IsImmediateSubterm succ s₁
  of-pred   : ∀ {s₁ : Term} → s₁ IsImmediateSubterm pred s₁
  of-iszero : ∀ {s₁ : Term} → s₁ IsImmediateSubterm iszero s₁
  of-if     : ∀ {s₁ s₂ s₃ : Term} → s₁ IsImmediateSubterm if s₁ then s₂ else s₃
  of-then   : ∀ {s₁ s₂ s₃ : Term} → s₂ IsImmediateSubterm if s₁ then s₂ else s₃
  of-else   : ∀ {s₁ s₂ s₃ : Term} → s₃ IsImmediateSubterm if s₁ then s₂ else s₃

ind-struct : ∀ (P : Term → Set) → (∀ {s : Term} → (∀ {r : Term} → r IsImmediateSubterm s → P r) → P s) → (s : Term) → P s
ind-struct P f true                    = f λ ()
ind-struct P f false                   = f λ ()
ind-struct P f zero                    = f λ ()
ind-struct P f (succ s₁)               = f λ { of-succ   → ind-struct P f s₁ }
ind-struct P f (pred s₁)               = f λ { of-pred   → ind-struct P f s₁ }
ind-struct P f (iszero s₁)             = f λ { of-iszero → ind-struct P f s₁ }
ind-struct P f (if s₁ then s₂ else s₃) = f λ { of-if     → ind-struct P f s₁ ;
                                               of-then   → ind-struct P f s₂ ;
                                               of-else   → ind-struct P f s₃ }

ind-depth : ∀ (P : Term → Set) → (∀ (s : Term) → (∀ (r : Term) → {!depth r < depth s!} → P r) → P s) → (s : Term) → P s
ind-depth P f true                    = {!!}
ind-depth P f false                   = {!!}
ind-depth P f zero                    = {!!}
ind-depth P f (succ s₁)               = {!!}
ind-depth P f (pred s₁)               = {!!}
ind-depth P f (iszero s₁)             = {!!}
ind-depth P f (if s₁ then s₂ else s₃) = {!!}

ind-size : ∀ (P : Term → Set) → (∀ (s : Term) → (∀ (r : Term) → {!size r < size s!} → P r) → P s) → (s : Term) → P s
ind-size P f true                    = {!!}
ind-size P f false                   = {!!}
ind-size P f zero                    = {!!}
ind-size P f (succ s₁)               = {!!}
ind-size P f (pred s₁)               = {!!}
ind-size P f (iszero s₁)             = {!!}
ind-size P f (if s₁ then s₂ else s₃) = {!!}
