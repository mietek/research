module Chapter3 where

open import Data.Nat using (_≤_ ; _<_ ; _+_ ; _⊔_ ; ℕ ; s≤s ; suc ; zero)
import Data.Nat.Properties as Nat
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_ ; _≢_ ; refl)
open import Relation.Binary using (DecSetoid ; Decidable)
open import Relation.Nullary using (¬_ ; Dec ; no ; yes)
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)

open import Prelude-UniqueList
open import Prelude-WellFounded


module _ where
  m≤m+n+o : ∀ m n o → m ≤ m + n + o
  m≤m+n+o m n o = Nat.≤-trans (Nat.m≤m+n m n) (Nat.m≤m+n (m + n) o)

  n≤m+n+o : ∀ m n o → n ≤ m + n + o
  n≤m+n+o m n o = Nat.≤-trans (Nat.n≤m+n m n) (Nat.m≤m+n (m + n) o)

  o≤m+n+o : ∀ m n o → o ≤ m + n + o
  o≤m+n+o m n o = Nat.n≤m+n (m + n) o

  m≤m⊔n⊔o : ∀ m n o → m ≤ m ⊔ n ⊔ o
  m≤m⊔n⊔o m n o = Nat.≤-trans (Nat.m≤m⊔n m n) (Nat.m≤m⊔n (m ⊔ n) o)

  n≤m⊔n⊔o : ∀ m n o → n ≤ m ⊔ n ⊔ o
  n≤m⊔n⊔o m n o = Nat.≤-trans (Nat.n≤m⊔n m n) (Nat.m≤m⊔n (m ⊔ n) o)

  o≤m⊔n⊔o : ∀ m n o → o ≤ m ⊔ n ⊔ o
  o≤m⊔n⊔o m n o = Nat.n≤m⊔n (m ⊔ n) o


-- 3. Untyped arithmetic expressions

-- 3.1. Introduction

-- 3.2. Syntax

-- 3.2.1. Definition [Terms, inductively]

data Term : Set where
  true false zero  : Term
  succ pred iszero : (t₁ : Term) → Term
  if_then_else     : (t₁ t₂ t₃ : Term) → Term

_≟_ : Decidable {A = Term} _≡_
true                  ≟ true                  = yes refl
true                  ≟ false                 = no λ ()
true                  ≟ zero                  = no λ ()
true                  ≟ succ s₁               = no λ ()
true                  ≟ pred s₁               = no λ ()
true                  ≟ iszero s₁             = no λ ()
true                  ≟ if s₁ then s₂ else s₃ = no λ ()
false                 ≟ true                  = no λ ()
false                 ≟ false                 = yes refl
false                 ≟ zero                  = no λ ()
false                 ≟ succ s₁               = no λ ()
false                 ≟ pred s₁               = no λ ()
false                 ≟ iszero s₁             = no λ ()
false                 ≟ if s₁ then s₂ else s₃ = no λ ()
zero                  ≟ true                  = no λ ()
zero                  ≟ false                 = no λ ()
zero                  ≟ zero                  = yes refl
zero                  ≟ succ s₁               = no λ ()
zero                  ≟ pred s₁               = no λ ()
zero                  ≟ iszero s₁             = no λ ()
zero                  ≟ if s₁ then s₂ else s₃ = no λ ()
succ r₁               ≟ true                  = no λ ()
succ r₁               ≟ false                 = no λ ()
succ r₁               ≟ zero                  = no λ ()
succ r₁               ≟ succ s₁               with r₁ ≟ s₁
... | yes refl = yes refl
... | no r₁≢s₁ = no λ { refl → refl ↯ r₁≢s₁ }
succ r₁               ≟ pred s₁               = no λ ()
succ r₁               ≟ iszero s₁             = no λ ()
succ r₁               ≟ if s₁ then s₂ else s₃ = no λ ()
pred r₁               ≟ true                  = no λ ()
pred r₁               ≟ false                 = no λ ()
pred r₁               ≟ zero                  = no λ ()
pred r₁               ≟ succ s₁               = no λ ()
pred r₁               ≟ pred s₁               with r₁ ≟ s₁
... | yes refl = yes refl
... | no r₁≢s₁ = no λ { refl → refl ↯ r₁≢s₁ }
pred r₁               ≟ iszero s₁             = no λ ()
pred r₁               ≟ if s₁ then s₂ else s₃ = no λ ()
iszero r₁             ≟ true                  = no λ ()
iszero r₁             ≟ false                 = no λ ()
iszero r₁             ≟ zero                  = no λ ()
iszero r₁             ≟ succ s₁               = no λ ()
iszero r₁             ≟ pred s₁               = no λ ()
iszero r₁             ≟ iszero s₁             with r₁ ≟ s₁
... | yes refl = yes refl
... | no r₁≢s₁ = no λ { refl → refl ↯ r₁≢s₁ }
iszero r₁             ≟ if s₁ then s₂ else s₃ = no λ ()
if r₁ then r₂ else r₃ ≟ true                  = no λ ()
if r₁ then r₂ else r₃ ≟ false                 = no λ ()
if r₁ then r₂ else r₃ ≟ zero                  = no λ ()
if r₁ then r₂ else r₃ ≟ succ s₁               = no λ ()
if r₁ then r₂ else r₃ ≟ pred s₁               = no λ ()
if r₁ then r₂ else r₃ ≟ iszero s₁             = no λ ()
if r₁ then r₂ else r₃ ≟ if s₁ then s₂ else s₃ with r₁ ≟ s₁ | r₂ ≟ s₂ | r₃ ≟ s₃
... | yes refl | yes refl | yes refl = yes refl
... | no r₁≢s₁ | _        | _        = no λ { refl → refl ↯ r₁≢s₁ }
... | _        | no r₂≢s₂ | _        = no λ { refl → refl ↯ r₂≢s₂ }
... | _        | _        | no r₃≢s₃ = no λ { refl → refl ↯ r₃≢s₃ }

Term-decSetoid : DecSetoid _ _
Term-decSetoid = record
  { Carrier = Term
  ; _≈_     = _≡_
  ; isDecEquivalence = record
    { isEquivalence = PropEq.isEquivalence
    ; _≟_           = _≟_
    }
  }

open module UniqueList-Term = MakeUniqueList (Term-decSetoid)

-- 3.2.2. Definition [Terms, by inference rules] (redundant)

-- 3.2.3. Definition [Terms, concretely] (redundant)

-- 3.2.4. Exercise (skipped)

-- 3.2.5. Exercise (skipped)

-- 3.2.6. Proposition (skipped)


-- 3.3. Induction on terms

-- 3.3.1. Definition

consts : Term → UniqueList
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
size (if t₁ then t₂ else t₃) = 1 + (size t₁ + size t₂ + size t₃)

depth : Term → ℕ
depth true                    = 1
depth false                   = 1
depth zero                    = 1
depth (succ t₁)               = 1 + depth t₁
depth (pred t₁)               = 1 + depth t₁
depth (iszero t₁)             = 1 + depth t₁
depth (if t₁ then t₂ else t₃) = 1 + (depth t₁ ⊔ depth t₂ ⊔ depth t₃)


-- 3.3.3. Lemma

module Lemma333-Direct where
  open Nat.≤-Reasoning

  lem : ∀ s → length (consts s) ≤ size s
  lem true                    = Nat.≤-refl
  lem false                   = Nat.≤-refl
  lem zero                    = Nat.≤-refl
  lem (succ s₁)               = Nat.≤-step (lem s₁)
  lem (pred s₁)               = Nat.≤-step (lem s₁)
  lem (iszero s₁)             = Nat.≤-step (lem s₁)
  lem (if s₁ then s₂ else s₃) = Nat.≤-step
    (begin
      length (consts s₁ ∪ consts s₂ ∪ consts s₃)
    ≤⟨ length-triangular (consts s₁ ∪ consts s₂) (consts s₃) ⟩
      length (consts s₁ ∪ consts s₂) + length (consts s₃)
    ≤⟨ Nat.+-monoˡ-≤ (length (consts s₃)) (length-triangular (consts s₁) (consts s₂)) ⟩
      length (consts s₁) + length (consts s₂) + length (consts s₃)
    ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (lem s₁) (lem s₂)) (lem s₃) ⟩
      size s₁ + size s₂ + size s₃
    ∎)


-- 3.3.4. Theorem [Principles of induction on terms]

-- Structural induction

data Subterm : Term → Term → Set where
  subterm-succ   : ∀ {s₁} → Subterm s₁ (succ s₁)
  subterm-pred   : ∀ {s₁} → Subterm s₁ (pred s₁)
  subterm-iszero : ∀ {s₁} → Subterm s₁ (iszero s₁)
  subterm-ifte₁  : ∀ {s₁ s₂ s₃} → Subterm s₁ (if s₁ then s₂ else s₃)
  subterm-ifte₂  : ∀ {s₁ s₂ s₃} → Subterm s₂ (if s₁ then s₂ else s₃)
  subterm-ifte₃  : ∀ {s₁ s₂ s₃} → Subterm s₃ (if s₁ then s₂ else s₃)

-- Verbose
module SubtermInd-Direct where
  subterm-ind : ∀ {ℓ} {P : Term → Set ℓ} → BuildsUp Subterm P → ∀ s → P s
  subterm-ind h s@true                 = h s λ r ()
  subterm-ind h s@false                = h s λ r ()
  subterm-ind h s@zero                 = h s λ r ()
  subterm-ind h s@(succ _)             = h s λ { r subterm-succ → subterm-ind h r }
  subterm-ind h s@(pred _)             = h s λ { r subterm-pred → subterm-ind h r }
  subterm-ind h s@(iszero _)           = h s λ { r subterm-iszero → subterm-ind h r }
  subterm-ind h s@(if _ then _ else _) = h s λ
    { r subterm-ifte₁ → subterm-ind h r
    ; r subterm-ifte₂ → subterm-ind h r
    ; r subterm-ifte₃ → subterm-ind h r
    }

-- Awkward
module SubtermInd-Stdlib where
  import Induction.WellFounded as Stdlib

  subterm-wf : Stdlib.WellFounded Subterm
  subterm-wf s = Stdlib.acc λ
    { s₁ subterm-succ   → subterm-wf s₁
    ; s₁ subterm-pred   → subterm-wf s₁
    ; s₁ subterm-iszero → subterm-wf s₁
    ; s₁ subterm-ifte₁  → subterm-wf s₁
    ; s₂ subterm-ifte₂  → subterm-wf s₂
    ; s₃ subterm-ifte₃  → subterm-wf s₃
    }

  open module SubtermInd {ℓ} = Stdlib.All subterm-wf ℓ using (wfRec)

  subterm-ind : ∀ {ℓ} {P : Term → Set ℓ} → Induction Subterm P
  subterm-ind {P = P} = wfRec P

-- Preferred
module _ where
  subterm-wf : WellFounded Subterm
  subterm-wf s = access s λ
    { s₁ subterm-succ   → subterm-wf s₁
    ; s₁ subterm-pred   → subterm-wf s₁
    ; s₁ subterm-iszero → subterm-wf s₁
    ; s₁ subterm-ifte₁  → subterm-wf s₁
    ; s₂ subterm-ifte₂  → subterm-wf s₂
    ; s₃ subterm-ifte₃  → subterm-wf s₃
    }

  subterm-ind : ∀ {ℓ} {P : Term → Set ℓ} → Induction Subterm P
  subterm-ind = ind subterm-wf


-- Induction on size

Subsize : Term → Term → Set
Subsize r s = size r < size s

subsize-wf : WellFounded Subsize
subsize-wf = InverseImage.wellFounded size <-wf

subsize-ind : ∀ {ℓ} {P : Term → Set ℓ} → Induction Subsize P
subsize-ind = ind subsize-wf


-- Induction on depth

Subdepth : Term → Term → Set
Subdepth r s = depth r < depth s

subdepth-wf : WellFounded Subdepth
subdepth-wf = InverseImage.wellFounded depth <-wf

subdepth-ind : ∀ {ℓ} {P : Term → Set ℓ} → Induction Subdepth P
subdepth-ind = ind subdepth-wf


module Lemma333-ViaSubtermInd where
  open Nat.≤-Reasoning

  lem-via-subterm-ind : ∀ s → length (consts s) ≤ size s
  lem-via-subterm-ind = subterm-ind λ
    { true                    h → Nat.≤-refl
    ; false                   h → Nat.≤-refl
    ; zero                    h → Nat.≤-refl
    ; (succ s₁)               h → Nat.≤-step (h s₁ subterm-succ)
    ; (pred s₁)               h → Nat.≤-step (h s₁ subterm-pred)
    ; (iszero s₁)             h → Nat.≤-step (h s₁ subterm-iszero)
    ; (if s₁ then s₂ else s₃) h →
      let
        h₁ = h s₁ subterm-ifte₁
        h₂ = h s₂ subterm-ifte₂
        h₃ = h s₃ subterm-ifte₃
      in
        Nat.≤-step (begin
          length (consts s₁ ∪ consts s₂ ∪ consts s₃)
        ≤⟨ length-triangular (consts s₁ ∪ consts s₂) (consts s₃) ⟩
          length (consts s₁ ∪ consts s₂) + length (consts s₃)
        ≤⟨ Nat.+-monoˡ-≤ (length (consts s₃)) (length-triangular (consts s₁) (consts s₂)) ⟩
          length (consts s₁) + length (consts s₂) + length (consts s₃)
        ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ h₁ h₂) h₃ ⟩
          size s₁ + size s₂ + size s₃
        ∎)
    }


module Lemma333-ViaSubsizeInd where
  open Nat.≤-Reasoning

  subsize-ifte₁ : ∀ s₁ s₂ s₃ → Subsize s₁ (if s₁ then s₂ else s₃)
  subsize-ifte₁ s₁ s₂ s₃ = s≤s (m≤m+n+o (size s₁) (size s₂) (size s₃))

  subsize-ifte₂ : ∀ s₁ s₂ s₃ → Subsize s₂ (if s₁ then s₂ else s₃)
  subsize-ifte₂ s₁ s₂ s₃ = s≤s (n≤m+n+o (size s₁) (size s₂) (size s₃))

  subsize-ifte₃ : ∀ s₁ s₂ s₃ → Subsize s₃ (if s₁ then s₂ else s₃)
  subsize-ifte₃ s₁ s₂ s₃ = s≤s (o≤m+n+o (size s₁) (size s₂) (size s₃))

  lem-via-subsize-ind : ∀ s → length (consts s) ≤ size s
  lem-via-subsize-ind = subsize-ind λ
    { true                    h → Nat.≤-refl
    ; false                   h → Nat.≤-refl
    ; zero                    h → Nat.≤-refl
    ; (succ s₁)               h → Nat.≤-step (h s₁ Nat.≤-refl)
    ; (pred s₁)               h → Nat.≤-step (h s₁ Nat.≤-refl)
    ; (iszero s₁)             h → Nat.≤-step (h s₁ Nat.≤-refl)
    ; (if s₁ then s₂ else s₃) h →
      let
        h₁ = h s₁ (subsize-ifte₁ s₁ s₂ s₃)
        h₂ = h s₂ (subsize-ifte₂ s₁ s₂ s₃)
        h₃ = h s₃ (subsize-ifte₃ s₁ s₂ s₃)
      in
        Nat.≤-step (begin
          length (consts s₁ ∪ consts s₂ ∪ consts s₃)
        ≤⟨ length-triangular (consts s₁ ∪ consts s₂) (consts s₃) ⟩
          length (consts s₁ ∪ consts s₂) + length (consts s₃)
        ≤⟨ Nat.+-monoˡ-≤ (length (consts s₃)) (length-triangular (consts s₁) (consts s₂)) ⟩
          length (consts s₁) + length (consts s₂) + length (consts s₃)
        ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ h₁ h₂) h₃ ⟩
          size s₁ + size s₂ + size s₃
        ∎)
    }


module Lemma333-ViaSubdepthInd where
  open Nat.≤-Reasoning

  subdepth-ifte₁ : ∀ s₁ s₂ s₃ → Subdepth s₁ (if s₁ then s₂ else s₃)
  subdepth-ifte₁ s₁ s₂ s₃ = s≤s (m≤m⊔n⊔o (depth s₁) (depth s₂) (depth s₃))

  subdepth-ifte₂ : ∀ s₁ s₂ s₃ → Subdepth s₂ (if s₁ then s₂ else s₃)
  subdepth-ifte₂ s₁ s₂ s₃ = s≤s (n≤m⊔n⊔o (depth s₁) (depth s₂) (depth s₃))

  subdepth-ifte₃ : ∀ s₁ s₂ s₃ → Subdepth s₃ (if s₁ then s₂ else s₃)
  subdepth-ifte₃ s₁ s₂ s₃ = s≤s (o≤m⊔n⊔o (depth s₁) (depth s₂) (depth s₃))

  lem-via-subdepth-ind : ∀ s → length (consts s) ≤ size s
  lem-via-subdepth-ind = subdepth-ind λ
    { true                    h → Nat.≤-refl
    ; false                   h → Nat.≤-refl
    ; zero                    h → Nat.≤-refl
    ; (succ s₁)               h → Nat.≤-step (h s₁ Nat.≤-refl)
    ; (pred s₁)               h → Nat.≤-step (h s₁ Nat.≤-refl)
    ; (iszero s₁)             h → Nat.≤-step (h s₁ Nat.≤-refl)
    ; (if s₁ then s₂ else s₃) h →
      let
        h₁ = h s₁ (subdepth-ifte₁ s₁ s₂ s₃)
        h₂ = h s₂ (subdepth-ifte₂ s₁ s₂ s₃)
        h₃ = h s₃ (subdepth-ifte₃ s₁ s₂ s₃)
      in
        Nat.≤-step (begin
          length (consts s₁ ∪ consts s₂ ∪ consts s₃)
        ≤⟨ length-triangular (consts s₁ ∪ consts s₂) (consts s₃) ⟩
          length (consts s₁ ∪ consts s₂) + length (consts s₃)
        ≤⟨ Nat.+-monoˡ-≤ (length (consts s₃)) (length-triangular (consts s₁) (consts s₂)) ⟩
          length (consts s₁) + length (consts s₂) + length (consts s₃)
        ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ h₁ h₂) h₃ ⟩
          size s₁ + size s₂ + size s₃
        ∎)
    }
