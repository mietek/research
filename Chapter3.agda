module Chapter3 where

open import Data.Nat using (_≤_ ; _<_ ; _+_ ; _⊔_ ; ℕ ; s≤s ; suc ; zero)
open import Data.Product using (_×_ ; _,_ ; Σ ; ∃ ; proj₁ ; proj₂)
import Data.Nat.Properties as Nat
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_ ; _≢_ ; refl ; subst) renaming (cong to _&_ ; sym to _⁻¹)
open import Relation.Binary using (DecSetoid ; Decidable)
open import Relation.Nullary using (¬_ ; Dec ; no ; yes)
open import Relation.Nullary.Negation using (contraposition) renaming (contradiction to _↯_)

open import Prelude-UniqueList
open import Prelude-WellFounded


module _ where
  infixl 8 _⊗_
  _⊗_ : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} {x y : A} → f ≡ g → x ≡ y → f x ≡ g y
  refl ⊗ refl = refl

  coerce : ∀ {ℓ} {A B : Set ℓ} → A → A ≡ B → B
  coerce x refl = x


-- 3. Untyped arithmetic expressions

-- 3.1. Introduction

-- 3.2. Syntax

-- 3.2.1. Definition [Terms, inductively]

data Term : Set where
  true false zero : Term
  suc pred isZero : (t₁ : Term) → Term
  if_then_else    : (t₁ t₂ t₃ : Term) → Term


-- 3.2.2. Definition [Terms, by inference rules] (redundant)

-- 3.2.3. Definition [Terms, concretely] (redundant)

-- 3.2.4. Exercise (skipped)

-- 3.2.5. Exercise (skipped)

-- 3.2.6. Proposition (skipped)

-- 3.3. Induction on terms

-- 3.3.1. Definition

module _ where
  _≟_ : Decidable {A = Term} _≡_
  true                  ≟ true                  = yes refl
  true                  ≟ false                 = no λ ()
  true                  ≟ zero                  = no λ ()
  true                  ≟ suc s₁                = no λ ()
  true                  ≟ pred s₁               = no λ ()
  true                  ≟ isZero s₁             = no λ ()
  true                  ≟ if s₁ then s₂ else s₃ = no λ ()
  false                 ≟ true                  = no λ ()
  false                 ≟ false                 = yes refl
  false                 ≟ zero                  = no λ ()
  false                 ≟ suc s₁                = no λ ()
  false                 ≟ pred s₁               = no λ ()
  false                 ≟ isZero s₁             = no λ ()
  false                 ≟ if s₁ then s₂ else s₃ = no λ ()
  zero                  ≟ true                  = no λ ()
  zero                  ≟ false                 = no λ ()
  zero                  ≟ zero                  = yes refl
  zero                  ≟ suc s₁                = no λ ()
  zero                  ≟ pred s₁               = no λ ()
  zero                  ≟ isZero s₁             = no λ ()
  zero                  ≟ if s₁ then s₂ else s₃ = no λ ()
  suc r₁                ≟ true                  = no λ ()
  suc r₁                ≟ false                 = no λ ()
  suc r₁                ≟ zero                  = no λ ()
  suc r₁                ≟ suc s₁                with r₁ ≟ s₁
  ... | yes refl = yes refl
  ... | no r₁≢s₁ = no λ { refl → refl ↯ r₁≢s₁ }
  suc r₁                ≟ pred s₁               = no λ ()
  suc r₁                ≟ isZero s₁             = no λ ()
  suc r₁                ≟ if s₁ then s₂ else s₃ = no λ ()
  pred r₁               ≟ true                  = no λ ()
  pred r₁               ≟ false                 = no λ ()
  pred r₁               ≟ zero                  = no λ ()
  pred r₁               ≟ suc s₁                = no λ ()
  pred r₁               ≟ pred s₁               with r₁ ≟ s₁
  ... | yes refl = yes refl
  ... | no r₁≢s₁ = no λ { refl → refl ↯ r₁≢s₁ }
  pred r₁               ≟ isZero s₁             = no λ ()
  pred r₁               ≟ if s₁ then s₂ else s₃ = no λ ()
  isZero r₁             ≟ true                  = no λ ()
  isZero r₁             ≟ false                 = no λ ()
  isZero r₁             ≟ zero                  = no λ ()
  isZero r₁             ≟ suc s₁                = no λ ()
  isZero r₁             ≟ pred s₁               = no λ ()
  isZero r₁             ≟ isZero s₁             with r₁ ≟ s₁
  ... | yes refl = yes refl
  ... | no r₁≢s₁ = no λ { refl → refl ↯ r₁≢s₁ }
  isZero r₁             ≟ if s₁ then s₂ else s₃ = no λ ()
  if r₁ then r₂ else r₃ ≟ true                  = no λ ()
  if r₁ then r₂ else r₃ ≟ false                 = no λ ()
  if r₁ then r₂ else r₃ ≟ zero                  = no λ ()
  if r₁ then r₂ else r₃ ≟ suc s₁                = no λ ()
  if r₁ then r₂ else r₃ ≟ pred s₁               = no λ ()
  if r₁ then r₂ else r₃ ≟ isZero s₁             = no λ ()
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

  open module UniqueList-Term = MakeUniqueList (Term-decSetoid) public

consts : Term → UniqueList
consts true                    = [ true ]
consts false                   = [ false ]
consts zero                    = [ zero ]
consts (suc t₁)                = consts t₁
consts (pred t₁)               = consts t₁
consts (isZero t₁)             = consts t₁
consts (if t₁ then t₂ else t₃) = consts t₁ ∪ consts t₂ ∪ consts t₃


-- 3.3.2. Definition

size : Term → ℕ
size true                    = 1
size false                   = 1
size zero                    = 1
size (suc t₁)                = 1 + size t₁
size (pred t₁)               = 1 + size t₁
size (isZero t₁)             = 1 + size t₁
size (if t₁ then t₂ else t₃) = 1 + (size t₁ + size t₂ + size t₃)

depth : Term → ℕ
depth true                    = 1
depth false                   = 1
depth zero                    = 1
depth (suc t₁)                = 1 + depth t₁
depth (pred t₁)               = 1 + depth t₁
depth (isZero t₁)             = 1 + depth t₁
depth (if t₁ then t₂ else t₃) = 1 + (depth t₁ ⊔ depth t₂ ⊔ depth t₃)


-- 3.3.3. Lemma

module Lemma333-Direct where
  open Nat.≤-Reasoning

  lem333 : ∀ s → length (consts s) ≤ size s
  lem333 true                    = Nat.≤-refl
  lem333 false                   = Nat.≤-refl
  lem333 zero                    = Nat.≤-refl
  lem333 (suc s₁)                = Nat.≤-step (lem333 s₁)
  lem333 (pred s₁)               = Nat.≤-step (lem333 s₁)
  lem333 (isZero s₁)             = Nat.≤-step (lem333 s₁)
  lem333 (if s₁ then s₂ else s₃) = Nat.≤-step
    (begin
      length (consts s₁ ∪ consts s₂ ∪ consts s₃)
    ≤⟨ length-triangular (consts s₁ ∪ consts s₂) (consts s₃) ⟩
      length (consts s₁ ∪ consts s₂) + length (consts s₃)
    ≤⟨ Nat.+-monoˡ-≤ (length (consts s₃)) (length-triangular (consts s₁) (consts s₂)) ⟩
      length (consts s₁) + length (consts s₂) + length (consts s₃)
    ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (lem333 s₁) (lem333 s₂)) (lem333 s₃) ⟩
      size s₁ + size s₂ + size s₃
    ∎)


-- 3.3.4. Theorem [Principles of induction on terms]

-- 3.3.4.1. Structural induction

data Subterm : Term → Term → Set where
  subterm-suc    : ∀ {s₁} → Subterm s₁ (suc s₁)
  subterm-pred   : ∀ {s₁} → Subterm s₁ (pred s₁)
  subterm-isZero : ∀ {s₁} → Subterm s₁ (isZero s₁)
  subterm-ifte₁  : ∀ {s₁ s₂ s₃} → Subterm s₁ (if s₁ then s₂ else s₃)
  subterm-ifte₂  : ∀ {s₁ s₂ s₃} → Subterm s₂ (if s₁ then s₂ else s₃)
  subterm-ifte₃  : ∀ {s₁ s₂ s₃} → Subterm s₃ (if s₁ then s₂ else s₃)

module SubtermIP-Direct where
  subterm-ip : ∀ {ℓ} {P : Term → Set ℓ} → InductionPrinciple Subterm P
  subterm-ip h s@true                 = h s λ r ()
  subterm-ip h s@false                = h s λ r ()
  subterm-ip h s@zero                 = h s λ r ()
  subterm-ip h s@(suc _)              = h s λ { r subterm-suc → subterm-ip h r }
  subterm-ip h s@(pred _)             = h s λ { r subterm-pred → subterm-ip h r }
  subterm-ip h s@(isZero _)           = h s λ { r subterm-isZero → subterm-ip h r }
  subterm-ip h s@(if _ then _ else _) = h s λ
    { r subterm-ifte₁ → subterm-ip h r
    ; r subterm-ifte₂ → subterm-ip h r
    ; r subterm-ifte₃ → subterm-ip h r
    }

module SubtermIP-Stdlib where
  import Induction.WellFounded as Stdlib

  subterm-wf : Stdlib.WellFounded Subterm
  subterm-wf s = Stdlib.acc λ
    { s₁ subterm-suc    → subterm-wf s₁
    ; s₁ subterm-pred   → subterm-wf s₁
    ; s₁ subterm-isZero → subterm-wf s₁
    ; s₁ subterm-ifte₁  → subterm-wf s₁
    ; s₂ subterm-ifte₂  → subterm-wf s₂
    ; s₃ subterm-ifte₃  → subterm-wf s₃
    }

  open module SubtermIP {ℓ} = Stdlib.All subterm-wf ℓ using (wfRec)

  subterm-ip : ∀ {ℓ} {P : Term → Set ℓ} → InductionPrinciple Subterm P
  subterm-ip {P = P} = wfRec P

module _ where
  subterm-wf : WellFounded Subterm
  subterm-wf s = access s λ
    { s₁ subterm-suc    → subterm-wf s₁
    ; s₁ subterm-pred   → subterm-wf s₁
    ; s₁ subterm-isZero → subterm-wf s₁
    ; s₁ subterm-ifte₁  → subterm-wf s₁
    ; s₂ subterm-ifte₂  → subterm-wf s₂
    ; s₃ subterm-ifte₃  → subterm-wf s₃
    }

  subterm-ip : ∀ {ℓ} {P : Term → Set ℓ} → InductionPrinciple Subterm P
  subterm-ip = inductionPrinciple subterm-wf

module Lemma333-ViaSubterm where
  open Nat.≤-Reasoning

  lem333-viaSubterm : ∀ s → length (consts s) ≤ size s
  lem333-viaSubterm = subterm-ip λ
    { true                    h → Nat.≤-refl
    ; false                   h → Nat.≤-refl
    ; zero                    h → Nat.≤-refl
    ; (suc s₁)                h → Nat.≤-step (h s₁ subterm-suc)
    ; (pred s₁)               h → Nat.≤-step (h s₁ subterm-pred)
    ; (isZero s₁)             h → Nat.≤-step (h s₁ subterm-isZero)
    ; (if s₁ then s₂ else s₃) h →
        Nat.≤-step (begin
          length (consts s₁ ∪ consts s₂ ∪ consts s₃)
        ≤⟨ length-triangular (consts s₁ ∪ consts s₂) (consts s₃) ⟩
          length (consts s₁ ∪ consts s₂) + length (consts s₃)
        ≤⟨ Nat.+-monoˡ-≤ (length (consts s₃)) (length-triangular (consts s₁) (consts s₂)) ⟩
          length (consts s₁) + length (consts s₂) + length (consts s₃)
        ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (h s₁ subterm-ifte₁) (h s₂ subterm-ifte₂)) (h s₃ subterm-ifte₃) ⟩
          size s₁ + size s₂ + size s₃
        ∎)
    }


-- 3.3.4.2. Induction on size

Subsize : Term → Term → Set
Subsize r s = size r < size s

subsize-wf : WellFounded Subsize
subsize-wf = InverseImage.wellFounded size <-wf

subsize-ip : ∀ {ℓ} {P : Term → Set ℓ} → InductionPrinciple Subsize P
subsize-ip = inductionPrinciple subsize-wf

module Lemma333-ViaSubsize where
  open Nat.≤-Reasoning

  module _ where
    m≤m+n+o : ∀ m n o → m ≤ m + n + o
    m≤m+n+o m n o = Nat.≤-trans (Nat.m≤m+n m n) (Nat.m≤m+n (m + n) o)

    n≤m+n+o : ∀ m n o → n ≤ m + n + o
    n≤m+n+o m n o = Nat.≤-trans (Nat.n≤m+n m n) (Nat.m≤m+n (m + n) o)

    o≤m+n+o : ∀ m n o → o ≤ m + n + o
    o≤m+n+o m n o = Nat.n≤m+n (m + n) o

  subsize-ifte₁ : ∀ s₁ s₂ s₃ → Subsize s₁ (if s₁ then s₂ else s₃)
  subsize-ifte₁ s₁ s₂ s₃ = s≤s (m≤m+n+o (size s₁) (size s₂) (size s₃))

  subsize-ifte₂ : ∀ s₁ s₂ s₃ → Subsize s₂ (if s₁ then s₂ else s₃)
  subsize-ifte₂ s₁ s₂ s₃ = s≤s (n≤m+n+o (size s₁) (size s₂) (size s₃))

  subsize-ifte₃ : ∀ s₁ s₂ s₃ → Subsize s₃ (if s₁ then s₂ else s₃)
  subsize-ifte₃ s₁ s₂ s₃ = s≤s (o≤m+n+o (size s₁) (size s₂) (size s₃))

  lem333-viaSubsize : ∀ s → length (consts s) ≤ size s
  lem333-viaSubsize = subsize-ip λ
    { true                    h → Nat.≤-refl
    ; false                   h → Nat.≤-refl
    ; zero                    h → Nat.≤-refl
    ; (suc s₁)                h → Nat.≤-step (h s₁ Nat.≤-refl)
    ; (pred s₁)               h → Nat.≤-step (h s₁ Nat.≤-refl)
    ; (isZero s₁)             h → Nat.≤-step (h s₁ Nat.≤-refl)
    ; (if s₁ then s₂ else s₃) h →
        Nat.≤-step (begin
          length (consts s₁ ∪ consts s₂ ∪ consts s₃)
        ≤⟨ length-triangular (consts s₁ ∪ consts s₂) (consts s₃) ⟩
          length (consts s₁ ∪ consts s₂) + length (consts s₃)
        ≤⟨ Nat.+-monoˡ-≤ (length (consts s₃)) (length-triangular (consts s₁) (consts s₂)) ⟩
          length (consts s₁) + length (consts s₂) + length (consts s₃)
        ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (h s₁ (subsize-ifte₁ s₁ s₂ s₃)) (h s₂ (subsize-ifte₂ s₁ s₂ s₃))) (h s₃ (subsize-ifte₃ s₁ s₂ s₃)) ⟩
          size s₁ + size s₂ + size s₃
        ∎)
    }


-- 3.3.4.3. Induction on depth

Subdepth : Term → Term → Set
Subdepth r s = depth r < depth s

subdepth-wf : WellFounded Subdepth
subdepth-wf = InverseImage.wellFounded depth <-wf

subdepth-ip : ∀ {ℓ} {P : Term → Set ℓ} → InductionPrinciple Subdepth P
subdepth-ip = inductionPrinciple subdepth-wf

module Lemma333-ViaSubdepth where
  open Nat.≤-Reasoning

  module _ where
    m≤m⊔n⊔o : ∀ m n o → m ≤ m ⊔ n ⊔ o
    m≤m⊔n⊔o m n o = Nat.≤-trans (Nat.m≤m⊔n m n) (Nat.m≤m⊔n (m ⊔ n) o)

    n≤m⊔n⊔o : ∀ m n o → n ≤ m ⊔ n ⊔ o
    n≤m⊔n⊔o m n o = Nat.≤-trans (Nat.n≤m⊔n m n) (Nat.m≤m⊔n (m ⊔ n) o)

    o≤m⊔n⊔o : ∀ m n o → o ≤ m ⊔ n ⊔ o
    o≤m⊔n⊔o m n o = Nat.n≤m⊔n (m ⊔ n) o

  subdepth-ifte₁ : ∀ s₁ s₂ s₃ → Subdepth s₁ (if s₁ then s₂ else s₃)
  subdepth-ifte₁ s₁ s₂ s₃ = s≤s (m≤m⊔n⊔o (depth s₁) (depth s₂) (depth s₃))

  subdepth-ifte₂ : ∀ s₁ s₂ s₃ → Subdepth s₂ (if s₁ then s₂ else s₃)
  subdepth-ifte₂ s₁ s₂ s₃ = s≤s (n≤m⊔n⊔o (depth s₁) (depth s₂) (depth s₃))

  subdepth-ifte₃ : ∀ s₁ s₂ s₃ → Subdepth s₃ (if s₁ then s₂ else s₃)
  subdepth-ifte₃ s₁ s₂ s₃ = s≤s (o≤m⊔n⊔o (depth s₁) (depth s₂) (depth s₃))

  lem333-viaSubdepth : ∀ s → length (consts s) ≤ size s
  lem333-viaSubdepth = subdepth-ip λ
    { true                    h → Nat.≤-refl
    ; false                   h → Nat.≤-refl
    ; zero                    h → Nat.≤-refl
    ; (suc s₁)                h → Nat.≤-step (h s₁ Nat.≤-refl)
    ; (pred s₁)               h → Nat.≤-step (h s₁ Nat.≤-refl)
    ; (isZero s₁)             h → Nat.≤-step (h s₁ Nat.≤-refl)
    ; (if s₁ then s₂ else s₃) h →
        Nat.≤-step (begin
          length (consts s₁ ∪ consts s₂ ∪ consts s₃)
        ≤⟨ length-triangular (consts s₁ ∪ consts s₂) (consts s₃) ⟩
          length (consts s₁ ∪ consts s₂) + length (consts s₃)
        ≤⟨ Nat.+-monoˡ-≤ (length (consts s₃)) (length-triangular (consts s₁) (consts s₂)) ⟩
          length (consts s₁) + length (consts s₂) + length (consts s₃)
        ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (h s₁ (subdepth-ifte₁ s₁ s₂ s₃)) (h s₂ (subdepth-ifte₂ s₁ s₂ s₃))) (h s₃ (subdepth-ifte₃ s₁ s₂ s₃)) ⟩
          size s₁ + size s₂ + size s₃
        ∎)
    }


-- 3.4. Semantic styles

-- 3.5. Evaluation

-- 3.5.1. Definition (redundant)

-- 3.5.2. Definition (redundant)

-- 3.5.3. Definition

module _ where
  data Term⁻ : Set where
    true false   : Term⁻
    if_then_else : (t₁ t₂ t₃ : Term⁻) → Term⁻

  data Value⁻ : Term⁻ → Set where
    v-true  : Value⁻ true
    v-false : Value⁻ false

-- t ⟹⁻ t′ means that t reduces to t′ in one step
infix 3 _⟹⁻_
data _⟹⁻_ : Term⁻ → Term⁻ → Set where
  r-ifTrue  : ∀ {t₂ t₃} → if true then t₂ else t₃ ⟹⁻ t₂
  r-ifFalse : ∀ {t₂ t₃} → if false then t₂ else t₃ ⟹⁻ t₃
  r-if      : ∀ {t₁ t₁′ t₂ t₃} → t₁ ⟹⁻ t₁′ → if t₁ then t₂ else t₃ ⟹⁻ if t₁′ then t₂ else t₃


-- 3.5.4. Theorem [Determinacy of one-step evaluation]

module _ where
  NormalForm⁻ : Term⁻ → Set
  NormalForm⁻ t = ∀ {t′} → ¬ (t ⟹⁻ t′)

  v⇒nf⁻ : ∀ {u} → Value⁻ u → NormalForm⁻ u
  v⇒nf⁻ v-true  ()
  v⇒nf⁻ v-false ()

⟹-det⁻ : ∀ {t t′ t″} → t ⟹⁻ t′ → t ⟹⁻ t″ → t′ ≡ t″
⟹-det⁻ r-ifTrue  r-ifTrue  = refl
⟹-det⁻ r-ifTrue  (r-if r″) = r″ ↯ v⇒nf⁻ v-true
⟹-det⁻ r-ifFalse r-ifFalse = refl
⟹-det⁻ r-ifFalse (r-if r″) = r″ ↯ v⇒nf⁻ v-false
⟹-det⁻ (r-if r′) r-ifTrue  = r′ ↯ v⇒nf⁻ v-true
⟹-det⁻ (r-if r′) r-ifFalse = r′ ↯ v⇒nf⁻ v-false
⟹-det⁻ (r-if r′) (r-if r″) = (λ t₁′ → if t₁′ then _ else _) & ⟹-det⁻ r′ r″


-- 3.5.5. Exercise (skipped)

-- 3.5.6. Definition (given above)

-- 3.5.7. Definition (given above)

-- 3.5.8. Theorem

module _ where
  reduce⁻ : ∀ t → ¬ Value⁻ t → ∃ λ t′ → t ⟹⁻ t′
  reduce⁻ true                                         ¬v = v-true ↯ ¬v
  reduce⁻ false                                        ¬v = v-false ↯ ¬v
  reduce⁻ (if true then t₂ else t₃)                    ¬v = t₂ , r-ifTrue
  reduce⁻ (if false then t₂ else t₃)                   ¬v = t₃ , r-ifFalse
  reduce⁻ (if t₁@(if _ then _ else _) then t₂ else t₃) ¬v with reduce⁻ t₁ λ ()
  ... | t₁′ , r₁ = if t₁′ then t₂ else t₃ , r-if r₁

nf⇒v⁻ : ∀ {u} → NormalForm⁻ u → Value⁻ u
nf⇒v⁻ {true}                                     nf = v-true
nf⇒v⁻ {false}                                    nf = v-false
nf⇒v⁻ {if true then _ else _}                    nf = r-ifTrue ↯ nf
nf⇒v⁻ {if false then _ else _}                   nf = r-ifFalse ↯ nf
nf⇒v⁻ {if t₁@(if _ then _ else _) then _ else _} nf with reduce⁻ t₁ λ ()
... | t₁′ , r₁ = r-if r₁ ↯ nf


-- 3.5.9. Definition

-- t ⟹*⁻ t′ means that t reduces to t′ in some number of steps
infix 3 _⟹*⁻_
data _⟹*⁻_ : Term⁻ → Term⁻ → Set where
  done : ∀ {t} → t ⟹*⁻ t
  step : ∀ {t t′ t″} → t ⟹⁻ t′ → t′ ⟹*⁻ t″ → t ⟹*⁻ t″


-- 3.5.10. Exercise (redundant)

-- 3.5.11. Theorem [Uniqueness of normal forms]

module _ where
  undoStep⁻ : ∀ {t t′ u} → Value⁻ u → t ⟹⁻ t′ → t ⟹*⁻ u → t′ ⟹*⁻ u
  undoStep⁻ v r′ done        = r′ ↯ v⇒nf⁻ v
  undoStep⁻ v r′ (step r rs) with ⟹-det⁻ r′ r
  ... | refl = rs

⟹*-det⁻ : ∀ {t u u′} → Value⁻ u → Value⁻ u′ → t ⟹*⁻ u → t ⟹*⁻ u′ → u ≡ u′
⟹*-det⁻ v v′ done        done          = refl
⟹*-det⁻ v v′ done        (step r′ rs′) = r′ ↯ v⇒nf⁻ v
⟹*-det⁻ v v′ (step r rs) rs′           = ⟹*-det⁻ v v′ rs (undoStep⁻ v′ r rs′)


-- 3.5.12. Theorem [Termination of evaluation]

module _ where
  steps⁻ : ∀ {t t′ t″} → t ⟹*⁻ t′ → t′ ⟹*⁻ t″ → t ⟹*⁻ t″
  steps⁻ done          rs″ = rs″
  steps⁻ (step r′ rs′) rs″ = step r′ (steps⁻ rs′ rs″)

  rs-if⁻ : ∀ {t₁ t₁′ t₂ t₃} → t₁ ⟹*⁻ t₁′ → if t₁ then t₂ else t₃ ⟹*⁻ if t₁′ then t₂ else t₃
  rs-if⁻ done        = done
  rs-if⁻ (step r rs) = step (r-if r) (rs-if⁻ rs)

  rs-ifTrue⁻ : ∀ {t₁ t₂ t₂′ t₃} → t₁ ⟹*⁻ true → t₂ ⟹*⁻ t₂′ → if t₁ then t₂ else t₃ ⟹*⁻ t₂′
  rs-ifTrue⁻ rs₁ rs₂ = steps⁻ (rs-if⁻ rs₁) (step r-ifTrue rs₂)

  rs-ifFalse⁻ : ∀ {t₁ t₂ t₃ t₃′} → t₁ ⟹*⁻ false → t₃ ⟹*⁻ t₃′ → if t₁ then t₂ else t₃ ⟹*⁻ t₃′
  rs-ifFalse⁻ rs₁ rs₃ = steps⁻ (rs-if⁻ rs₁) (step r-ifFalse rs₃)

  -- t ⇓⁻ u means that t evaluates to u
  infix 3 _⇓⁻_
  _⇓⁻_ : Term⁻ → Term⁻ → Set
  t ⇓⁻ u = Value⁻ u × t ⟹*⁻ u

  eval-ifTrue⁻ : ∀ {t₁ t₂ t₃ u₂} → t₁ ⟹*⁻ true → t₂ ⇓⁻ u₂ → if t₁ then t₂ else t₃ ⇓⁻ u₂
  eval-ifTrue⁻ rs₁ (v₂ , rs₂) = v₂ , rs-ifTrue⁻ rs₁ rs₂

  eval-ifFalse⁻ : ∀ {t₁ t₂ t₃ u₃} → t₁ ⟹*⁻ false → t₃ ⇓⁻ u₃ → if t₁ then t₂ else t₃ ⇓⁻ u₃
  eval-ifFalse⁻ rs₁ (v₃ , rs₃) = v₃ , rs-ifFalse⁻ rs₁ rs₃

  -- t ⇓⁻ means that the evaluation of t terminates
  _⇓⁻ : Term⁻ → Set
  t ⇓⁻ = ∃ λ u → t ⇓⁻ u

  halt-ifTrue⁻ : ∀ {t₁ t₂ t₃} → t₁ ⟹*⁻ true → t₂ ⇓⁻ → if t₁ then t₂ else t₃ ⇓⁻
  halt-ifTrue⁻ rs₁ (u₂ , e₂) = u₂ , eval-ifTrue⁻ rs₁ e₂

  halt-ifFalse⁻ : ∀ {t₁ t₂ t₃} → t₁ ⟹*⁻ false → t₃ ⇓⁻ → if t₁ then t₂ else t₃ ⇓⁻
  halt-ifFalse⁻ rs₁ (u₃ , e₃) = u₃ , eval-ifFalse⁻ rs₁ e₃

  halt-if⁻ : ∀ {t₁ t₂ t₃} → t₁ ⇓⁻ → t₂ ⇓⁻ → t₃ ⇓⁻ → if t₁ then t₂ else t₃ ⇓⁻
  halt-if⁻ (true                  , v-true  , rs₁) h₂ h₃ = halt-ifTrue⁻ rs₁ h₂
  halt-if⁻ (false                 , v-false , rs₁) h₂ h₃ = halt-ifFalse⁻ rs₁ h₃
  halt-if⁻ (if u₁ then u₂ else u₃ , ()      , rs₁) h₂ h₃

halt⁻ : ∀ t → t ⇓⁻
halt⁻ true                    = true  , v-true  , done
halt⁻ false                   = false , v-false , done
halt⁻ (if t₁ then t₂ else t₃) = halt-if⁻ (halt⁻ t₁) (halt⁻ t₂) (halt⁻ t₃)


-- 3.5.13. Exercise (skipped)

-- 3.5.14. Exercise

module _ where
  data NumericValue : Term → Set where
    nv-zero : NumericValue zero
    nv-suc  : ∀ {u} → NumericValue u → NumericValue (suc u)

  data Value : Term → Set where
    v-true  : Value true
    v-false : Value false
    v-nv    : ∀ {u} → NumericValue u → Value u

  -- t ⟹ t′ means that t reduces to t′ in one step
  infix 3 _⟹_
  data _⟹_ : Term → Term → Set where
    r-ifTrue     : ∀ {t₂ t₃} → if true then t₂ else t₃ ⟹ t₂
    r-ifFalse    : ∀ {t₂ t₃} → if false then t₂ else t₃ ⟹ t₃
    r-if         : ∀ {t₁ t₁′ t₂ t₃} → t₁ ⟹ t₁′ → if t₁ then t₂ else t₃ ⟹ if t₁′ then t₂ else t₃
    r-suc        : ∀ {t₁ t₁′} → t₁ ⟹ t₁′ → suc t₁ ⟹ suc t₁′
    r-predZero   : pred zero ⟹ zero
    r-predSuc    : ∀ {u} → NumericValue u → pred (suc u) ⟹ u
    r-pred       : ∀ {t₁ t₁′} → t₁ ⟹ t₁′ → pred t₁ ⟹ pred t₁′
    r-isZeroZero : isZero zero ⟹ true
    r-isZeroSuc  : ∀ {u} → NumericValue u → isZero (suc u) ⟹ false
    r-isZero     : ∀ {t₁ t₁′} → t₁ ⟹ t₁′ → isZero t₁ ⟹ isZero t₁′

  NormalForm : Term → Set
  NormalForm t = ∀ {t′} → ¬ (t ⟹ t′)

  nv⇒nf : ∀ {u} → NumericValue u → NormalForm u
  nv⇒nf nv-zero     ()
  nv⇒nf (nv-suc nv) (r-suc r) = r ↯ nv⇒nf nv

  v⇒nf : ∀ {u} → Value u → NormalForm u
  v⇒nf v-true    ()
  v⇒nf v-false   ()
  v⇒nf (v-nv nv) = nv⇒nf nv

⟹-det : ∀ {t t′ t″} → t ⟹ t′ → t ⟹ t″ → t′ ≡ t″
⟹-det r-ifTrue          r-ifTrue          = refl
⟹-det r-ifTrue          (r-if r″)         = r″ ↯ v⇒nf v-true
⟹-det r-ifFalse         r-ifFalse         = refl
⟹-det r-ifFalse         (r-if r″)         = r″ ↯ v⇒nf v-false
⟹-det (r-if r′)         r-ifTrue          = r′ ↯ v⇒nf v-true
⟹-det (r-if r′)         r-ifFalse         = r′ ↯ v⇒nf v-false
⟹-det (r-if r′)         (r-if r″)         = (λ t₁′ → if t₁′ then _ else _) & ⟹-det r′ r″
⟹-det (r-suc r′)        (r-suc r″)        = suc & ⟹-det r′ r″
⟹-det r-predZero        r-predZero        = refl
⟹-det r-predZero        (r-pred r″)       = r″ ↯ nv⇒nf nv-zero
⟹-det (r-predSuc nv′)   (r-predSuc nv″)   = refl
⟹-det (r-predSuc nv′)   (r-pred r″)       = r″ ↯ nv⇒nf (nv-suc nv′)
⟹-det (r-pred r′)       r-predZero        = r′ ↯ nv⇒nf nv-zero
⟹-det (r-pred r′)       (r-predSuc nv″)   = r′ ↯ nv⇒nf (nv-suc nv″)
⟹-det (r-pred r′)       (r-pred r″)       = pred & ⟹-det r′ r″
⟹-det r-isZeroZero      r-isZeroZero      = refl
⟹-det r-isZeroZero      (r-isZero r″)     = r″ ↯ nv⇒nf nv-zero
⟹-det (r-isZeroSuc nv′) (r-isZeroSuc nv″) = refl
⟹-det (r-isZeroSuc nv′) (r-isZero r″)     = r″ ↯ nv⇒nf (nv-suc nv′)
⟹-det (r-isZero r′)     r-isZeroZero      = r′ ↯ nv⇒nf nv-zero
⟹-det (r-isZero r′)     (r-isZeroSuc nv″) = r′ ↯ nv⇒nf (nv-suc nv″)
⟹-det (r-isZero r′)     (r-isZero r″)     = isZero & ⟹-det r′ r″
