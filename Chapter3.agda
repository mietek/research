module Chapter3 where

open import Data.Nat using (_≤_ ; _<_ ; _+_ ; _⊔_ ; ℕ ; s≤s ; suc ; zero)
import Data.Nat.Properties as Nat
open import Data.Product using (_×_ ; _,_ ; Σ ; ∃ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
import Level
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_ ; _≢_ ; refl ; subst) renaming (cong to _&_ ; sym to _⁻¹)
import Relation.Binary as BinRel
open import Relation.Nullary using (¬_ ; Dec ; no ; yes)
open import Relation.Nullary.Negation using (contraposition) renaming (contradiction to _↯_)
import Relation.Unary as UnRel

open import Prelude-UniqueList
open import Prelude-WellFounded


module _ where
  infixl 8 _⊗_
  _⊗_ : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} {x y : A} → f ≡ g → x ≡ y → f x ≡ g y
  refl ⊗ refl = refl

  coerce : ∀ {ℓ} {A B : Set ℓ} → A → A ≡ B → B
  coerce x refl = x


module ReductionKit₁ {t ℓ} {Term : Set t} (_⟹_ : Term → Term → Set ℓ) where
  -- t ⟹* t′ means that t reduces to t′ in some number of steps
  infix 3 _⟹*_
  data _⟹*_ : Term → Term → Set (t Level.⊔ ℓ) where
    []  : ∀ {t} → t ⟹* t
    _∷_ : ∀ {t t′ t″} → t ⟹ t′ → t′ ⟹* t″ → t ⟹* t″

  NormalForm : Term → Set (t Level.⊔ ℓ)
  NormalForm t = ∀ {t′} → ¬ (t ⟹ t′)

  Reducible : Term → Set (t Level.⊔ ℓ)
  Reducible t = ∃ λ t′ → t ⟹ t′

  nf⇒¬ρ : ∀ {t} → NormalForm t → ¬ Reducible t
  nf⇒¬ρ nf (_ , r) = r ↯ nf

  ¬ρ⇒nf : ∀ {t} → ¬ Reducible t → NormalForm t
  ¬ρ⇒nf ¬ρ r = (_ , r) ↯ ¬ρ


module ReductionKit₂ {t ℓ} {Term : Set t} (_⟹_ : Term → Term → Set ℓ)
                                          (⟹-det : ∀ {t t′ t″} → t ⟹ t′ → t ⟹ t″ → t′ ≡ t″) where
  open ReductionKit₁ _⟹_

  chopHead : ∀ {t t′ u} → NormalForm u → t ⟹ t′ → t ⟹* u → t′ ⟹* u
  chopHead nf r []         = r ↯ nf
  chopHead nf r (r′ ∷ rs′) with ⟹-det r r′
  ... | refl               = rs′

  ⟹*-det : ∀ {t u u′} → NormalForm u → NormalForm u′ → t ⟹* u → t ⟹* u′ → u ≡ u′
  ⟹*-det nf nf′ []       []         = refl
  ⟹*-det nf nf′ []       (r′ ∷ rs′) = r′ ↯ nf
  ⟹*-det nf nf′ (r ∷ rs) rs′        = ⟹*-det nf nf′ rs (chopHead nf′ r rs′)

  _++_ : ∀ {t t′ t″} → t ⟹* t′ → t′ ⟹* t″ → t ⟹* t″
  []         ++ rs″ = rs″
  (r′ ∷ rs′) ++ rs″ = r′ ∷ (rs′ ++ rs″)

  _∷ʳ_ : ∀ {t t′ t″} → t ⟹* t′ → t′ ⟹ t″ → t ⟹* t″
  rs′ ∷ʳ r″ = rs′ ++ (r″ ∷ [])

  map : ∀ {t t′} {R : Term → Term} (f : ∀ {u u′} → u ⟹ u′ → R u ⟹ R u′) →
        t ⟹* t′ → R t ⟹* R t′
  map f []       = []
  map f (r ∷ rs) = (f r) ∷ (map f rs)


-- 3. Untyped arithmetic expressions

-- 3.1. Introduction

-- 3.2. Syntax

-- 3.2.1. Definition [Terms, inductively]

module NumbersAndBooleans where
  data Term : Set where
    true false zero : Term
    suc pred iszero : (t₁ : Term) → Term
    if_then_else    : (t₁ t₂ t₃ : Term) → Term


-- 3.2.2. Definition [Terms, by inference rules] (redundant)

-- 3.2.3. Definition [Terms, concretely] (redundant)

-- 3.2.4. Exercise (skipped)

-- 3.2.5. Exercise (skipped)

-- 3.2.6. Proposition (skipped)

-- 3.3. Induction on terms

-- 3.3.1. Definition

  module _ where
    _≟_ : BinRel.Decidable {A = Term} _≡_
    true                  ≟ true                  = yes refl
    true                  ≟ false                 = no λ ()
    true                  ≟ zero                  = no λ ()
    true                  ≟ suc t₁                = no λ ()
    true                  ≟ pred t₁               = no λ ()
    true                  ≟ iszero t₁             = no λ ()
    true                  ≟ if t₁ then t₂ else t₃ = no λ ()
    false                 ≟ true                  = no λ ()
    false                 ≟ false                 = yes refl
    false                 ≟ zero                  = no λ ()
    false                 ≟ suc t₁                = no λ ()
    false                 ≟ pred t₁               = no λ ()
    false                 ≟ iszero t₁             = no λ ()
    false                 ≟ if t₁ then t₂ else t₃ = no λ ()
    zero                  ≟ true                  = no λ ()
    zero                  ≟ false                 = no λ ()
    zero                  ≟ zero                  = yes refl
    zero                  ≟ suc t₁                = no λ ()
    zero                  ≟ pred t₁               = no λ ()
    zero                  ≟ iszero t₁             = no λ ()
    zero                  ≟ if t₁ then t₂ else t₃ = no λ ()
    suc s₁                ≟ true                  = no λ ()
    suc s₁                ≟ false                 = no λ ()
    suc s₁                ≟ zero                  = no λ ()
    suc s₁                ≟ suc t₁                with s₁ ≟ t₁
    ... | yes refl                                = yes refl
    ... | no s₁≢t₁                                = no λ where refl → refl ↯ s₁≢t₁
    suc s₁                ≟ pred t₁               = no λ ()
    suc s₁                ≟ iszero t₁             = no λ ()
    suc s₁                ≟ if t₁ then t₂ else t₃ = no λ ()
    pred s₁               ≟ true                  = no λ ()
    pred s₁               ≟ false                 = no λ ()
    pred s₁               ≟ zero                  = no λ ()
    pred s₁               ≟ suc t₁                = no λ ()
    pred s₁               ≟ pred t₁               with s₁ ≟ t₁
    ... | yes refl                                = yes refl
    ... | no s₁≢t₁                                = no λ where refl → refl ↯ s₁≢t₁
    pred s₁               ≟ iszero t₁             = no λ ()
    pred s₁               ≟ if t₁ then t₂ else t₃ = no λ ()
    iszero s₁             ≟ true                  = no λ ()
    iszero s₁             ≟ false                 = no λ ()
    iszero s₁             ≟ zero                  = no λ ()
    iszero s₁             ≟ suc t₁                = no λ ()
    iszero s₁             ≟ pred t₁               = no λ ()
    iszero s₁             ≟ iszero t₁             with s₁ ≟ t₁
    ... | yes refl                                = yes refl
    ... | no s₁≢t₁                                = no λ where refl → refl ↯ s₁≢t₁
    iszero s₁             ≟ if t₁ then t₂ else t₃ = no λ ()
    if s₁ then s₂ else s₃ ≟ true                  = no λ ()
    if s₁ then s₂ else s₃ ≟ false                 = no λ ()
    if s₁ then s₂ else s₃ ≟ zero                  = no λ ()
    if s₁ then s₂ else s₃ ≟ suc t₁                = no λ ()
    if s₁ then s₂ else s₃ ≟ pred t₁               = no λ ()
    if s₁ then s₂ else s₃ ≟ iszero t₁             = no λ ()
    if s₁ then s₂ else s₃ ≟ if t₁ then t₂ else t₃ with s₁ ≟ t₁ | s₂ ≟ t₂ | s₃ ≟ t₃
    ... | yes refl | yes refl | yes refl          = yes refl
    ... | no s₁≢t₁ | _        | _                 = no λ where refl → refl ↯ s₁≢t₁
    ... | _        | no s₂≢t₂ | _                 = no λ where refl → refl ↯ s₂≢t₂
    ... | _        | _        | no s₃≢t₃          = no λ where refl → refl ↯ s₃≢t₃

    Term-decSetoid : BinRel.DecSetoid _ _
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
  consts (iszero t₁)             = consts t₁
  consts (if t₁ then t₂ else t₃) = consts t₁ ∪ consts t₂ ∪ consts t₃


-- 3.3.2. Definition

  size : Term → ℕ
  size true                    = 1
  size false                   = 1
  size zero                    = 1
  size (suc t₁)                = 1 + size t₁
  size (pred t₁)               = 1 + size t₁
  size (iszero t₁)             = 1 + size t₁
  size (if t₁ then t₂ else t₃) = 1 + (size t₁ + size t₂ + size t₃)

  depth : Term → ℕ
  depth true                    = 1
  depth false                   = 1
  depth zero                    = 1
  depth (suc t₁)                = 1 + depth t₁
  depth (pred t₁)               = 1 + depth t₁
  depth (iszero t₁)             = 1 + depth t₁
  depth (if t₁ then t₂ else t₃) = 1 + (depth t₁ ⊔ depth t₂ ⊔ depth t₃)


-- 3.3.3. Lemma

  -- Direct proof using pattern matching
  module Lemma333-Direct where
    open Nat.≤-Reasoning

    lem333 : ∀ t → length (consts t) ≤ size t
    lem333 true                    = Nat.≤-refl
    lem333 false                   = Nat.≤-refl
    lem333 zero                    = Nat.≤-refl
    lem333 (suc t₁)                = Nat.≤-step (lem333 t₁)
    lem333 (pred t₁)               = Nat.≤-step (lem333 t₁)
    lem333 (iszero t₁)             = Nat.≤-step (lem333 t₁)
    lem333 (if t₁ then t₂ else t₃) = Nat.≤-step
      (begin
        length (consts t₁ ∪ consts t₂ ∪ consts t₃)
      ≤⟨ length-triangular (consts t₁ ∪ consts t₂) (consts t₃) ⟩
        length (consts t₁ ∪ consts t₂) + length (consts t₃)
      ≤⟨ Nat.+-monoˡ-≤ (length (consts t₃)) (length-triangular (consts t₁) (consts t₂)) ⟩
        length (consts t₁) + length (consts t₂) + length (consts t₃)
      ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (lem333 t₁) (lem333 t₂)) (lem333 t₃) ⟩
        size t₁ + size t₂ + size t₃
      ∎)


-- 3.3.4. Theorem [Principles of induction on terms]

-- 3.3.4.1. Structural induction

  module _ where
    data Subterm : Term → Term → Set where
      suc    : ∀ {t₁} → Subterm t₁ (suc t₁)
      pred   : ∀ {t₁} → Subterm t₁ (pred t₁)
      iszero : ∀ {t₁} → Subterm t₁ (iszero t₁)
      if₁    : ∀ {t₁ t₂ t₃} → Subterm t₁ (if t₁ then t₂ else t₃)
      if₂    : ∀ {t₁ t₂ t₃} → Subterm t₂ (if t₁ then t₂ else t₃)
      if₃    : ∀ {t₁ t₂ t₃} → Subterm t₃ (if t₁ then t₂ else t₃)

  -- Direct definition using pattern matching
  module IndStruct-Direct where
    ind-struct : ∀ {ℓ} {P : Term → Set ℓ} → InductionPrinciple Subterm P
    ind-struct h t@true                 = h t λ s ()
    ind-struct h t@false                = h t λ s ()
    ind-struct h t@zero                 = h t λ s ()
    ind-struct h t@(suc _)              = h t λ where s suc    → ind-struct h s
    ind-struct h t@(pred _)             = h t λ where s pred   → ind-struct h s
    ind-struct h t@(iszero _)           = h t λ where s iszero → ind-struct h s
    ind-struct h t@(if _ then _ else _) = h t λ where s if₁    → ind-struct h s
                                                      s if₂    → ind-struct h s
                                                      s if₃    → ind-struct h s

  -- Definition using combinators from the stdlib
  module IndStruct-Stdlib where
    import Induction.WellFounded as Stdlib

    subterm-wf : Stdlib.WellFounded Subterm
    subterm-wf s = Stdlib.acc λ where
      t₁ suc    → subterm-wf t₁
      t₁ pred   → subterm-wf t₁
      t₁ iszero → subterm-wf t₁
      t₁ if₁    → subterm-wf t₁
      t₂ if₂    → subterm-wf t₂
      t₃ if₃    → subterm-wf t₃

    module AllSubtermWF {ℓ} = Stdlib.All subterm-wf ℓ

    ind-struct : ∀ {ℓ} {P : Term → Set ℓ} → InductionPrinciple Subterm P
    ind-struct {P = P} = AllSubtermWF.wfRec P

  -- Definition using custom combinators
  module _ where
    subterm-wf : WellFounded Subterm
    subterm-wf s = access s λ where
      t₁ suc    → subterm-wf t₁
      t₁ pred   → subterm-wf t₁
      t₁ iszero → subterm-wf t₁
      t₁ if₁    → subterm-wf t₁
      t₂ if₂    → subterm-wf t₂
      t₃ if₃    → subterm-wf t₃

  ind-struct : ∀ {ℓ} {P : Term → Set ℓ} → InductionPrinciple Subterm P
  ind-struct = inductionPrinciple subterm-wf

  -- Proof using structural induction
  module Lemma333-IndStruct where
    open Nat.≤-Reasoning

    lem333 : ∀ s → length (consts s) ≤ size s
    lem333 = ind-struct λ where
      true                    h → Nat.≤-refl
      false                   h → Nat.≤-refl
      zero                    h → Nat.≤-refl
      (suc t₁)                h → Nat.≤-step (h t₁ suc)
      (pred t₁)               h → Nat.≤-step (h t₁ pred)
      (iszero t₁)             h → Nat.≤-step (h t₁ iszero)
      (if t₁ then t₂ else t₃) h → Nat.≤-step
        (begin
          length (consts t₁ ∪ consts t₂ ∪ consts t₃)
        ≤⟨ length-triangular (consts t₁ ∪ consts t₂) (consts t₃) ⟩
          length (consts t₁ ∪ consts t₂) + length (consts t₃)
        ≤⟨ Nat.+-monoˡ-≤ (length (consts t₃)) (length-triangular (consts t₁) (consts t₂)) ⟩
          length (consts t₁) + length (consts t₂) + length (consts t₃)
        ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (h t₁ if₁) (h t₂ if₂)) (h t₃ if₃) ⟩
          size t₁ + size t₂ + size t₃
        ∎)


-- 3.3.4.2. Induction on size

  module _ where
    LessSize : Term → Term → Set
    LessSize s t = size s < size t

    ls-wf : WellFounded LessSize
    ls-wf = InverseImage.wellFounded size <-wf

  ind-size : ∀ {ℓ} {P : Term → Set ℓ} → InductionPrinciple LessSize P
  ind-size = inductionPrinciple ls-wf

  -- Proof using induction on size
  module Lemma333-IndSize where
    open Nat.≤-Reasoning

    module _ where
      m≤m+n+o : ∀ m n o → m ≤ m + n + o
      m≤m+n+o m n o = Nat.≤-trans (Nat.m≤m+n m n) (Nat.m≤m+n (m + n) o)

      n≤m+n+o : ∀ m n o → n ≤ m + n + o
      n≤m+n+o m n o = Nat.≤-trans (Nat.n≤m+n m n) (Nat.m≤m+n (m + n) o)

      o≤m+n+o : ∀ m n o → o ≤ m + n + o
      o≤m+n+o m n o = Nat.n≤m+n (m + n) o

    ls-if₁ : ∀ t₁ t₂ t₃ → LessSize t₁ (if t₁ then t₂ else t₃)
    ls-if₁ t₁ t₂ t₃ = s≤s (m≤m+n+o (size t₁) (size t₂) (size t₃))

    ls-if₂ : ∀ t₁ t₂ t₃ → LessSize t₂ (if t₁ then t₂ else t₃)
    ls-if₂ t₁ t₂ t₃ = s≤s (n≤m+n+o (size t₁) (size t₂) (size t₃))

    ls-if₃ : ∀ t₁ t₂ t₃ → LessSize t₃ (if t₁ then t₂ else t₃)
    ls-if₃ t₁ t₂ t₃ = s≤s (o≤m+n+o (size t₁) (size t₂) (size t₃))

    lem333 : ∀ s → length (consts s) ≤ size s
    lem333 = ind-size λ where
      true                    h → Nat.≤-refl
      false                   h → Nat.≤-refl
      zero                    h → Nat.≤-refl
      (suc t₁)                h → Nat.≤-step (h t₁ Nat.≤-refl)
      (pred t₁)               h → Nat.≤-step (h t₁ Nat.≤-refl)
      (iszero t₁)             h → Nat.≤-step (h t₁ Nat.≤-refl)
      (if t₁ then t₂ else t₃) h → Nat.≤-step
        (begin
          length (consts t₁ ∪ consts t₂ ∪ consts t₃)
        ≤⟨ length-triangular (consts t₁ ∪ consts t₂) (consts t₃) ⟩
          length (consts t₁ ∪ consts t₂) + length (consts t₃)
        ≤⟨ Nat.+-monoˡ-≤ (length (consts t₃)) (length-triangular (consts t₁) (consts t₂)) ⟩
          length (consts t₁) + length (consts t₂) + length (consts t₃)
        ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (h t₁ (ls-if₁ t₁ t₂ t₃)) (h t₂ (ls-if₂ t₁ t₂ t₃))) (h t₃ (ls-if₃ t₁ t₂ t₃)) ⟩
          size t₁ + size t₂ + size t₃
        ∎)


-- 3.3.4.3. Induction on depth

  module _ where
    LessDepth : Term → Term → Set
    LessDepth s t = depth s < depth t

    ld-wf : WellFounded LessDepth
    ld-wf = InverseImage.wellFounded depth <-wf

  ind-depth : ∀ {ℓ} {P : Term → Set ℓ} → InductionPrinciple LessDepth P
  ind-depth = inductionPrinciple ld-wf

  -- Proof using induction on depth
  module Lemma333-IndDepth where
    open Nat.≤-Reasoning

    module _ where
      m≤m⊔n⊔o : ∀ m n o → m ≤ m ⊔ n ⊔ o
      m≤m⊔n⊔o m n o = Nat.≤-trans (Nat.m≤m⊔n m n) (Nat.m≤m⊔n (m ⊔ n) o)

      n≤m⊔n⊔o : ∀ m n o → n ≤ m ⊔ n ⊔ o
      n≤m⊔n⊔o m n o = Nat.≤-trans (Nat.n≤m⊔n m n) (Nat.m≤m⊔n (m ⊔ n) o)

      o≤m⊔n⊔o : ∀ m n o → o ≤ m ⊔ n ⊔ o
      o≤m⊔n⊔o m n o = Nat.n≤m⊔n (m ⊔ n) o

    ld-if₁ : ∀ t₁ t₂ t₃ → LessDepth t₁ (if t₁ then t₂ else t₃)
    ld-if₁ t₁ t₂ t₃ = s≤s (m≤m⊔n⊔o (depth t₁) (depth t₂) (depth t₃))

    ld-if₂ : ∀ t₁ t₂ t₃ → LessDepth t₂ (if t₁ then t₂ else t₃)
    ld-if₂ t₁ t₂ t₃ = s≤s (n≤m⊔n⊔o (depth t₁) (depth t₂) (depth t₃))

    ld-if₃ : ∀ t₁ t₂ t₃ → LessDepth t₃ (if t₁ then t₂ else t₃)
    ld-if₃ t₁ t₂ t₃ = s≤s (o≤m⊔n⊔o (depth t₁) (depth t₂) (depth t₃))

    lem333 : ∀ s → length (consts s) ≤ size s
    lem333 = ind-depth λ where
      true                    h → Nat.≤-refl
      false                   h → Nat.≤-refl
      zero                    h → Nat.≤-refl
      (suc t₁)                h → Nat.≤-step (h t₁ Nat.≤-refl)
      (pred t₁)               h → Nat.≤-step (h t₁ Nat.≤-refl)
      (iszero t₁)             h → Nat.≤-step (h t₁ Nat.≤-refl)
      (if t₁ then t₂ else t₃) h → Nat.≤-step
        (begin
          length (consts t₁ ∪ consts t₂ ∪ consts t₃)
        ≤⟨ length-triangular (consts t₁ ∪ consts t₂) (consts t₃) ⟩
          length (consts t₁ ∪ consts t₂) + length (consts t₃)
        ≤⟨ Nat.+-monoˡ-≤ (length (consts t₃)) (length-triangular (consts t₁) (consts t₂)) ⟩
          length (consts t₁) + length (consts t₂) + length (consts t₃)
        ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (h t₁ (ld-if₁ t₁ t₂ t₃)) (h t₂ (ld-if₂ t₁ t₂ t₃))) (h t₃ (ld-if₃ t₁ t₂ t₃)) ⟩
          size t₁ + size t₂ + size t₃
        ∎)


-- 3.4. Semantic styles

-- 3.5. Evaluation

-- 3.5.1. Definition (redundant)

-- 3.5.2. Definition (redundant)

-- 3.5.3. Definition

module BooleansOnly where
  module _ where
    data Term : Set where
      true false   : Term
      if_then_else : (t₁ t₂ t₃ : Term) → Term

    data Value : Term → Set where
      true  : Value true
      false : Value false

  -- t ⟹ t′ means that t reduces to t′ in one step
  infix 3 _⟹_
  data _⟹_ : Term → Term → Set where
    r-ifTrue  : ∀ {t₂ t₃} → if true then t₂ else t₃ ⟹ t₂
    r-ifFalse : ∀ {t₂ t₃} → if false then t₂ else t₃ ⟹ t₃
    r-if      : ∀ {t₁ t₁′ t₂ t₃} → t₁ ⟹ t₁′ → if t₁ then t₂ else t₃ ⟹ if t₁′ then t₂ else t₃

  open ReductionKit₁ _⟹_ public


-- 3.5.4. Theorem [Determinacy of one-step reduction]

  module _ where
    v⇒nf : ∀ {t} → Value t → NormalForm t
    v⇒nf true  ()
    v⇒nf false ()

  ⟹-det : ∀ {t t′ t″} → t ⟹ t′ → t ⟹ t″ → t′ ≡ t″
  ⟹-det r-ifTrue  r-ifTrue  = refl
  ⟹-det r-ifTrue  (r-if r′) = r′ ↯ v⇒nf true
  ⟹-det r-ifFalse r-ifFalse = refl
  ⟹-det r-ifFalse (r-if r′) = r′ ↯ v⇒nf false
  ⟹-det (r-if r)  r-ifTrue  = r ↯ v⇒nf true
  ⟹-det (r-if r)  r-ifFalse = r ↯ v⇒nf false
  ⟹-det (r-if r)  (r-if r′) = (λ s₁ → if s₁ then _ else _) & ⟹-det r r′

  open ReductionKit₂ _⟹_ ⟹-det public


-- 3.5.5. Exercise (skipped)

-- 3.5.6. Definition (given above)

-- 3.5.7. Definition (given above)

-- 3.5.8. Theorem

  module _ where
    data Classifiable : Term → Set where
      val : ∀ {t} → Value t → Classifiable t
      red : ∀ {t} → Reducible t → Classifiable t

    classify : ∀ t → Classifiable t
    classify true                    = val true
    classify false                   = val false
    classify (if t₁ then t₂ else t₃) with classify t₁
    ... | val true                   = red (t₂ , r-ifTrue)
    ... | val false                  = red (t₃ , r-ifFalse)
    ... | red (t₁′ , r₁)             = red (if t₁′ then t₂ else t₃ , r-if r₁)

  nf⇒v : ∀ {t} → NormalForm t → Value t
  nf⇒v {t} nf      with classify t
  ... | val v       = v
  ... | red (_ , r) = r ↯ nf


-- 3.5.9. Definition (included in ReductionKit₁)

-- 3.5.10. Exercise (redundant)

-- 3.5.11. Theorem [Uniqueness of normal forms] (included in ReductionKit₂)

-- 3.5.12. Theorem [Termination of evaluation]

  module _ where
    -- t ⇓ u means that t evaluates to u
    infix 3 _⇓_
    _⇓_ : Term → Term → Set
    t ⇓ u = Value u × t ⟹* u

    -- t ⇓ means that the evaluation of t terminates
    _⇓ : Term → Set
    t ⇓ = ∃ λ u → t ⇓ u

    halt-ifTrue : ∀ {t₁ t₂ t₃} → t₁ ⟹* true → t₂ ⇓ → if t₁ then t₂ else t₃ ⇓
    halt-ifTrue rs₁ (u₂ , v₂ , rs₂) = u₂ , v₂ , (map r-if rs₁) ++ (r-ifTrue ∷ rs₂)

    halt-ifFalse : ∀ {t₁ t₂ t₃} → t₁ ⟹* false → t₃ ⇓ → if t₁ then t₂ else t₃ ⇓
    halt-ifFalse rs₁ (u₃ , v₃ , rs₃) = u₃ , v₃ , (map r-if rs₁) ++ (r-ifFalse ∷ rs₃)

    halt : ∀ t → t ⇓
    halt true                    = true  , true  , []
    halt false                   = false , false , []
    halt (if t₁ then t₂ else t₃) with halt t₁
    ... | (.true  , true  , rs₁) = halt-ifTrue rs₁ (halt t₂)
    ... | (.false , false , rs₁) = halt-ifFalse rs₁ (halt t₃)

  halt′ : ∀ t → ∃ λ t′ → NormalForm t′ × t ⟹* t′
  halt′ t with halt t
  ... | (t′ , v , rs) = t′ , v⇒nf v , rs


-- 3.5.13. Exercise (skipped)

-- 3.5.14. Exercise

module NumbersAndBooleans′ where
  open NumbersAndBooleans public

  module _ where
    data NumericValue : Term → Set where
      zero : NumericValue zero
      suc  : ∀ {t₁} → NumericValue t₁ → NumericValue (suc t₁)

    data Value : Term → Set where
      true  : Value true
      false : Value false
      num   : ∀ {t₁} → NumericValue t₁ → Value t₁

    -- t ⟹ t′ means that t reduces to t′ in one step
    infix 3 _⟹_
    data _⟹_ : Term → Term → Set where
      r-suc        : ∀ {t₁ t₁′} → t₁ ⟹ t₁′ → suc t₁ ⟹ suc t₁′
      r-predZero   : pred zero ⟹ zero
      r-predSuc    : ∀ {t₁} → NumericValue t₁ → pred (suc t₁) ⟹ t₁
      r-pred       : ∀ {t₁ t₁′} → t₁ ⟹ t₁′ → pred t₁ ⟹ pred t₁′
      r-iszeroZero : iszero zero ⟹ true
      r-iszeroSuc  : ∀ {t₁} → NumericValue t₁ → iszero (suc t₁) ⟹ false
      r-iszero     : ∀ {t₁ t₁′} → t₁ ⟹ t₁′ → iszero t₁ ⟹ iszero t₁′
      r-ifTrue     : ∀ {t₂ t₃} → if true then t₂ else t₃ ⟹ t₂
      r-ifFalse    : ∀ {t₂ t₃} → if false then t₂ else t₃ ⟹ t₃
      r-if         : ∀ {t₁ t₁′ t₂ t₃} → t₁ ⟹ t₁′ → if t₁ then t₂ else t₃ ⟹ if t₁′ then t₂ else t₃

    open ReductionKit₁ _⟹_ public

    nv⇒nf : ∀ {t} → NumericValue t → NormalForm t
    nv⇒nf zero     ()
    nv⇒nf (suc nv) (r-suc r) = r ↯ nv⇒nf nv

    v⇒nf : ∀ {t} → Value t → NormalForm t
    v⇒nf true     ()
    v⇒nf false    ()
    v⇒nf (num nv) = nv⇒nf nv

  ⟹-det : ∀ {t t′ t″} → t ⟹ t′ → t ⟹ t″ → t′ ≡ t″
  ⟹-det (r-suc r′)        (r-suc r″)        = suc & ⟹-det r′ r″
  ⟹-det r-predZero        r-predZero        = refl
  ⟹-det r-predZero        (r-pred r″)       = r″ ↯ nv⇒nf zero
  ⟹-det (r-predSuc nv′)   (r-predSuc nv″)   = refl
  ⟹-det (r-predSuc nv′)   (r-pred r″)       = r″ ↯ nv⇒nf (suc nv′)
  ⟹-det (r-pred r′)       r-predZero        = r′ ↯ nv⇒nf zero
  ⟹-det (r-pred r′)       (r-predSuc nv″)   = r′ ↯ nv⇒nf (suc nv″)
  ⟹-det (r-pred r′)       (r-pred r″)       = pred & ⟹-det r′ r″
  ⟹-det r-iszeroZero      r-iszeroZero      = refl
  ⟹-det r-iszeroZero      (r-iszero r″)     = r″ ↯ nv⇒nf zero
  ⟹-det (r-iszeroSuc nv′) (r-iszeroSuc nv″) = refl
  ⟹-det (r-iszeroSuc nv′) (r-iszero r″)     = r″ ↯ nv⇒nf (suc nv′)
  ⟹-det (r-iszero r′)     r-iszeroZero      = r′ ↯ nv⇒nf zero
  ⟹-det (r-iszero r′)     (r-iszeroSuc nv″) = r′ ↯ nv⇒nf (suc nv″)
  ⟹-det (r-iszero r′)     (r-iszero r″)     = iszero & ⟹-det r′ r″
  ⟹-det r-ifTrue          r-ifTrue          = refl
  ⟹-det r-ifTrue          (r-if r″)         = r″ ↯ v⇒nf true
  ⟹-det r-ifFalse         r-ifFalse         = refl
  ⟹-det r-ifFalse         (r-if r″)         = r″ ↯ v⇒nf false
  ⟹-det (r-if r′)         r-ifTrue          = r′ ↯ v⇒nf true
  ⟹-det (r-if r′)         r-ifFalse         = r′ ↯ v⇒nf false
  ⟹-det (r-if r′)         (r-if r″)         = (λ t₁′ → if t₁′ then _ else _) & ⟹-det r′ r″

  open ReductionKit₂ _⟹_ ⟹-det public


-- 3.5.15. Exercise

module NumbersAndBooleansGetStuck where
  open NumbersAndBooleans′ public

  Stuck : Term → Set
  Stuck t = ¬ Value t × NormalForm t

  data Classifiable : Term → Set where
    stu : ∀ {t} → Stuck t → Classifiable t
    val : ∀ {t} → Value t → Classifiable t
    red : ∀ {t} → Reducible t → Classifiable t

  s-sucTrue : Stuck (suc true)
  s-sucTrue = ((λ where (num (suc ()))) , λ where (r-suc ()))

  s-sucFalse : Stuck (suc false)
  s-sucFalse = ((λ where (num (suc ()))) , λ where (r-suc ()))

  s-sucStuck : ∀ {t₁} → Stuck t₁ → Stuck (suc t₁)
  s-sucStuck (¬v₁ , nf₁) = ((λ where (num (suc nv₁)) → num nv₁ ↯ ¬v₁)
                           , λ where (r-suc r₁) → r₁ ↯ nf₁)

  s-predTrue : Stuck (pred true)
  s-predTrue = ((λ where (num ())) , λ where (r-pred ()))

  s-predFalse : Stuck (pred false)
  s-predFalse = ((λ where (num ())) , λ where (r-pred ()))

  s-predStuck : ∀ {t₁} → Stuck t₁ → Stuck (pred t₁)
  s-predStuck (¬v₁ , nf₁) = ((λ where (num ()))
                            , λ where r-predZero      → num zero ↯ ¬v₁
                                      (r-predSuc nv₁) → num (suc nv₁) ↯ ¬v₁
                                      (r-pred r₁)     → r₁ ↯ nf₁)

  s-iszeroTrue : Stuck (iszero true)
  s-iszeroTrue = ((λ where (num ())) , λ where (r-iszero ()))

  s-iszeroFalse : Stuck (iszero false)
  s-iszeroFalse = ((λ where (num ())) , λ where (r-iszero ()))

  s-iszero : ∀ {t₁} → Stuck t₁ → Stuck (iszero t₁)
  s-iszero (¬v₁ , nf₁) = ((λ where (num ()))
                         , λ where r-iszeroZero      → num zero ↯ ¬v₁
                                   (r-iszeroSuc nv₁) → num (suc nv₁) ↯ ¬v₁
                                   (r-iszero r₁)     → r₁ ↯ nf₁)

  s-ifZero : ∀ {t₂ t₃} → Stuck (if zero then t₂ else t₃)
  s-ifZero = ((λ where (num ())) , λ where (r-if ()))

  s-ifSuc : ∀ {nv₁ t₂ t₃} → NumericValue nv₁ → Stuck (if (suc nv₁) then t₂ else t₃)
  s-ifSuc nv₁ = ((λ where (num ()))
                , λ where (r-if (r-suc r₁)) → r₁ ↯ nv⇒nf nv₁)

  s-ifStuck : ∀ {t₁ t₂ t₃} → Stuck t₁ → Stuck (if t₁ then t₂ else t₃)
  s-ifStuck (¬v₁ , nf₁) = ((λ where (num ()))
                          , λ where r-ifTrue  → true ↯ ¬v₁
                                    r-ifFalse → false ↯ ¬v₁
                                    (r-if r₁) → r₁ ↯ nf₁)

  classify : ∀ t → Classifiable t
  classify true                    = val true
  classify false                   = val false
  classify zero                    = val (num zero)
  classify (suc t₁)                with classify t₁
  ... | stu s₁                     = stu (s-sucStuck s₁)
  ... | val true                   = stu s-sucTrue
  ... | val false                  = stu s-sucFalse
  ... | val (num nv₁)              = val (num (suc nv₁))
  ... | red (t₁′ , r₁)             = red (suc t₁′ , r-suc r₁)
  classify (pred t₁)               with classify t₁
  ... | stu s₁                     = stu (s-predStuck s₁)
  ... | val true                   = stu s-predTrue
  ... | val false                  = stu s-predFalse
  ... | val (num zero)             = red (zero , r-predZero)
  ... | val (num (suc nv₁))        = red (_ , r-predSuc nv₁)
  ... | red (t₁′ , r₁)             = red (pred t₁′ , r-pred r₁)
  classify (iszero t₁)             with classify t₁
  ... | stu s₁                     = stu (s-iszero s₁)
  ... | val true                   = stu s-iszeroTrue
  ... | val false                  = stu s-iszeroFalse
  ... | val (num zero)             = red (true , r-iszeroZero)
  ... | val (num (suc nv₁))        = red (false , r-iszeroSuc nv₁)
  ... | red (t₁′ , r₁)             = red (iszero t₁′ , r-iszero r₁)
  classify (if t₁ then t₂ else t₃) with classify t₁
  ... | stu s₁                     = stu (s-ifStuck s₁)
  ... | val true                   = red (t₂ , r-ifTrue)
  ... | val false                  = red (t₃ , r-ifFalse)
  ... | val (num zero)             = stu s-ifZero
  ... | val (num (suc nv₁))        = stu (s-ifSuc nv₁)
  ... | red (t₁′ , r₁)             = red (if t₁′ then t₂ else t₃ , r-if r₁)

  nf⇒v⊎s : ∀ {t} → NormalForm t → Value t ⊎ Stuck t
  nf⇒v⊎s {t} nf    with classify t
  ... | red (_ , r) = r ↯ nf
  ... | val v       = inj₁ v
  ... | stu s       = inj₂ s

  -- t ⇓ u means that t evaluates to u
  infix 3 _⇓_
  _⇓_ : Term → Term → Set
  t ⇓ u = (Value u ⊎ Stuck u) × t ⟹* u

  -- t ⇓ means that the evaluation of t terminates
  _⇓ : Term → Set
  t ⇓ = ∃ λ u → t ⇓ u

  halt-sucTrue : ∀ {t₁} → t₁ ⟹* true → suc t₁ ⇓
  halt-sucTrue rs₁ = {!!}

  halt-sucFalse : ∀ {t₁} → t₁ ⟹* false → suc t₁ ⇓
  halt-sucFalse rs₁ = {!!}

  halt-sucZero : ∀ {t₁} → t₁ ⟹* zero → suc t₁ ⇓
  halt-sucZero rs₁ = {!!}

  halt-sucSuc : ∀ {t₁ u₁} → NumericValue u₁ → t₁ ⟹* suc u₁ → suc t₁ ⇓
  halt-sucSuc nv₁ rs₁ = {!!}

  halt-sucStuck : ∀ {t₁ u₁} → Stuck u₁ → t₁ ⟹* u₁ → suc t₁ ⇓
  halt-sucStuck s₁ rs₁ = {!!}

  halt-predTrue : ∀ {t₁} → t₁ ⟹* true → pred t₁ ⇓
  halt-predTrue rs₁ = {!!}

  halt-predFalse : ∀ {t₁} → t₁ ⟹* false → pred t₁ ⇓
  halt-predFalse rs₁ = {!!}

  halt-predZero : ∀ {t₁} → t₁ ⟹* zero → pred t₁ ⇓
  halt-predZero rs₁ = {!!}

  halt-predSuc : ∀ {t₁ u₁} → NumericValue u₁ → t₁ ⟹* suc u₁ → pred t₁ ⇓
  halt-predSuc nv₁ rs₁ = {!!}

  halt-predStuck : ∀ {t₁ u₁} → Stuck u₁ → t₁ ⟹* u₁ → pred t₁ ⇓
  halt-predStuck s₁ rs₁ = {!!}

  halt-iszeroTrue : ∀ {t₁} → t₁ ⟹* true → iszero t₁ ⇓
  halt-iszeroTrue rs₁ = iszero true , inj₂ s-iszeroTrue , map r-iszero rs₁

  halt-iszeroFalse : ∀ {t₁} → t₁ ⟹* false → iszero t₁ ⇓
  halt-iszeroFalse rs₁ = iszero false , inj₂ s-iszeroFalse , map r-iszero rs₁

  halt-iszeroZero : ∀ {t₁} → t₁ ⟹* zero → iszero t₁ ⇓
  halt-iszeroZero rs₁ = true , inj₁ true , (map r-iszero rs₁) ∷ʳ r-iszeroZero

  halt-iszeroSuc : ∀ {t₁ u₁} → NumericValue u₁ → t₁ ⟹* suc u₁ → iszero t₁ ⇓
  halt-iszeroSuc nv₁ rs₁ = {!!}

  halt-iszeroStuck : ∀ {t₁ u₁} → Stuck u₁ → t₁ ⟹* u₁ → iszero t₁ ⇓
  halt-iszeroStuck s₁ rs₁ = {!!}

  halt-ifTrue : ∀ {t₁ t₂ t₃} → t₁ ⟹* true → t₂ ⇓ → if t₁ then t₂ else t₃ ⇓
  halt-ifTrue rs₁ (u₂ , v₂ , rs₂) = u₂ , v₂ , (map r-if rs₁) ++ (r-ifTrue ∷ rs₂)

  halt-ifFalse : ∀ {t₁ t₂ t₃} → t₁ ⟹* false → t₃ ⇓ → if t₁ then t₂ else t₃ ⇓
  halt-ifFalse rs₁ (u₃ , v₃ , rs₃) = u₃ , v₃ , (map r-if rs₁) ++ (r-ifFalse ∷ rs₃)

  halt-ifZero : ∀ {t₁ t₂ t₃} → t₁ ⟹* zero → if t₁ then t₂ else t₃ ⇓
  halt-ifZero rs₁ = if zero then _ else _ , inj₂ s-ifZero , map r-if rs₁

  halt-ifSuc : ∀ {t₁ t₂ t₃ u₁} → NumericValue u₁ → t₁ ⟹* suc u₁ → if t₁ then t₂ else t₃ ⇓
  halt-ifSuc nv₁ rs₁ = if (suc _) then _ else _ , inj₂ (s-ifSuc nv₁) , map r-if rs₁

  halt-ifStuck : ∀ {t₁ t₂ t₃ u₁} → Stuck u₁ → t₁ ⟹* u₁ → if t₁ then t₂ else t₃ ⇓
  halt-ifStuck s₁ rs₁ = if _ then _ else _ , inj₂ (s-ifStuck s₁) , map r-if rs₁

  halt : ∀ t → t ⇓
  halt true                                     = true  , inj₁ true       , []
  halt false                                    = false , inj₁ false      , []
  halt zero                                     = zero  , inj₁ (num zero) , []
  halt (suc t₁)                                 with halt t₁
  ... | (.true    , inj₁ true            , rs₁) = halt-sucTrue rs₁
  ... | (.false   , inj₁ false           , rs₁) = halt-sucFalse rs₁
  ... | (.zero    , inj₁ (num zero)      , rs₁) = halt-sucZero rs₁
  ... | (.(suc _) , inj₁ (num (suc nv₁)) , rs₁) = halt-sucSuc nv₁ rs₁
  ... | (_        , inj₂ s₁              , rs₁) = halt-sucStuck s₁ rs₁
  halt (pred t₁)                                with halt t₁
  ... | (.true    , inj₁ true            , rs₁) = halt-predTrue rs₁
  ... | (.false   , inj₁ false           , rs₁) = halt-predFalse rs₁
  ... | (.zero    , inj₁ (num zero)      , rs₁) = halt-predZero rs₁
  ... | (.(suc _) , inj₁ (num (suc nv₁)) , rs₁) = halt-predSuc nv₁ rs₁
  ... | (_        , inj₂ s₁              , rs₁) = halt-predStuck s₁ rs₁
  halt (iszero t₁)                              with halt t₁
  ... | (.true    , inj₁ true            , rs₁) = halt-iszeroTrue rs₁
  ... | (.false   , inj₁ false           , rs₁) = halt-iszeroFalse rs₁
  ... | (.zero    , inj₁ (num zero)      , rs₁) = halt-iszeroZero rs₁
  ... | (.(suc _) , inj₁ (num (suc nv₁)) , rs₁) = halt-iszeroSuc nv₁ rs₁
  ... | (_        , inj₂ s₁              , rs₁) = halt-iszeroStuck s₁ rs₁
  halt (if t₁ then t₂ else t₃)                  with halt t₁
  ... | (.true    , inj₁ true            , rs₁) = halt-ifTrue rs₁ (halt t₂)
  ... | (.false   , inj₁ false           , rs₁) = halt-ifFalse rs₁ (halt t₃)
  ... | (.zero    , inj₁ (num zero)      , rs₁) = halt-ifZero rs₁
  ... | (.(suc _) , inj₁ (num (suc nv₁)) , rs₁) = halt-ifSuc nv₁ rs₁
  ... | (_        , inj₂ s₁              , rs₁) = halt-ifStuck s₁ rs₁

  halt′ : ∀ t → ∃ λ t′ → NormalForm t′ × t ⟹* t′
  halt′ t with halt t
  ... | (t′ , inj₁ v         , rs) = t′ , v⇒nf v , rs
  ... | (t′ , inj₂ (¬v , nf) , rs) = t′ , nf      , rs


-- 3.5.16. Exercise

module NumbersAndBooleansGoWrong where
  data Term : Set where
    wrong true false zero : Term
    suc pred iszero       : (t₁ : Term) → Term
    if_then_else          : (t₁ t₂ t₃ : Term) → Term

  data NumericValue : Term → Set where
    zero : NumericValue zero
    suc  : ∀ {t₁} → NumericValue t₁ → NumericValue (suc t₁)

  data Value : Term → Set where
    true  : Value true
    false : Value false
    num   : ∀ {t₁} → NumericValue t₁ → Value t₁

  data BadNat : Term → Set where
    wrong : BadNat wrong
    true  : BadNat true
    false : BadNat false

  data BadBool : Term → Set where
    wrong : BadBool wrong
    num   : ∀ {u} → NumericValue u → BadBool u

  -- t ⟹ t′ means that t reduces to t′ in one step
  infix 3 _⟹_
  data _⟹_ : Term → Term → Set where
    r-sucWrong    : ∀ {t₁} → BadNat t₁ → suc t₁ ⟹ wrong
    r-suc         : ∀ {t₁ t₁′} → t₁ ⟹ t₁′ → suc t₁ ⟹ suc t₁′
    r-predWrong   : ∀ {t₁} → BadNat t₁ → pred t₁ ⟹ wrong
    r-predZero    : pred zero ⟹ zero
    r-predSuc     : ∀ {t₁} → NumericValue t₁ → pred (suc t₁) ⟹ t₁
    r-pred        : ∀ {t₁ t₁′} → t₁ ⟹ t₁′ → pred t₁ ⟹ pred t₁′
    r-iszeroWrong : ∀ {t₁} → BadNat t₁ → iszero t₁ ⟹ wrong
    r-iszeroZero  : iszero zero ⟹ true
    r-iszeroSuc   : ∀ {t₁} → NumericValue t₁ → iszero (suc t₁) ⟹ false
    r-iszero      : ∀ {t₁ t₁′} → t₁ ⟹ t₁′ → iszero t₁ ⟹ iszero t₁′
    r-ifWrong     : ∀ {t₁ t₂ t₃} → BadBool t₁ → if t₁ then t₂ else t₃ ⟹ wrong
    r-ifTrue      : ∀ {t₂ t₃} → if true then t₂ else t₃ ⟹ t₂
    r-ifFalse     : ∀ {t₂ t₃} → if false then t₂ else t₃ ⟹ t₃
    r-if          : ∀ {t₁ t₁′ t₂ t₃} → t₁ ⟹ t₁′ → if t₁ then t₂ else t₃ ⟹ if t₁′ then t₂ else t₃

  open ReductionKit₁ _⟹_

  bn⇒¬nv : ∀ {t} → BadNat t → ¬ NumericValue t
  bn⇒¬nv wrong = λ ()
  bn⇒¬nv true  = λ ()
  bn⇒¬nv false = λ ()

  nv⇒nf : ∀ {t} → NumericValue t → NormalForm t
  nv⇒nf zero     = λ ()
  nv⇒nf (suc nv) = λ where
    (r-sucWrong bn) → nv ↯ bn⇒¬nv bn
    (r-suc r)       → r ↯ nv⇒nf nv

  v⇒nf : ∀ {t} → Value t → NormalForm t
  v⇒nf true     = λ ()
  v⇒nf false    = λ ()
  v⇒nf (num nv) = nv⇒nf nv

  bn⇒nf : ∀ {t} → BadNat t → NormalForm t
  bn⇒nf wrong = λ ()
  bn⇒nf true  = λ ()
  bn⇒nf false = λ ()

  bb⇒nf : ∀ {t} → BadBool t → NormalForm t
  bb⇒nf wrong    = λ ()
  bb⇒nf (num nv) = nv⇒nf nv

  ⟹-det : ∀ {t t′ t″} → t ⟹ t′ → t ⟹ t″ → t′ ≡ t″
  ⟹-det (r-sucWrong bn′)     (r-sucWrong bn″)    = refl
  ⟹-det (r-sucWrong bn′)     (r-suc r″)          = r″ ↯ bn⇒nf bn′
  ⟹-det (r-suc r′)           (r-sucWrong bn″)    = r′ ↯ bn⇒nf bn″
  ⟹-det (r-suc r′)           (r-suc r″)          = suc & ⟹-det r′ r″
  ⟹-det (r-predWrong bn′)    (r-predWrong bn″)   = refl
  ⟹-det (r-predWrong ())     r-predZero
  ⟹-det (r-predWrong ())     (r-predSuc nv″)
  ⟹-det (r-predWrong bn′)    (r-pred r″)         = r″ ↯ bn⇒nf bn′
  ⟹-det r-predZero (         r-predWrong ())
  ⟹-det r-predZero           r-predZero          = refl
  ⟹-det r-predZero           (r-pred r″)         = r″ ↯ nv⇒nf zero
  ⟹-det (r-predSuc nv′)      (r-predWrong ())
  ⟹-det (r-predSuc nv′)      (r-predSuc nv″)     = refl
  ⟹-det (r-predSuc nv′)      (r-pred r″)         = r″ ↯ nv⇒nf (suc nv′)
  ⟹-det (r-pred r′)          (r-predWrong bn″)   = r′ ↯ bn⇒nf bn″
  ⟹-det (r-pred r′)          r-predZero          = r′ ↯ nv⇒nf zero
  ⟹-det (r-pred r′)          (r-predSuc nv″)     = r′ ↯ nv⇒nf (suc nv″)
  ⟹-det (r-pred r′)          (r-pred r″)         = pred & ⟹-det r′ r″
  ⟹-det (r-iszeroWrong bn′)  (r-iszeroWrong bn″) = refl
  ⟹-det (r-iszeroWrong ())   r-iszeroZero
  ⟹-det (r-iszeroWrong ())   (r-iszeroSuc nv″)
  ⟹-det (r-iszeroWrong bn′)  (r-iszero r″)       = r″ ↯ bn⇒nf bn′
  ⟹-det r-iszeroZero         (r-iszeroWrong ())
  ⟹-det r-iszeroZero         r-iszeroZero        = refl
  ⟹-det r-iszeroZero         (r-iszero r″)       = r″ ↯ nv⇒nf zero
  ⟹-det (r-iszeroSuc nv′)    (r-iszeroWrong ())
  ⟹-det (r-iszeroSuc nv′)    (r-iszeroSuc nv″)   = refl
  ⟹-det (r-iszeroSuc nv′)    (r-iszero r″)       = r″ ↯ nv⇒nf (suc nv′)
  ⟹-det (r-iszero r′)        (r-iszeroWrong bn″) = r′ ↯ bn⇒nf bn″
  ⟹-det (r-iszero r′)        r-iszeroZero        = r′ ↯ nv⇒nf zero
  ⟹-det (r-iszero r′)        (r-iszeroSuc nv″)   = r′ ↯ nv⇒nf (suc nv″)
  ⟹-det (r-iszero r′)        (r-iszero r″)       = iszero & ⟹-det r′ r″
  ⟹-det (r-ifWrong bb′)      (r-ifWrong bb″)     = refl
  ⟹-det (r-ifWrong (num ())) r-ifTrue
  ⟹-det (r-ifWrong (num ())) r-ifFalse
  ⟹-det (r-ifWrong bb′)      (r-if r″)           = r″ ↯ bb⇒nf bb′
  ⟹-det r-ifTrue             (r-ifWrong (num ()))
  ⟹-det r-ifTrue             r-ifTrue            = refl
  ⟹-det r-ifTrue             (r-if r″)           = r″ ↯ v⇒nf true
  ⟹-det r-ifFalse            (r-ifWrong (num ()))
  ⟹-det r-ifFalse            r-ifFalse           = refl
  ⟹-det r-ifFalse            (r-if r″)           = r″ ↯ v⇒nf false
  ⟹-det (r-if r′)            (r-ifWrong bb″)     = r′ ↯ bb⇒nf bb″
  ⟹-det (r-if r′)            r-ifTrue            = r′ ↯ v⇒nf true
  ⟹-det (r-if r′)            r-ifFalse           = r′ ↯ v⇒nf false
  ⟹-det (r-if r′)            (r-if r″)           = (λ t₁′ → if t₁′ then _ else _) & ⟹-det r′ r″

  open ReductionKit₂ _⟹_ ⟹-det

  -- t ⇓ u means that t evaluates to u
  infix 3 _⇓_
  _⇓_ : Term → Term → Set
  t ⇓ u = (Value u ⊎ u ≡ wrong) × t ⟹* u

  -- t ⇓ means that the evaluation of t terminates
  _⇓ : Term → Set
  t ⇓ = ∃ λ u → t ⇓ u

  halt-ifTrue : ∀ {t₁ t₂ t₃} → t₁ ⟹* true → t₂ ⇓ → if t₁ then t₂ else t₃ ⇓
  halt-ifTrue rs₁ (u₂ , v₂ , rs₂) = u₂ , v₂ , (map r-if rs₁) ++ (r-ifTrue ∷ rs₂)

  halt-ifFalse : ∀ {t₁ t₂ t₃} → t₁ ⟹* false → t₃ ⇓ → if t₁ then t₂ else t₃ ⇓
  halt-ifFalse rs₁ (u₃ , v₃ , rs₃) = u₃ , v₃ , (map r-if rs₁) ++ (r-ifFalse ∷ rs₃)
