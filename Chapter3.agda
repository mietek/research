----------------------------------------------------------------------------------------------------

module Chapter3 where

import Data.Nat as Nat
open Nat
  using (_≤_ ; _<_ ; _+_ ; s≤s ; suc ; zero)
  renaming (ℕ to Nat)

import Data.Nat.Properties as Nat
open Nat.≤-Reasoning

open import Data.Product
  using (_×_ ; _,_ ; Σ ; ∃ ; proj₁ ; proj₂)

open import Level
  using (_⊔_ ; 0ℓ)

open import Relation.Binary
  using (_=[_]⇒_ ; Decidable ; DecSetoid ; Rel)

import Relation.Binary.PropositionalEquality as PropEq
open PropEq
  using (_≡_ ; _≢_ ; refl ; subst)
  renaming (cong to _&_) -- ; sym to _⁻¹)

import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
open Star using ()
  renaming (Star to _* ; ε to [] ; _◅_ to _∷_ ; _◅◅_ to _++_)

open import Relation.Nullary
  using (¬_ ; Dec ; no ; yes)

open import Relation.Nullary.Negation
  renaming (contradiction to _↯_)

open import Relation.Unary
  using (Pred)


----------------------------------------------------------------------------------------------------
--
-- TODO: Put this in a separate module

infixl 8 _⊗_
_⊗_ : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} {x y : A} →
      f ≡ g → x ≡ y → f x ≡ g y
refl ⊗ refl = refl

coerce : ∀ {ℓ} {A B : Set ℓ} → A → A ≡ B → B
coerce x refl = x

Pred₀ : ∀ {a} → Set a → Set _
Pred₀ A = Pred A 0ℓ

Rel₀ : ∀ {a} → Set a → Set _
Rel₀ A = Rel A 0ℓ


----------------------------------------------------------------------------------------------------
--
-- 3. Untyped arithmetic expressions
--
-- 3.1. Introduction
--
-- 3.2. Syntax


----------------------------------------------------------------------------------------------------
--
-- 3.2.1. Definition [Terms, inductively]
-- “The set of _terms_ is the smallest set `T` such that …”

module NumbersAndBooleans-Part1
  where
    data Term : Set₀ where
      true false zero : Term
      suc pred iszero : (t₁ : Term) → Term
      if_then_else    : (t₁ t₂ t₃ : Term) → Term


----------------------------------------------------------------------------------------------------
--
-- 3.2.2. Definition [Terms, by inference rules]
-- “The set of terms is defined by the following rules: …”
-- (redundant)
--
-- 3.2.3. Definition [Terms, concretely]
-- “For each natural number `i`, define a set `Sᵢ` as follows: …”
-- (redundant)
--
-- 3.2.4. Exercise [⋆⋆]
-- “How many elements does `S₃` have?”
-- (skipped)
--
-- 3.2.5. Exercise [⋆⋆]
-- “Show that the sets `Sᵢ` are _cumulative_—that is, that for each `i` we have `Sᵢ ⊆ Sᵢ₊₁`.”
-- (skipped)
--
-- 3.2.6. Proposition
-- “`T = S`.”
-- (skipped)


----------------------------------------------------------------------------------------------------
--
-- 3.3. Induction on terms
--
-- Since we’re working in type theory, we’re going to need a type of containers that are not allowed
-- to contain duplicate elements, `UniqueList`.  To put terms in such a container, we’re going to
-- need a decidable equality on terms.  Therefore, we’re going to show that the built-in Agda
-- equality, `_≡_`, is decidable for terms.

    open import Prelude-UniqueList public

    _≟_ : Decidable {A = Term} _≡_
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
    ... | yes refl | yes refl | no s₃≢t₃          = no λ where refl → refl ↯ s₃≢t₃
    ... | yes refl | no s₂≢t₂ | _                 = no λ where refl → refl ↯ s₂≢t₂
    ... | no s₁≢t₁ | _        | _                 = no λ where refl → refl ↯ s₁≢t₁

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


----------------------------------------------------------------------------------------------------
--
-- 3.3.1. Definition
-- “The set of constants appearing in a term `t`, written `consts(t)`, is defined as follows: …”

    consts : Term → UniqueList
    consts true                    = [ true ]
    consts false                   = [ false ]
    consts zero                    = [ zero ]
    consts (suc t₁)                = consts t₁
    consts (pred t₁)               = consts t₁
    consts (iszero t₁)             = consts t₁
    consts (if t₁ then t₂ else t₃) = consts t₁ ∪ consts t₂ ∪ consts t₃


----------------------------------------------------------------------------------------------------
--
-- 3.3.2. Definition
-- “The _size_ of a term `t`, written `size(t)`, is defined as follows: …”
-- “Similarly, the _depth_ of a term `t`, written `depth(t)`, is defined as follows: …”

    size : Term → Nat
    size true                    = 1
    size false                   = 1
    size zero                    = 1
    size (suc t₁)                = 1 + size t₁
    size (pred t₁)               = 1 + size t₁
    size (iszero t₁)             = 1 + size t₁
    size (if t₁ then t₂ else t₃) = 1 + (size t₁ + size t₂ + size t₃)

    depth : Term → Nat
    depth true                    = 1
    depth false                   = 1
    depth zero                    = 1
    depth (suc t₁)                = 1 + depth t₁
    depth (pred t₁)               = 1 + depth t₁
    depth (iszero t₁)             = 1 + depth t₁
    depth (if t₁ then t₂ else t₃) = 1 + (depth t₁ Nat.⊔ depth t₂ Nat.⊔ depth t₃)


----------------------------------------------------------------------------------------------------
--
-- 3.3.3. Lemma
-- “The number of distinct constants in a term `t` is no greater than the size of `t` (i.e.,
-- `|consts(t)| ≤ size(t)`).”
--
-- As an exercise, we’re going to prove Lemma 3.3.3 using four methods.  First, the most natural
-- method to use in Agda, a direct proof using pattern matching.

    module Lemma333-Direct
      where
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
          ≤⟨ Nat.+-monoˡ-≤ (length (consts t₃))
                           (length-triangular (consts t₁) (consts t₂)) ⟩
            length (consts t₁) + length (consts t₂) + length (consts t₃)
          ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (lem333 t₁)
                                        (lem333 t₂))
                          (lem333 t₃) ⟩
            size t₁ + size t₂ + size t₃
          ∎)


----------------------------------------------------------------------------------------------------
--
-- 3.3.4. Theorem [Principles of induction on terms]
--
-- 3.3.4.a. Structural induction
-- “If, for each term `t`, given `P(s)` for all immediate subterms `s` of `t` we can show `P(t)`,
-- then `P(t)` holds for all `t`.
--
-- We’re going to start by defining what it means for a term to be an immediate subterm of another
-- term.

    data Subterm : Rel₀ Term where
      suc    : ∀ {t₁} → Subterm t₁ (suc t₁)
      pred   : ∀ {t₁} → Subterm t₁ (pred t₁)
      iszero : ∀ {t₁} → Subterm t₁ (iszero t₁)
      if₁    : ∀ {t₁ t₂ t₃} → Subterm t₁ (if t₁ then t₂ else t₃)
      if₂    : ∀ {t₁ t₂ t₃} → Subterm t₂ (if t₁ then t₂ else t₃)
      if₃    : ∀ {t₁ t₂ t₃} → Subterm t₃ (if t₁ then t₂ else t₃)


-- As an exercise, we’re going to define structural induction using three methods.  First, a direct
-- definition using pattern matching.

    module IndStruct-Direct
      where
        ind-struct : ∀ {ℓ} {P : Pred Term ℓ} →
                     (∀ t → (∀ s → Subterm s t → P s) → P t) → ∀ t → P t
        ind-struct h t@true                 = h t λ s ()
        ind-struct h t@false                = h t λ s ()
        ind-struct h t@zero                 = h t λ s ()
        ind-struct h t@(suc _)              = h t λ where s suc    → ind-struct h s
        ind-struct h t@(pred _)             = h t λ where s pred   → ind-struct h s
        ind-struct h t@(iszero _)           = h t λ where s iszero → ind-struct h s
        ind-struct h t@(if _ then _ else _) = h t λ where s if₁    → ind-struct h s
                                                          s if₂    → ind-struct h s
                                                          s if₃    → ind-struct h s


-- Second, a definition based on well-founded induction and accessibility, using equipment from
-- the Agda standard library.  Some of the definitions referenced are a little difficult to
-- understand, as acknowledged in the documentation.

    module IndStruct-Stdlib
      where
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

        ind-struct : ∀ {ℓ} {P : Pred Term ℓ} →
                     (∀ t → (∀ s → Subterm s t → P s) → P t) → ∀ t → P t
        ind-struct {P = P} = AllSubtermWF.wfRec P


-- Third, a definition using our own equipment.  We’d like to think that our phrasing of the
-- concepts involved is a little easier to understand, while being no less general.

    open import Prelude-WellFounded public

    subterm-wf : WellFounded Subterm
    subterm-wf s = access s λ where
      t₁ suc    → subterm-wf t₁
      t₁ pred   → subterm-wf t₁
      t₁ iszero → subterm-wf t₁
      t₁ if₁    → subterm-wf t₁
      t₂ if₂    → subterm-wf t₂
      t₃ if₃    → subterm-wf t₃

    ind-struct : ∀ {ℓ} {P : Pred Term ℓ} → InductionPrinciple Subterm P
    ind-struct = inductionPrinciple subterm-wf


-- A proof of Lemma 3.3.3 using structural induction.

    module Lemma333-IndStruct
      where
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
            ≤⟨ Nat.+-monoˡ-≤ (length (consts t₃))
                             (length-triangular (consts t₁) (consts t₂)) ⟩
              length (consts t₁) + length (consts t₂) + length (consts t₃)
            ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (h t₁ if₁)
                                          (h t₂ if₂))
                            (h t₃ if₃) ⟩
              size t₁ + size t₂ + size t₃
            ∎)


----------------------------------------------------------------------------------------------------
--
-- 3.3.4.b. Induction on size
-- “If, for each term `t`, given `P(s)` for all `s` such that `size(s) < size(t)` we can show
-- `P(t)`, then `P(t)` holds for all `t`.”
--
-- A definition based on well-founded induction.

    LessSize : Rel₀ Term
    LessSize s t = size s < size t

    ls-wf : WellFounded LessSize
    ls-wf = InverseImage.wellFounded size <-wf

    ind-size : ∀ {ℓ} {P : Pred Term ℓ} → InductionPrinciple LessSize P
    ind-size = inductionPrinciple ls-wf


-- Another proof of Lemma 3.3.3 using induction on size.

    module Lemma333-IndSize
      where
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
            ≤⟨ Nat.+-monoˡ-≤ (length (consts t₃))
                             (length-triangular (consts t₁) (consts t₂)) ⟩
              length (consts t₁) + length (consts t₂) + length (consts t₃)
            ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (h t₁ (ls-if₁ t₁ t₂ t₃))
                                          (h t₂ (ls-if₂ t₁ t₂ t₃)))
                            (h t₃ (ls-if₃ t₁ t₂ t₃)) ⟩
              size t₁ + size t₂ + size t₃
            ∎)


----------------------------------------------------------------------------------------------------
--
-- 3.3.4.c. Induction on depth
-- “If, for each term `t`, given `P(s)` for all `s` such that `depth(s) < depth(t)` we can show
-- `P(t)`, then `P(t)` holds for all `t`.”
--
-- A definition based on well-founded induction.

    LessDepth : Rel₀ Term
    LessDepth s t = depth s < depth t

    ld-wf : WellFounded LessDepth
    ld-wf = InverseImage.wellFounded depth <-wf

    ind-depth : ∀ {ℓ} {P : Pred Term ℓ} → InductionPrinciple LessDepth P
    ind-depth = inductionPrinciple ld-wf


-- Another proof of Lemma 3.3.3 using induction on depth.

    module Lemma333-IndDepth
      where
        m≤m⊔n⊔o : ∀ m n o → m ≤ m Nat.⊔ n Nat.⊔ o
        m≤m⊔n⊔o m n o = Nat.≤-trans (Nat.m≤m⊔n m n) (Nat.m≤m⊔n (m Nat.⊔ n) o)

        n≤m⊔n⊔o : ∀ m n o → n ≤ m Nat.⊔ n Nat.⊔ o
        n≤m⊔n⊔o m n o = Nat.≤-trans (Nat.n≤m⊔n m n) (Nat.m≤m⊔n (m Nat.⊔ n) o)

        o≤m⊔n⊔o : ∀ m n o → o ≤ m Nat.⊔ n Nat.⊔ o
        o≤m⊔n⊔o m n o = Nat.n≤m⊔n (m Nat.⊔ n) o

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
            ≤⟨ Nat.+-monoˡ-≤ (length (consts t₃))
                             (length-triangular (consts t₁) (consts t₂)) ⟩
              length (consts t₁) + length (consts t₂) + length (consts t₃)
            ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (h t₁ (ld-if₁ t₁ t₂ t₃))
                                          (h t₂ (ld-if₂ t₁ t₂ t₃)))
                            (h t₃ (ld-if₃ t₁ t₂ t₃)) ⟩
              size t₁ + size t₂ + size t₃
            ∎)


----------------------------------------------------------------------------------------------------
--
-- 3.4. Semantic styles
--
-- 3.5. Evaluation
--
-- In this section, we leave numbers aside and focus on boolean expressions.

module BooleansOnly-Part1
  where
    data Term : Set₀ where
      true false   : Term
      if_then_else : (t₁ t₂ t₃ : Term) → Term

    data Value : Pred₀ Term where
      true  : Value true
      false : Value false


----------------------------------------------------------------------------------------------------
--
-- 3.5.1. Definition
-- “An _instance_ of an inference rule is obtained by consistently replacing each metavariable by
-- the same term in the rule’s conclusion and all its premises (if any).”
--
-- In Agda, we model inference rules as constructors of inductive type families.  Thus, instances of
-- inference rules are obtained using Agda’s built-in notion of substitution.
--
-- 3.5.2. Definition
-- “A rule is _satisfied_ by a relation if, for each instance of the rule, either the conclusion is
-- in the relation or one of the premises is not.”
--
-- In our model, a rule is satisfied by an inductive type family if, given evidence for all of the
-- premises, a constructor of the type family serves as evidence for the conclusion.


----------------------------------------------------------------------------------------------------
--
-- 3.5.3. Definition
-- “The _one-step reduction_ relation `⟹` is the smallest binary relation on terms satisfying the
-- three rules in …”
--
-- We say `t ⟹ t′` to mean that `t` reduces to `t′` in one step.

    infix 3 _⟹_
    data _⟹_ : Rel₀ Term where
      r-ifTrue  : ∀ {t₂ t₃} → if true then t₂ else t₃ ⟹ t₂
      r-ifFalse : ∀ {t₂ t₃} → if false then t₂ else t₃ ⟹ t₃
      r-if      : ∀ {t₁ t₁′ t₂ t₃} → t₁ ⟹ t₁′ →
                  if t₁ then t₂ else t₃ ⟹ if t₁′ then t₂ else t₃


----------------------------------------------------------------------------------------------------
--
-- 3.5.4. Theorem [Determinacy of one-step reduction]
-- “If `t ⟹ t′` and `t ⟹ t″`, then `t′ = t″`.
--
-- Before we can prove this theorem, we need to jump ahead to Definition 3.5.6 and say what it
-- means for a term to be in _normal form_.  In type theory, it is often more convenient to use a
-- positive definition.  For this reason, we also define what it means for a term to be _reducible_.
-- We give both definitions in a generic manner, parametrised by the one-step reduction relation, so
-- that we can reuse them in later sections.

module NormalForms {t ℓ} {Term : Set t}
    (_⟹_ : Rel Term ℓ)
  where
    NormalForm : Pred Term (t ⊔ ℓ)
    NormalForm t = ∀ {t′} → ¬ (t ⟹ t′)

    Reducible : Pred Term (t ⊔ ℓ)
    Reducible t = ∃ λ t′ → t ⟹ t′

    nf⇒¬ρ : ∀ {t} → NormalForm t → ¬ Reducible t
    nf⇒¬ρ nf (_ , r) = r ↯ nf

    ¬ρ⇒nf : ∀ {t} → ¬ Reducible t → NormalForm t
    ¬ρ⇒nf ¬ρ r = (_ , r) ↯ ¬ρ


-- We also need to jump ahead to Theorem 3.5.7, and show that every value is in normal form.

module BooleansOnly-Part2
  where
    open BooleansOnly-Part1 public
    open NormalForms _⟹_ public

    v⇒nf : ∀ {t} → Value t → NormalForm t
    v⇒nf true  = λ ()
    v⇒nf false = λ ()

    ⟹-det : ∀ {t t′ t″} → t ⟹ t′ → t ⟹ t″ → t′ ≡ t″
    ⟹-det r-ifTrue  r-ifTrue  = refl
    ⟹-det r-ifTrue  (r-if r′) = r′ ↯ v⇒nf true
    ⟹-det r-ifFalse r-ifFalse = refl
    ⟹-det r-ifFalse (r-if r′) = r′ ↯ v⇒nf false
    ⟹-det (r-if r)  r-ifTrue  = r ↯ v⇒nf true
    ⟹-det (r-if r)  r-ifFalse = r ↯ v⇒nf false
    ⟹-det (r-if r)  (r-if r′) = (λ s₁ → if s₁ then _ else _) & ⟹-det r r′


----------------------------------------------------------------------------------------------------
--
-- 3.5.5. Exercise [⋆]
-- “Spell out the induction principle used in the preceding proof, in the style of Theorem 3.3.4.”
-- (skipped)
--
-- 3.5.6. Definition
-- “A term `t` is in _normal form_ if no evaluation rule applies to it—i.e., if there is no `t′`
-- such that `t ⟹ t′`.  (We sometimes say ‘`t` is a normal form’ as shorthand for ‘`t` is a term
-- in normal form.’)”
-- (given above)
--
-- 3.5.7. Theorem
-- “Every value is in normal form.”
-- (given above)


----------------------------------------------------------------------------------------------------
--
-- 3.5.8. Theorem
-- “If `t` is in normal form, then `t` is a value.”
--
-- To prove this theorem, we’re first going to show that every term is either a value, or reducible
-- to another term.

    data Value|Reducible : Pred₀ Term where
      val : ∀ {t} → Value t → Value|Reducible t
      red : ∀ {t} → Reducible t → Value|Reducible t

    classify : ∀ t → Value|Reducible t
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


----------------------------------------------------------------------------------------------------
--
-- 3.5.9. Definition
-- “The _multi-step reduction_ relation `⟹*` is the reflexive, transitive closure of one-step
-- reduction.  That is, it is the smallest relation such that (1) if `t ⟹ t′` then `t ⟹* t′`,
-- (2) `t ⟹* t` for all `t`, and (3) if `t ⟹* t′` and `t′ ⟹* t″`, then `t ⟹* t″`.”
--
-- We say `t ⟹* t′` to mean that `t` reduces to `t′` in multiple steps.  We give this definition
-- in a generic manner, using equipment from the Agda standard library, and we include some related
-- utilities.

module MultiStepReduction {t ℓ} {Term : Set t}
    (_⟹_ : Rel Term ℓ)
  where
    infix 3 _⟹*_
    _⟹*_ : Rel Term (t ⊔ ℓ)
    _⟹*_ = _⟹_ *

    _∷ʳ_ : ∀ {t t′ t″} → t ⟹* t′ → t′ ⟹ t″ → t ⟹* t″
    rs ∷ʳ r = rs ++ (r ∷ [])

    map : ∀ {f : Term → Term} → (∀ {t t′} → t ⟹ t′ → f t ⟹ f t′) →
          ∀ {t t′} → t ⟹* t′ → f t ⟹* f t′
    map {f = f} = Star.gmap f


----------------------------------------------------------------------------------------------------
--
-- 3.5.10. Exercise [*]
-- “Rephrase Definition 3.5.9 as a set of inference rules.”
-- (redundant)


----------------------------------------------------------------------------------------------------
--
-- 3.5.11. Theorem [Uniqueness of normal forms]
-- “If `t ⟹* u` and `t ⟹* u′`, where `u` and `u′` are both normal forms, then `u = u′`.”

module UniquenessOfNormalForms {t ℓ} {Term : Set t}
    (_⟹_ : Rel Term ℓ)
    (⟹-det : ∀ {t t′ t″} → t ⟹ t′ → t ⟹ t″ → t′ ≡ t″)
  where
    open NormalForms _⟹_
    open MultiStepReduction _⟹_

    ⟹*-unf : ∀ {t u u′} → NormalForm u → NormalForm u′ → t ⟹* u → t ⟹* u′ → u ≡ u′
    ⟹*-unf nf nf′ []       []         = refl
    ⟹*-unf nf nf′ []       (r′ ∷ rs′) = r′ ↯ nf
    ⟹*-unf nf nf′ (r ∷ rs) []         = r ↯ nf′
    ⟹*-unf nf nf′ (r ∷ rs) (r′ ∷ rs′) with ⟹-det r r′
    ... | refl                          = ⟹*-unf nf nf′ rs rs′


----------------------------------------------------------------------------------------------------
--
-- 3.5.12. Theorem [Termination of evaluation]
-- “For every term `t` there is some normal form `u` such that `t ⟹* u`.”
--
-- We first show a variant of this theorem that uses the notion of value instead of normal form.
-- We say `t ⇓ u` to mean that `t` evaluates to `u`, and `t ⇓` to mean that evaluation of `t`
-- terminates.

module BooleansOnly-Part3
  where
    open BooleansOnly-Part2 public
    open MultiStepReduction _⟹_ public
    open UniquenessOfNormalForms _⟹_ ⟹-det public

    _⇓_ : Rel₀ Term
    t ⇓ u = Value u × t ⟹* u

    _⇓ : Pred₀ Term
    t ⇓ = ∃ λ u → t ⇓ u

    halt-if : ∀ {t₁ t₂ t₃ tₙ u₁} → t₁ ⟹* u₁ → if u₁ then t₂ else t₃ ⟹ tₙ →
              tₙ ⇓ → if t₁ then t₂ else t₃ ⇓
    halt-if rs₁ rₙ (uₙ , vₙ , rsₙ) = uₙ , vₙ , (map r-if rs₁ ++ rₙ ∷ rsₙ)

    halt : ∀ t → t ⇓
    halt true                    = _ , true  , []
    halt false                   = _ , false , []
    halt (if t₁ then t₂ else t₃) with halt t₁
    ... | .true  , true  , rs₁   = halt-if rs₁ r-ifTrue (halt t₂)
    ... | .false , false , rs₁   = halt-if rs₁ r-ifFalse (halt t₃)

    halt′ : ∀ t → ∃ λ u → NormalForm u × t ⟹* u
    halt′ t          with halt t
    ... | u , v , rs = u , v⇒nf v , rs


----------------------------------------------------------------------------------------------------
--
-- 3.5.13. Exercise [Recommended, ⋆⋆]
-- “1. Suppose we add a new rule…”
-- “2. Suppose instead that we add this rule…”
-- (skipped)


----------------------------------------------------------------------------------------------------
--
-- 3.5.14. Exercise [⋆⋆]
-- ”Show that Theorem 3.5.4 is also valid for the reduction relation on arithmetic expressions:
-- if `t ⟹ t′` and `t ⟹ t″`, then `t′ = t″`.”

module NumbersAndBooleans-Part2
  where
    open NumbersAndBooleans-Part1 public

    data NumericValue : Pred₀ Term where
      zero : NumericValue zero
      suc  : ∀ {t₁} → (nv₁ : NumericValue t₁) → NumericValue (suc t₁)

    data Value : Pred₀ Term where
      true  : Value true
      false : Value false
      num   : ∀ {t₁} → (nv₁ : NumericValue t₁) → Value t₁


-- Echo of Definition 3.5.3.

    infix 3 _⟹_
    data _⟹_ : Rel₀ Term where
      r-suc        : ∀ {t₁ t₁′} → t₁ ⟹ t₁′ → suc t₁ ⟹ suc t₁′
      r-predZero   : pred zero ⟹ zero
      r-predSuc    : ∀ {t₁} → NumericValue t₁ → pred (suc t₁) ⟹ t₁
      r-pred       : ∀ {t₁ t₁′} → t₁ ⟹ t₁′ → pred t₁ ⟹ pred t₁′
      r-iszeroZero : iszero zero ⟹ true
      r-iszeroSuc  : ∀ {t₁} → NumericValue t₁ → iszero (suc t₁) ⟹ false
      r-iszero     : ∀ {t₁ t₁′} → t₁ ⟹ t₁′ → iszero t₁ ⟹ iszero t₁′
      r-ifTrue     : ∀ {t₂ t₃} → if true then t₂ else t₃ ⟹ t₂
      r-ifFalse    : ∀ {t₂ t₃} → if false then t₂ else t₃ ⟹ t₃
      r-if         : ∀ {t₁ t₁′ t₂ t₃} → t₁ ⟹ t₁′ →
                     if t₁ then t₂ else t₃ ⟹ if t₁′ then t₂ else t₃


-- Echo of Definition 3.5.6.

    open NormalForms _⟹_ public


-- Echo of Theorem 3.5.7.

    nv⇒nf : ∀ {t} → NumericValue t → NormalForm t
    nv⇒nf zero     = λ ()
    nv⇒nf (suc nv) = λ where (r-suc r) → r ↯ nv⇒nf nv

    v⇒nf : ∀ {t} → Value t → NormalForm t
    v⇒nf true     = λ ()
    v⇒nf false    = λ ()
    v⇒nf (num nv) = nv⇒nf nv


-- Echo of Theorem 3.5.4.

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
    ⟹-det (r-if r′)         (r-if r″)         = (λ t₁′ → if t₁′ then _ else _) &  ⟹-det r′ r″


----------------------------------------------------------------------------------------------------
--
-- 3.5.15. Definition
-- “A closed term is _stuck_ if it is in normal form but not a value.”
--
-- In anticipation of Exercise 3.5.16, we’re going to work towards showing that evaluation of
-- expressions-that-get-stuck is terminating.

module NumbersAndBooleansGetStuck
  where
    open NumbersAndBooleans-Part2 public

    Stuck : Pred₀ Term
    Stuck t = ¬ Value t × NormalForm t


-- Every term is either stuck, a value, or reducible to another term.

    data Stuck/Value/Reducible : Pred₀ Term where
      stu : ∀ {t} → Stuck t → Stuck/Value/Reducible t
      val : ∀ {t} → Value t → Stuck/Value/Reducible t
      red : ∀ {t} → Reducible t → Stuck/Value/Reducible t

    s-sucStuck : ∀ {t₁} → Stuck t₁ → Stuck (suc t₁)
    s-sucStuck (¬v₁ , nf₁) = (λ where (num (suc nv₁)) → num nv₁ ↯ ¬v₁)
                           , (λ where (r-suc r₁) → r₁ ↯ nf₁)

    s-sucTrue : Stuck (suc true)
    s-sucTrue = (λ where (num (suc ())))
              , (λ where (r-suc ()))

    s-sucFalse : Stuck (suc false)
    s-sucFalse = (λ where (num (suc ())))
               , (λ where (r-suc ()))

    s-predStuck : ∀ {t₁} → Stuck t₁ → Stuck (pred t₁)
    s-predStuck (¬v₁ , nf₁) = (λ where (num ()))
                            , (λ where r-predZero      → num zero ↯ ¬v₁
                                       (r-predSuc nv₁) → num (suc nv₁) ↯ ¬v₁
                                       (r-pred r₁)     → r₁ ↯ nf₁)

    s-predTrue : Stuck (pred true)
    s-predTrue = (λ where (num ()))
               , (λ where (r-pred ()))

    s-predFalse : Stuck (pred false)
    s-predFalse = (λ where (num ()))
                , (λ where (r-pred ()))

    s-iszeroStuck : ∀ {t₁} → Stuck t₁ → Stuck (iszero t₁)
    s-iszeroStuck (¬v₁ , nf₁) = (λ where (num ()))
                              , (λ where r-iszeroZero      → num zero ↯ ¬v₁
                                         (r-iszeroSuc nv₁) → num (suc nv₁) ↯ ¬v₁
                                         (r-iszero r₁)     → r₁ ↯ nf₁)

    s-iszeroTrue : Stuck (iszero true)
    s-iszeroTrue = (λ where (num ()))
                 , (λ where (r-iszero ()))

    s-iszeroFalse : Stuck (iszero false)
    s-iszeroFalse = (λ where (num ()))
                  , (λ where (r-iszero ()))

    s-ifStuck : ∀ {t₁ t₂ t₃} → Stuck t₁ → Stuck (if t₁ then t₂ else t₃)
    s-ifStuck (¬v₁ , nf₁) = (λ where (num ()))
                          , (λ where r-ifTrue  → true ↯ ¬v₁
                                     r-ifFalse → false ↯ ¬v₁
                                     (r-if r₁) → r₁ ↯ nf₁)

    s-ifZero : ∀ {t₂ t₃} → Stuck (if zero then t₂ else t₃)
    s-ifZero = (λ where (num ()))
             , (λ where (r-if ()))

    s-ifSuc : ∀ {nv₁ t₂ t₃} → NumericValue nv₁ → Stuck (if (suc nv₁) then t₂ else t₃)
    s-ifSuc nv₁ = (λ where (num ()))
                , (λ where (r-if (r-suc r₁)) → r₁ ↯ nv⇒nf nv₁)

    classify : ∀ t → Stuck/Value/Reducible t
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
    ... | stu s₁                     = stu (s-iszeroStuck s₁)
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


-- Echo of Theorem 3.5.8.

    data Stuck/Value : Pred₀ Term where
      stu : ∀ {t} → Stuck t → Stuck/Value t
      val : ∀ {t} → Value t → Stuck/Value t

    nf⇒s/v : ∀ {t} → NormalForm t → Stuck/Value t
    nf⇒s/v {t} nf    with classify t
    ... | stu s       = stu s
    ... | val v       = val v
    ... | red (_ , r) = r ↯ nf


-- Echo of Definition 3.5.9 and Theorem 3.5.11.

    open MultiStepReduction _⟹_ public
    open UniquenessOfNormalForms _⟹_ ⟹-det public


-- Equipment for showing termination.

    _⇓_ : Rel₀ Term
    t ⇓ u = Stuck/Value u × t ⟹* u

    _⇓ : Pred₀ Term
    t ⇓ = ∃ λ u → t ⇓ u

    halt-if : ∀ {t₁ t₂ t₃ tₙ u₁} → t₁ ⟹* u₁ → if u₁ then t₂ else t₃ ⟹ tₙ →
              tₙ ⇓ → if t₁ then t₂ else t₃ ⇓
    halt-if rs₁ rₙ (uₙ , vₙ , rsₙ) = uₙ , vₙ , (map r-if rs₁ ++ rₙ ∷ rsₙ)

    halt : ∀ t → t ⇓
    halt true                                  = _ , val true               , []
    halt false                                 = _ , val false              , []
    halt zero                                  = _ , val (num zero)         , []
    halt (suc t₁)                              with halt t₁
    ... | _        , stu s₁              , rs₁ = _ , stu (s-sucStuck s₁)    , map r-suc rs₁
    ... | .true    , val true            , rs₁ = _ , stu s-sucTrue          , map r-suc rs₁
    ... | .false   , val false           , rs₁ = _ , stu s-sucFalse         , map r-suc rs₁
    ... | ._       , val (num nv₁)       , rs₁ = _ , val (num (suc nv₁))    , map r-suc rs₁
    halt (pred t₁)                             with halt t₁
    ... | _        , stu s₁              , rs₁ = _ , stu (s-predStuck s₁)   , map r-pred rs₁
    ... | .true    , val true            , rs₁ = _ , stu s-predTrue         , map r-pred rs₁
    ... | .false   , val false           , rs₁ = _ , stu s-predFalse        , map r-pred rs₁
    ... | .zero    , val (num zero)      , rs₁ = _ , val (num zero)         , map r-pred rs₁ ∷ʳ r-predZero
    ... | .(suc _) , val (num (suc nv₁)) , rs₁ = _ , val (num nv₁)          , map r-pred rs₁ ∷ʳ r-predSuc nv₁
    halt (iszero t₁)                           with halt t₁
    ... | _        , stu s₁              , rs₁ = _ , stu (s-iszeroStuck s₁) , map r-iszero rs₁
    ... | .true    , val true            , rs₁ = _ , stu s-iszeroTrue       , map r-iszero rs₁
    ... | .false   , val false           , rs₁ = _ , stu s-iszeroFalse      , map r-iszero rs₁
    ... | .zero    , val (num zero)      , rs₁ = _ , val true               , map r-iszero rs₁ ∷ʳ r-iszeroZero
    ... | .(suc _) , val (num (suc nv₁)) , rs₁ = _ , val false              , map r-iszero rs₁ ∷ʳ r-iszeroSuc nv₁
    halt (if t₁ then t₂ else t₃)               with halt t₁
    ... | _        , stu s₁              , rs₁ = _ , stu (s-ifStuck s₁)     , map r-if rs₁
    ... | .true    , val true            , rs₁ = halt-if rs₁ r-ifTrue (halt t₂)
    ... | .false   , val false           , rs₁ = halt-if rs₁ r-ifFalse (halt t₃)
    ... | .zero    , val (num zero)      , rs₁ = _ , stu s-ifZero           , map r-if rs₁
    ... | .(suc _) , val (num (suc nv₁)) , rs₁ = _ , stu (s-ifSuc nv₁)      , map r-if rs₁


-- Echo of Theorem 3.5.12.

    halt′ : ∀ t → ∃ λ u → NormalForm u × t ⟹* u
    halt′ t                      with halt t
    ... | u , stu (¬v , nf) , rs = u , nf      , rs
    ... | u , val v         , rs = u , v⇒nf v , rs


----------------------------------------------------------------------------------------------------
--
-- 3.5.16. Exercise [Recommended, ⋆⋆⋆]
-- ”A different way of formalizing meaningless states of the abstract machine is to introduce a new
-- term called `wrong` and augment the operational semantics with rules that explicitly generate
-- `wrong` in all the situations where the present semantics gets stuck.  To do this in detail, …”
-- “Show that these two treatments of run-time errors agree by (1) finding a precise way of stating
-- the intuition that “the two treatments agree,” and (2) proving it.”
--
-- We’re going to start by showing that evaluation of expressions-that-go-wrong is terminating.
-- Then, we’ll show that expressions-that-go-wrong go wrong exactly when expressions-that-get-stuck
-- get stuck.  First, we echo Definition 3.2.1 and redefine terms and values.

module NumbersAndBooleansGoWrong
  where
    data Term : Set₀ where
      wrong true false zero : Term
      suc pred iszero       : (t₁ : Term) → Term
      if_then_else          : (t₁ t₂ t₃ : Term) → Term

    data NumericValue : Pred₀ Term where
      zero : NumericValue zero
      suc  : ∀ {t₁} → NumericValue t₁ → NumericValue (suc t₁)

    data Value : Pred₀ Term where
      wrong : Value wrong
      true  : Value true
      false : Value false
      num   : ∀ {t₁} → NumericValue t₁ → Value t₁

    data BadNat : Pred₀ Term where
      wrong : BadNat wrong
      true  : BadNat true
      false : BadNat false

    data BadBool : Pred₀ Term where
      wrong : BadBool wrong
      num   : ∀ {u} → NumericValue u → BadBool u


-- Echo of Definition 3.5.3.

    infix 3 _⟹_
    data _⟹_ : Rel₀ Term where
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
      r-if          : ∀ {t₁ t₁′ t₂ t₃} → t₁ ⟹ t₁′ →
                      if t₁ then t₂ else t₃ ⟹ if t₁′ then t₂ else t₃


-- Echo of Definition 3.5.6.

    open NormalForms _⟹_ public


-- Echo of Theorem 3.5.7.

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
    v⇒nf wrong    = λ ()
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


-- Echo of Theorem 3.5.4.

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
    ⟹-det (r-if r′)            (r-if r″)           = (λ t₁′ → if t₁′ then _ else _) &
                                                         ⟹-det r′ r″


-- Every term is either a value, or reducible to another term.

    data Value|Reducible : Pred₀ Term where
      val : ∀ {t} → Value t → Value|Reducible t
      red : ∀ {t} → Reducible t → Value|Reducible t

    classify : ∀ t → Value|Reducible t
    classify wrong                   = val wrong
    classify true                    = val true
    classify false                   = val false
    classify zero                    = val (num zero)
    classify (suc t₁)                with classify t₁
    ... | val wrong                  = red (wrong , r-sucWrong wrong)
    ... | val true                   = red (wrong , r-sucWrong true)
    ... | val false                  = red (wrong , r-sucWrong false)
    ... | val (num nv₁)              = val (num (suc nv₁))
    ... | red (t₁′ , r₁)             = red (suc t₁′ , r-suc r₁)
    classify (pred t₁)               with classify t₁
    ... | val wrong                  = red (wrong , r-predWrong wrong)
    ... | val true                   = red (wrong , r-predWrong true)
    ... | val false                  = red (wrong , r-predWrong false)
    ... | val (num zero)             = red (zero , r-predZero)
    ... | val (num (suc nv₁))        = red (_ , r-predSuc nv₁)
    ... | red (t₁′ , r₁)             = red (pred t₁′ , r-pred r₁)
    classify (iszero t₁)             with classify t₁
    ... | val wrong                  = red (wrong , r-iszeroWrong wrong)
    ... | val true                   = red (wrong , r-iszeroWrong true)
    ... | val false                  = red (wrong , r-iszeroWrong false)
    ... | val (num zero)             = red (true , r-iszeroZero)
    ... | val (num (suc nv₁))        = red (false , r-iszeroSuc nv₁)
    ... | red (t₁′ , r₁)             = red (iszero t₁′ , r-iszero r₁)
    classify (if t₁ then t₂ else t₃) with classify t₁
    ... | val wrong                  = red (wrong , r-ifWrong wrong)
    ... | val true                   = red (t₂ , r-ifTrue)
    ... | val false                  = red (t₃ , r-ifFalse)
    ... | val (num nv₁)              = red (wrong , r-ifWrong (num nv₁))
    ... | red (t₁′ , r₁)             = red (if t₁′ then t₂ else t₃ , r-if r₁)


-- Echo of Theorem 3.5.8.

    nf⇒v : ∀ {t} → NormalForm t → Value t
    nf⇒v {t} nf    with classify t
    ... | val v       = v
    ... | red (_ , r) = r ↯ nf


-- Echo of Definition 3.5.9 and Theorem 3.5.11.

    open MultiStepReduction _⟹_ public
    open UniquenessOfNormalForms _⟹_ ⟹-det public


-- Equipment for showing termination.

    _⇓_ : Rel₀ Term
    t ⇓ u = Value u × t ⟹* u

    _⇓ : Pred₀ Term
    t ⇓ = ∃ λ u → t ⇓ u

    halt-if : ∀ {t₁ t₂ t₃ tₙ u₁} → t₁ ⟹* u₁ → if u₁ then t₂ else t₃ ⟹ tₙ →
              tₙ ⇓ → if t₁ then t₂ else t₃ ⇓
    halt-if rs₁ rₙ (uₙ , vₙ , rsₙ) = uₙ , vₙ , (map r-if rs₁ ++ rₙ ∷ rsₙ)

    halt : ∀ t → t ⇓
    halt wrong                         = _ , wrong         , []
    halt true                          = _ , true          , []
    halt false                         = _ , false         , []
    halt zero                          = _ , num zero      , []
    halt (suc t₁)                      with halt t₁
    ... | .wrong , wrong         , rs₁ = _ , wrong         , map r-suc rs₁ ∷ʳ r-sucWrong wrong
    ... | .true  , true          , rs₁ = _ , wrong         , map r-suc rs₁ ∷ʳ r-sucWrong true
    ... | .false , false         , rs₁ = _ , wrong         , map r-suc rs₁ ∷ʳ r-sucWrong false
    ... | _      , num nv₁       , rs₁ = _ , num (suc nv₁) , map r-suc rs₁
    halt (pred t₁)                     with halt t₁
    ... | .wrong , wrong         , rs₁ = _ , wrong         , map r-pred rs₁ ∷ʳ r-predWrong wrong
    ... | .true  , true          , rs₁ = _ , wrong         , map r-pred rs₁ ∷ʳ r-predWrong true
    ... | .false , false         , rs₁ = _ , wrong         , map r-pred rs₁ ∷ʳ r-predWrong false
    ... | _      , num zero      , rs₁ = _ , num zero      , map r-pred rs₁ ∷ʳ r-predZero
    ... | _      , num (suc nv₁) , rs₁ = _ , num nv₁       , map r-pred rs₁ ∷ʳ r-predSuc nv₁
    halt (iszero t₁)                   with halt t₁
    ... | .wrong , wrong         , rs₁ = _ , wrong         , map r-iszero rs₁ ∷ʳ r-iszeroWrong wrong
    ... | .true  , true          , rs₁ = _ , wrong         , map r-iszero rs₁ ∷ʳ r-iszeroWrong true
    ... | .false , false         , rs₁ = _ , wrong         , map r-iszero rs₁ ∷ʳ r-iszeroWrong false
    ... | _      , num zero      , rs₁ = _ , true          , map r-iszero rs₁ ∷ʳ r-iszeroZero
    ... | _      , num (suc nv₁) , rs₁ = _ , false         , map r-iszero rs₁ ∷ʳ r-iszeroSuc nv₁
    halt (if t₁ then t₂ else t₃)       with halt t₁
    ... | .wrong , wrong         , rs₁ = _ , wrong         , map r-if rs₁ ∷ʳ r-ifWrong wrong
    ... | .true  , true          , rs₁ = halt-if rs₁ r-ifTrue (halt t₂)
    ... | .false , false         , rs₁ = halt-if rs₁ r-ifFalse (halt t₃)
    ... | _      , num nv₁       , rs₁ = _ , wrong         , map r-if rs₁ ∷ʳ r-ifWrong (num nv₁)


-- Echo of Theorem 3.5.12.

    halt′ : ∀ t → ∃ λ u → NormalForm u × t ⟹* u
    halt′ t          with halt t
    ... | u , v , rs = u , v⇒nf v , rs


-- TODO


----------------------------------------------------------------------------------------------------
--
-- 3.5.17. Exercise [Recommended, ***]
-- “Two styles of operational semantics are in common use. The one used in this book is called the
-- _small-step_ style, because the definition of the reduction relation shows how individual steps
-- of computation are used to rewrite a term, bit by bit, until it eventually becomes a value.
-- On top of this, we define a multi-step reduction relation that allows us to talk about terms
-- reducing (in many steps) to values.  An alternative style, called _big-step semantics_ (or
-- sometimes _natural semantics_), directly formulates the notion of “this term evaluates to that
-- final value,” written `t ⇓ v`.  The big-step evaluation rules for our language of boolean and
-- arithmetic expressions look like this: …”
-- “Show that the small-step and big-step semantics for this language coincide, i.e.
-- `t ⟹* v` iff `t ⇓ v`.”


-- TODO


----------------------------------------------------------------------------------------------------
--
-- 3.5.18 Exercise [⋆⋆ ↛]
-- “Suppose we want to change the evaluation strategy of our language so that the `then` and `else`
-- branches of an `if` expression are evaluated (in that order) _before_ the guard is evaluated.
-- Show how the reduction rules need to change to achieve this effect.”
-- (skipped)


----------------------------------------------------------------------------------------------------
--
-- 3.6 Notes


----------------------------------------------------------------------------------------------------
