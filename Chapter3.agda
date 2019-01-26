----------------------------------------------------------------------------------------------------

module Chapter3 where

open import Data.Empty public using (⊥ ; ⊥-elim)

open import Data.List public using (List ; [] ; _∷_)

import Data.Nat as Nat
open Nat public using (_≤_ ; _<_ ; _+_ ; s≤s ; suc ; zero)
  renaming (ℕ to Nat)

import Data.Nat.Properties as Nat
open Nat.≤-Reasoning public

open import Data.Product public using (_×_ ; _,_ ; Σ ; ∃ ; proj₁ ; proj₂)

open import Data.Sum public using (_⊎_ ; inj₁ ; inj₂)

open import Data.Unit public using (⊤ ; tt)

open import Function public using (case_of_)

open import Level public using (_⊔_ ; 0ℓ)

open import Relation.Binary public using (Decidable ; DecSetoid ; Reflexive ; Rel ; Transitive)

import Relation.Binary.PropositionalEquality as PropEq
open PropEq public using (_≡_ ; _≢_ ; refl ; subst)
  renaming (cong to _&_ ; sym to _⁻¹)

-- import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
-- open Star public using ()
--   renaming (Star to _* ; ε to [] ; _◅_ to _∷_ ; _◅◅_ to _++_)

open import Relation.Nullary public using (¬_ ; Dec ; no ; yes)

open import Relation.Nullary.Negation public using (contraposition)
  renaming (contradiction to _↯_)

open import Relation.Unary public using (Pred)


----------------------------------------------------------------------------------------------------
--
-- TODO: Temporary

data _* {a ℓ} {A : Set a} (R : Rel A ℓ) : Rel A (a ⊔ ℓ) where
  []  : Reflexive (R *)
  _∷_ : ∀ {x y z} → (r : R x y) (rs : (R *) y z) → (R *) x z

pattern _∷⟨_⟩_ r y rs = _∷_ {_} {y} {_} r rs

_++_ : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} → Transitive (R *)
[]       ++ rs′ = rs′
(r ∷ rs) ++ rs′ = r ∷ (rs ++ rs′)

_∷ʳ_ : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} →
       ∀ {x y z} → (R *) x y → R y z → (R *) x z
rs ∷ʳ r = rs ++ (r ∷ [])

map : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} {f : A → A} →
      (∀ {x y} → R x y → R (f x) (f y)) →
      ∀ {x y} → (R *) x y → (R *) (f x) (f y)
map h []       = []
map h (r ∷ rs) = h r ∷ map h rs

¬¬snoc : ∀ {a ℓ} {A : Set a} {R : A → A → Set ℓ} →
         ∀ {x y z} → (R *) x y → R y z → ¬ ¬ ((R *) x z)
¬¬snoc R*xy Ryz ¬R*xz = (R*xy ++ (Ryz ∷ [])) ↯ ¬R*xz

undo : ∀ {a ℓ} {A : Set a} {R : A → A → Set ℓ} →
       ∀ {x y z} → R y z → ¬ ((R *) x z) → ¬ ((R *) x y)
undo Ryz ¬R*xz R*xy = ¬¬snoc R*xy Ryz ¬R*xz


data _*′ {a ℓ} {A : Set a} (R : Rel A ℓ) : Rel A (a ⊔ ℓ) where
  []′   : Reflexive (R *′)
  _∷ʳ′_ : ∀ {x y z} → (rs : (R *′) x y) (r : R y z) → (R *′) x z

_++′_ : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} → Transitive (R *′)
rs ++′ []′          = rs
rs ++′ (rs′ ∷ʳ′ r′) = (rs ++′ rs′) ∷ʳ′ r′

_∷′_ : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} →
       ∀ {x y z} → R x y → (R *′) y z → (R *′) x z
r ∷′ rs = ([]′ ∷ʳ′ r) ++′ rs

undo′ : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} →
        ∀ {x y z} → R y z → ¬ ((R *′) x z) → ¬ ((R *′) x y)
undo′ Ryz ¬R*′xz R*′xy = (R*′xy ∷ʳ′ Ryz) ↯ ¬R*′xz


*→*′ : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} →
        ∀ {x y} → (R *) x y → (R *′) x y
*→*′ []       = []′
*→*′ (r ∷ rs) = r ∷′ *→*′ rs

*′→* : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} →
        ∀ {x y} → (R *′) x y → (R *) x y
*′→* []′        = []
*′→* (rs ∷ʳ′ r) = *′→* rs ∷ʳ r


----------------------------------------------------------------------------------------------------
--
-- TODO: Clean this up

_↔_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
A ↔ B = (A → B) × (B → A)

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
      suc pred iszero : (t : Term) → Term
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
    true                  ≟ suc _                 = no λ ()
    true                  ≟ pred _                = no λ ()
    true                  ≟ iszero _              = no λ ()
    true                  ≟ if _ then _ else _    = no λ ()
    false                 ≟ true                  = no λ ()
    false                 ≟ false                 = yes refl
    false                 ≟ zero                  = no λ ()
    false                 ≟ suc _                 = no λ ()
    false                 ≟ pred _                = no λ ()
    false                 ≟ iszero _              = no λ ()
    false                 ≟ if _ then _ else _    = no λ ()
    zero                  ≟ true                  = no λ ()
    zero                  ≟ false                 = no λ ()
    zero                  ≟ zero                  = yes refl
    zero                  ≟ suc _                 = no λ ()
    zero                  ≟ pred _                = no λ ()
    zero                  ≟ iszero _              = no λ ()
    zero                  ≟ if _ then _ else _    = no λ ()
    suc _                 ≟ true                  = no λ ()
    suc _                 ≟ false                 = no λ ()
    suc _                 ≟ zero                  = no λ ()
    suc s                 ≟ suc t                 with s ≟ t
    ... | yes refl                                = yes refl
    ... | no s≢t                                  = no λ where refl → refl ↯ s≢t
    suc _                 ≟ pred _                = no λ ()
    suc _                 ≟ iszero _              = no λ ()
    suc _                 ≟ if _ then _ else _    = no λ ()
    pred _                ≟ true                  = no λ ()
    pred _                ≟ false                 = no λ ()
    pred _                ≟ zero                  = no λ ()
    pred _                ≟ suc _                 = no λ ()
    pred s                ≟ pred t                with s ≟ t
    ... | yes refl                                = yes refl
    ... | no s≢t                                  = no λ where refl → refl ↯ s≢t
    pred _                ≟ iszero _              = no λ ()
    pred _                ≟ if _ then _ else _    = no λ ()
    iszero _              ≟ true                  = no λ ()
    iszero _              ≟ false                 = no λ ()
    iszero _              ≟ zero                  = no λ ()
    iszero _              ≟ suc _                 = no λ ()
    iszero _              ≟ pred _                = no λ ()
    iszero s              ≟ iszero t              with s ≟ t
    ... | yes refl                                = yes refl
    ... | no s≢t                                  = no λ where refl → refl ↯ s≢t
    iszero _              ≟ if _ then _ else _    = no λ ()
    if _ then _ else _    ≟ true                  = no λ ()
    if _ then _ else _    ≟ false                 = no λ ()
    if _ then _ else _    ≟ zero                  = no λ ()
    if _ then _ else _    ≟ suc _                 = no λ ()
    if _ then _ else _    ≟ pred _                = no λ ()
    if _ then _ else _    ≟ iszero _              = no λ ()
    if s₁ then s₂ else s₃ ≟ if t₁ then t₂ else t₃ with s₁ ≟ t₁ | s₂ ≟ t₂ | s₃ ≟ t₃
    ... | no s₁≢t₁ | _        | _                 = no λ where refl → refl ↯ s₁≢t₁
    ... | yes refl | no s₂≢t₂ | _                 = no λ where refl → refl ↯ s₂≢t₂
    ... | yes refl | yes refl | no s₃≢t₃          = no λ where refl → refl ↯ s₃≢t₃
    ... | yes refl | yes refl | yes refl          = yes refl

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
    consts (suc t)                 = consts t
    consts (pred t)                = consts t
    consts (iszero t)              = consts t
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
    size (suc t)                 = 1 + size t
    size (pred t)                = 1 + size t
    size (iszero t)              = 1 + size t
    size (if t₁ then t₂ else t₃) = 1 + (size t₁ + size t₂ + size t₃)

    depth : Term → Nat
    depth true                    = 1
    depth false                   = 1
    depth zero                    = 1
    depth (suc t)                 = 1 + depth t
    depth (pred t)                = 1 + depth t
    depth (iszero t)              = 1 + depth t
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
        lem-333 : ∀ t → length (consts t) ≤ size t
        lem-333 true                    = Nat.≤-refl
        lem-333 false                   = Nat.≤-refl
        lem-333 zero                    = Nat.≤-refl
        lem-333 (suc t)                 = Nat.≤-step (lem-333 t)
        lem-333 (pred t)                = Nat.≤-step (lem-333 t)
        lem-333 (iszero t)              = Nat.≤-step (lem-333 t)
        lem-333 (if t₁ then t₂ else t₃) = Nat.≤-step
          (begin
            length (consts t₁ ∪ consts t₂ ∪ consts t₃)
          ≤⟨ length-triangular (consts t₁ ∪ consts t₂) (consts t₃) ⟩
            length (consts t₁ ∪ consts t₂) + length (consts t₃)
          ≤⟨ Nat.+-monoˡ-≤ (length (consts t₃)) (length-triangular (consts t₁) (consts t₂)) ⟩
            length (consts t₁) + length (consts t₂) + length (consts t₃)
          ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (lem-333 t₁) (lem-333 t₂)) (lem-333 t₃) ⟩
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

    data _∈_ : Rel₀ Term where
      suc    : ∀ {t} → t ∈ suc t
      pred   : ∀ {t} → t ∈ pred t
      iszero : ∀ {t} → t ∈ iszero t
      if₁    : ∀ {t₁ t₂ t₃} → t₁ ∈ if t₁ then t₂ else t₃
      if₂    : ∀ {t₁ t₂ t₃} → t₂ ∈ if t₁ then t₂ else t₃
      if₃    : ∀ {t₁ t₂ t₃} → t₃ ∈ if t₁ then t₂ else t₃


-- As an exercise, we’re going to define structural induction using three methods.  First, a direct
-- definition using pattern matching.

    module Ind-Struct-Direct
      where
        ind-struct : ∀ {ℓ} {P : Pred Term ℓ} → (∀ t → (∀ s →  s ∈ t → P s) → P t) →
                     ∀ t → P t
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

    module Ind-Struct-Stdlib
      where
        import Induction.WellFounded as Stdlib

        ∈-wf : Stdlib.WellFounded _∈_
        ∈-wf s = Stdlib.acc λ where
          t suc    → ∈-wf t
          t pred   → ∈-wf t
          t iszero → ∈-wf t
          t₁ if₁   → ∈-wf t₁
          t₂ if₂   → ∈-wf t₂
          t₃ if₃   → ∈-wf t₃

        module ∈-All {ℓ} = Stdlib.All ∈-wf ℓ

        ind-struct : ∀ {ℓ} {P : Pred Term ℓ} → (∀ t → (∀ s → s ∈ t → P s) → P t) →
                     ∀ t → P t
        ind-struct {P = P} = ∈-All.wfRec P


-- Third, a definition using our own equipment.  We’d like to think that our phrasing of the
-- concepts involved is a little easier to understand, while being no less general.

    open import Prelude-WellFounded public

    ∈-wf : WellFounded _∈_
    ∈-wf s = access s λ where
      t suc    → ∈-wf t
      t pred   → ∈-wf t
      t iszero → ∈-wf t
      t₁ if₁   → ∈-wf t₁
      t₂ if₂   → ∈-wf t₂
      t₃ if₃   → ∈-wf t₃

    ind-struct : ∀ {ℓ} {P : Pred Term ℓ} → InductionPrinciple _∈_ P
    ind-struct = inductionPrinciple ∈-wf


-- A proof of Lemma 3.3.3 using structural induction.

    module Lemma333-Ind-Struct
      where
        lem-333 : ∀ t → length (consts t) ≤ size t
        lem-333 = ind-struct λ where
          true                    h → Nat.≤-refl
          false                   h → Nat.≤-refl
          zero                    h → Nat.≤-refl
          (suc t)                 h → Nat.≤-step (h t suc)
          (pred t)                h → Nat.≤-step (h t pred)
          (iszero t)              h → Nat.≤-step (h t iszero)
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

    module Lemma333-Ind-Size
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

        lem-333 : ∀ t → length (consts t) ≤ size t
        lem-333 = ind-size λ where
          true                    h → Nat.≤-refl
          false                   h → Nat.≤-refl
          zero                    h → Nat.≤-refl
          (suc t)                 h → Nat.≤-step (h t Nat.≤-refl)
          (pred t)                h → Nat.≤-step (h t Nat.≤-refl)
          (iszero t)              h → Nat.≤-step (h t Nat.≤-refl)
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

    module Lemma333-Ind-Depth
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

        lem-333 : ∀ t → length (consts t) ≤ size t
        lem-333 = ind-depth λ where
          true                    h → Nat.≤-refl
          false                   h → Nat.≤-refl
          zero                    h → Nat.≤-refl
          (suc t)                 h → Nat.≤-step (h t Nat.≤-refl)
          (pred t)                h → Nat.≤-step (h t Nat.≤-refl)
          (iszero t)              h → Nat.≤-step (h t Nat.≤-refl)
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
-- We say `t ⟹ u` to mean that `t` reduces to `u` in one step.

    infix 3 _⟹_
    data _⟹_ : Rel₀ Term where
      r-ifTrue  : ∀ {t₂ t₃} → if true then t₂ else t₃ ⟹ t₂
      r-ifFalse : ∀ {t₂ t₃} → if false then t₂ else t₃ ⟹ t₃
      r-if      : ∀ {t₁ t₂ t₃ u₁} → (t₁⟹u₁ : t₁ ⟹ u₁) → if t₁ then t₂ else t₃ ⟹ if u₁ then t₂ else t₃


----------------------------------------------------------------------------------------------------
--
-- 3.5.4. Theorem [Determinacy of one-step reduction]
-- “If `t ⟹ u` and `t ⟹ u′`, then `u ≡ u′`.
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
    NormalForm t = ∀ {u} → ¬ (t ⟹ u)

    Reducible : Pred Term (t ⊔ ℓ)
    Reducible t = ∃ λ u → t ⟹ u

    nf→¬ρ : ∀ {t} → NormalForm t → ¬ Reducible t
    nf→¬ρ nfₜ (_ , t⟹u) = t⟹u ↯ nfₜ

    ¬ρ→nf : ∀ {t} → ¬ Reducible t → NormalForm t
    ¬ρ→nf ¬ρₜ t⟹u = (_ , t⟹u) ↯ ¬ρₜ


-- We also need to jump ahead to Theorem 3.5.7, and show that every value is in normal form.

module BooleansOnly-Part2
  where
    open BooleansOnly-Part1 public
    open NormalForms _⟹_ public

    v→nf : ∀ {t} → Value t → NormalForm t
    v→nf true  = λ ()
    v→nf false = λ ()

    ⟹-det : ∀ {t u u′} → t ⟹ u → t ⟹ u′ → u ≡ u′
    ⟹-det r-ifTrue          r-ifTrue           = refl
    ⟹-det r-ifTrue          (r-if true⟹u₁′)  = true⟹u₁′ ↯ v→nf true
    ⟹-det r-ifFalse         r-ifFalse          = refl
    ⟹-det r-ifFalse         (r-if false⟹u₁′) = false⟹u₁′ ↯ v→nf false
    ⟹-det (r-if true⟹u₁)  r-ifTrue           = true⟹u₁ ↯ v→nf true
    ⟹-det (r-if false⟹u₁) r-ifFalse          = false⟹u₁ ↯ v→nf false
    ⟹-det (r-if t₁⟹u₁)    (r-if t₁⟹u₁′)    = (λ u₁″ → if u₁″ then _ else _) & ⟹-det t₁⟹u₁ t₁⟹u₁′


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

    data Value/Reducible : Pred₀ Term where
      val : ∀ {t} → (vₜ : Value t) → Value/Reducible t
      red : ∀ {t} → (ρₜ : Reducible t) → Value/Reducible t

    classify : ∀ t → Value/Reducible t
    classify true                    = val true
    classify false                   = val false
    classify (if t₁ then t₂ else t₃) with classify t₁
    ... | val true                   = red (_ , r-ifTrue)
    ... | val false                  = red (_ , r-ifFalse)
    ... | red (_ , t₁⟹u₁)          = red (_ , r-if t₁⟹u₁)

    nf→v : ∀ {t} → NormalForm t → Value t
    nf→v {t} nfₜ         with classify t
    ... | val vₜ          = vₜ
    ... | red (_ , t⟹u) = t⟹u ↯ nfₜ


----------------------------------------------------------------------------------------------------
--
-- 3.5.9. Definition
-- “The _multi-step reduction_ relation `⟹*` is the reflexive, transitive closure of one-step
-- reduction.  That is, it is the smallest relation such that (1) if `t ⟹ u` then `t ⟹* u`,
-- (2) `t ⟹* t` for all `t`, and (3) if `s ⟹* t` and `t ⟹* u`, then `s ⟹* u`.”
--
-- We say `t ⟹* u` to mean that `t` reduces to `u` in multiple steps.  We give this definition
-- in a generic manner, and we include an alternative definition with a dual structure.

module MultiStepReduction {a ℓ} {A : Set a}
    (_⟹_ : Rel A ℓ)
  where
    infix 3 _⟹*_
    _⟹*_ : Rel A (a ⊔ ℓ)
    _⟹*_ = _⟹_ *


-- TODO: Is this used?

    infix 3 _⟹*′_
    _⟹*′_ : Rel A (a ⊔ ℓ)
    _⟹*′_ = _⟹_ *′


----------------------------------------------------------------------------------------------------
--
-- 3.5.10. Exercise [*]
-- “Rephrase Definition 3.5.9 as a set of inference rules.”
-- (redundant)


----------------------------------------------------------------------------------------------------
--
-- 3.5.11. Theorem [Uniqueness of normal forms]
-- “If `t ⟹* u` and `t ⟹* u′`, where `u` and `u′` are both normal forms, then `u ≡ u′`.”

module UniquenessOfNormalForms {a ℓ} {A : Set a}
    (_⟹_ : Rel A ℓ)
    (⟹-det : ∀ {t u u′} → t ⟹ u → t ⟹ u′ → u ≡ u′)
  where
    open NormalForms _⟹_
    open MultiStepReduction _⟹_

    {-# DISPLAY _* _⟹_ = _⟹*_ #-}
    {-# DISPLAY _*′ _⟹_ = _⟹*′_ #-}

    ⟹*-unf : ∀ {t u u′} → NormalForm u → NormalForm u′ → t ⟹* u → t ⟹* u′ → u ≡ u′
    ⟹*-unf nfₜ nfₜ′ []               []                  = refl
    ⟹*-unf nfₜ nfᵤ′ []               (t⟹j′ ∷ j′⟹*u′) = t⟹j′ ↯ nfₜ
    ⟹*-unf nfᵤ nfₜ  (t⟹j ∷ j⟹*u) []                  = t⟹j ↯ nfₜ
    ⟹*-unf nfᵤ nfᵤ′ (t⟹j ∷ j⟹*u) (t⟹j′ ∷ j′⟹*u′) with ⟹-det t⟹j t⟹j′
    ... | refl                                             = ⟹*-unf nfᵤ nfᵤ′ j⟹*u j′⟹*u′


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

    halt : ∀ t → t ⇓
    halt true                     = _ , true , []
    halt false                    = _ , false , []
    halt (if t₁ then t₂ else t₃)  with halt t₁ | halt t₂ | halt t₃
    ... | _ , true  , t₁⟹*true  | _ , vᵤ₂ , t₂⟹*u₂ | _ = _ , vᵤ₂ , (map r-if t₁⟹*true) ++ (r-ifTrue ∷ t₂⟹*u₂)
    ... | _ , false , t₁⟹*false | _ | _ , vᵤ₃ , t₃⟹*u₃ = _ , vᵤ₃ , (map r-if t₁⟹*false) ++ (r-ifFalse ∷ t₃⟹*u₃)

    halt′ : ∀ t → ∃ λ u → NormalForm u × t ⟹* u
    halt′ t               with halt t
    ... | _ , vᵤ , t⟹*u = _ , v→nf vᵤ , t⟹*u


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
-- if `t ⟹ u` and `t ⟹ u′`, then `u ≡ u′`.”

module NumbersAndBooleans-Part2
  where
    open NumbersAndBooleans-Part1 public

    data NumericValue : Pred₀ Term where
      zero : NumericValue zero
      suc  : ∀ {t} → (nvₜ : NumericValue t) → NumericValue (suc t)

    data Value : Pred₀ Term where
      true  : Value true
      false : Value false
      num   : ∀ {t} → (nvₜ : NumericValue t) → Value t


-- Echo of Definition 3.5.3.

    infix 3 _⟹_
    data _⟹_ : Rel₀ Term where
      r-suc        : ∀ {t u} → (t⟹u : t ⟹ u) → suc t ⟹ suc u
      r-predZero   : pred zero ⟹ zero
      r-predSuc    : ∀ {t} → (nvₜ : NumericValue t) → pred (suc t) ⟹ t
      r-pred       : ∀ {t u} → (t⟹u : t ⟹ u) → pred t ⟹ pred u
      r-iszeroZero : iszero zero ⟹ true
      r-iszeroSuc  : ∀ {t} → (nvₜ : NumericValue t) → iszero (suc t) ⟹ false
      r-iszero     : ∀ {t u} → (t⟹u : t ⟹ u) → iszero t ⟹ iszero u
      r-ifTrue     : ∀ {t₂ t₃} → if true then t₂ else t₃ ⟹ t₂
      r-ifFalse    : ∀ {t₂ t₃} → if false then t₂ else t₃ ⟹ t₃
      r-if         : ∀ {t₁ t₂ t₃ u₁} → (t₁⟹u₁ : t₁ ⟹ u₁) → if t₁ then t₂ else t₃ ⟹ if u₁ then t₂ else t₃


-- Echo of Definition 3.5.6.

    open NormalForms _⟹_ public


-- Echo of Theorem 3.5.7.

    nv→nf : ∀ {t} → NumericValue t → NormalForm t
    nv→nf zero      = λ ()
    nv→nf (suc nvₜ) = λ where (r-suc t⟹u) → t⟹u ↯ nv→nf nvₜ

    v→nf : ∀ {t} → Value t → NormalForm t
    v→nf true      = λ ()
    v→nf false     = λ ()
    v→nf (num nvₜ) = nv→nf nvₜ


-- Echo of Theorem 3.5.4.

    ⟹-det : ∀ {t u u′} → t ⟹ u → t ⟹ u′ → u ≡ u′
    ⟹-det (r-suc t⟹u)       (r-suc t⟹u′)       = suc & ⟹-det t⟹u t⟹u′
    ⟹-det r-predZero          r-predZero           = refl
    ⟹-det r-predZero          (r-pred zero⟹u′)   = zero⟹u′ ↯ nv→nf zero
    ⟹-det (r-predSuc _)       (r-predSuc _)        = refl
    ⟹-det (r-predSuc nvₜ)     (r-pred suct⟹u′)   = suct⟹u′ ↯ nv→nf (suc nvₜ)
    ⟹-det (r-pred zero⟹u)   r-predZero           = zero⟹u ↯ nv→nf zero
    ⟹-det (r-pred suct⟹u)   (r-predSuc nvₜ)      = suct⟹u ↯ nv→nf (suc nvₜ)
    ⟹-det (r-pred t⟹u)      (r-pred t⟹u′)      = pred & ⟹-det t⟹u t⟹u′
    ⟹-det r-iszeroZero        r-iszeroZero         = refl
    ⟹-det r-iszeroZero        (r-iszero zero⟹u′) = zero⟹u′ ↯ nv→nf zero
    ⟹-det (r-iszeroSuc _)     (r-iszeroSuc _)      = refl
    ⟹-det (r-iszeroSuc nvₜ)   (r-iszero suct⟹u′) = suct⟹u′ ↯ nv→nf (suc nvₜ)
    ⟹-det (r-iszero zero⟹u) r-iszeroZero         = zero⟹u ↯ nv→nf zero
    ⟹-det (r-iszero suct⟹u) (r-iszeroSuc nvₜ)    = suct⟹u ↯ nv→nf (suc nvₜ)
    ⟹-det (r-iszero t⟹u)    (r-iszero t⟹u′)    = iszero & ⟹-det t⟹u t⟹u′
    ⟹-det r-ifTrue            r-ifTrue             = refl
    ⟹-det r-ifTrue            (r-if true⟹u₁′)    = true⟹u₁′ ↯ v→nf true
    ⟹-det r-ifFalse           r-ifFalse            = refl
    ⟹-det r-ifFalse           (r-if false⟹u₁′)   = false⟹u₁′ ↯ v→nf false
    ⟹-det (r-if true⟹u₁)    r-ifTrue             = true⟹u₁ ↯ v→nf true
    ⟹-det (r-if false⟹u₁)   r-ifFalse            = false⟹u₁ ↯ v→nf false
    ⟹-det (r-if t₁⟹u₁)      (r-if t₁⟹u₁′)      = (λ u₁″ → if u₁″ then _ else _) & ⟹-det t₁⟹u₁ t₁⟹u₁′


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
      stu : ∀ {t} → (σₜ : Stuck t) → Stuck/Value/Reducible t
      val : ∀ {t} → (vₜ : Value t) → Stuck/Value/Reducible t
      red : ∀ {t} → (ρₜ : Reducible t) → Stuck/Value/Reducible t

    σ-suc : ∀ {t} → Stuck t → Stuck (suc t)
    σ-suc (¬vₜ , nfₜ) = (λ where (num (suc nvₜ)) → num nvₜ ↯ ¬vₜ)
                      , (λ where (r-suc t⟹u) → t⟹u ↯ nfₜ)

    σ-sucTrue : Stuck (suc true)
    σ-sucTrue = (λ where (num (suc ())))
              , (λ where (r-suc ()))

    σ-sucFalse : Stuck (suc false)
    σ-sucFalse = (λ where (num (suc ())))
               , (λ where (r-suc ()))

    σ-pred : ∀ {t} → Stuck t → Stuck (pred t)
    σ-pred (¬vₜ , nfₜ) = (λ where (num ()))
                       , (λ where r-predZero      → num zero ↯ ¬vₜ
                                  (r-predSuc nvₜ) → num (suc nvₜ) ↯ ¬vₜ
                                  (r-pred t⟹u)  → t⟹u ↯ nfₜ)

    σ-predTrue : Stuck (pred true)
    σ-predTrue = (λ where (num ()))
               , (λ where (r-pred ()))

    σ-predFalse : Stuck (pred false)
    σ-predFalse = (λ where (num ()))
                , (λ where (r-pred ()))

    σ-iszero : ∀ {t} → Stuck t → Stuck (iszero t)
    σ-iszero (¬vₜ , nfₜ) = (λ where (num ()))
                         , (λ where r-iszeroZero      → num zero ↯ ¬vₜ
                                    (r-iszeroSuc nvₜ) → num (suc nvₜ) ↯ ¬vₜ
                                    (r-iszero t⟹u)  → t⟹u ↯ nfₜ)

    σ-iszeroTrue : Stuck (iszero true)
    σ-iszeroTrue = (λ where (num ()))
                 , (λ where (r-iszero ()))

    σ-iszeroFalse : Stuck (iszero false)
    σ-iszeroFalse = (λ where (num ()))
                  , (λ where (r-iszero ()))

    σ-if : ∀ {t₁ t₂ t₃} → Stuck t₁ → Stuck (if t₁ then t₂ else t₃)
    σ-if (¬vₜ₁ , nfₜ₁) = (λ where (num ()))
                       , (λ where r-ifTrue       → true ↯ ¬vₜ₁
                                  r-ifFalse      → false ↯ ¬vₜ₁
                                  (r-if t₁⟹u₁) → t₁⟹u₁ ↯ nfₜ₁)

    σ-ifZero : ∀ {t₂ t₃} → Stuck (if zero then t₂ else t₃)
    σ-ifZero = (λ where (num ()))
             , (λ where (r-if ()))

    σ-ifSuc : ∀ {t₁ t₂ t₃} → NumericValue t₁ → Stuck (if (suc t₁) then t₂ else t₃)
    σ-ifSuc nvₜ₁ = (λ where (num ()))
                 , (λ where (r-if (r-suc t₁⟹u₁)) → t₁⟹u₁ ↯ nv→nf nvₜ₁)

    classify : ∀ t → Stuck/Value/Reducible t
    classify true                    = val true
    classify false                   = val false
    classify zero                    = val (num zero)
    classify (suc t)                 with classify t
    ... | stu σₜ                     = stu (σ-suc σₜ)
    ... | val true                   = stu σ-sucTrue
    ... | val false                  = stu σ-sucFalse
    ... | val (num nvₜ)              = val (num (suc nvₜ))
    ... | red (_ , t⟹u)            = red (_ , r-suc t⟹u)
    classify (pred t)                with classify t
    ... | stu σₜ                     = stu (σ-pred σₜ)
    ... | val true                   = stu σ-predTrue
    ... | val false                  = stu σ-predFalse
    ... | val (num zero)             = red (_ , r-predZero)
    ... | val (num (suc nvₜ))        = red (_ , r-predSuc nvₜ)
    ... | red (_ , t⟹u)            = red (_ , r-pred t⟹u)
    classify (iszero t)              with classify t
    ... | stu σₜ                      = stu (σ-iszero σₜ)
    ... | val true                   = stu σ-iszeroTrue
    ... | val false                  = stu σ-iszeroFalse
    ... | val (num zero)             = red (_ , r-iszeroZero)
    ... | val (num (suc nvₜ))        = red (_ , r-iszeroSuc nvₜ)
    ... | red (_ , t⟹u)            = red (_ , r-iszero t⟹u)
    classify (if t₁ then t₂ else t₃) with classify t₁
    ... | stu σₜ₁                    = stu (σ-if σₜ₁)
    ... | val true                   = red (_ , r-ifTrue)
    ... | val false                  = red (_ , r-ifFalse)
    ... | val (num zero)             = stu σ-ifZero
    ... | val (num (suc nvₜ₁))       = stu (σ-ifSuc nvₜ₁)
    ... | red (_ , t₁⟹u₁)          = red (_ , r-if t₁⟹u₁)


-- Echo of Theorem 3.5.8.

    data Stuck/Value : Pred₀ Term where
      stu : ∀ {t} → (σₜ : Stuck t) → Stuck/Value t
      val : ∀ {t} → (vₜ : Value t) → Stuck/Value t

    nf→σ/v : ∀ {t} → NormalForm t → Stuck/Value t
    nf→σ/v {t} nfₜ       with classify t
    ... | stu σₜ          = stu σₜ
    ... | val vₜ          = val vₜ
    ... | red (_ , t⟹u) = t⟹u ↯ nfₜ


-- Echo of Definition 3.5.9 and Theorem 3.5.11.

    open MultiStepReduction _⟹_ public
    open UniquenessOfNormalForms _⟹_ ⟹-det public

    {-# DISPLAY _* _⟹_ = _⟹*_ #-}
    {-# DISPLAY _*′ _⟹_ = _⟹*′_ #-}


-- Equipment for showing termination.

    _⇓_ : Rel₀ Term
    t ⇓ u = Stuck/Value u × t ⟹* u

    _⇓ : Pred₀ Term
    t ⇓ = ∃ λ u → t ⇓ u

    halt : ∀ t → t ⇓
    halt true                                    = _ , val true , []
    halt false                                   = _ , val false , []
    halt zero                                    = _ , val (num zero) , []
    halt (suc t)                                 with halt t
    ... | _ , stu σᵤ               , t⟹*u      = _ , stu (σ-suc σᵤ) , map r-suc t⟹*u
    ... | _ , val true             , t⟹*true   = _ , stu σ-sucTrue , map r-suc t⟹*true
    ... | _ , val false            , t⟹*false  = _ , stu σ-sucFalse , map r-suc t⟹*false
    ... | _ , val (num nvᵤ)        , t⟹*u      = _ , val (num (suc nvᵤ)) , map r-suc t⟹*u
    halt (pred t)                                with halt t
    ... | _ , stu σᵤ               , t⟹*u      = _ , stu (σ-pred σᵤ) , map r-pred t⟹*u
    ... | _ , val true             , t⟹*true   = _ , stu σ-predTrue , map r-pred t⟹*true
    ... | _ , val false            , t⟹*false  = _ , stu σ-predFalse , map r-pred t⟹*false
    ... | _ , val (num zero)       , t⟹*zero   = _ , val (num zero) , map r-pred t⟹*zero ∷ʳ r-predZero
    ... | _ , val (num (suc nvᵤ))  , t⟹*sucu   = _ , val (num nvᵤ) , map r-pred t⟹*sucu ∷ʳ r-predSuc nvᵤ
    halt (iszero t)                              with halt t
    ... | _ , stu σᵤ               , t⟹*u      = _ , stu (σ-iszero σᵤ) , map r-iszero t⟹*u
    ... | _ , val true             , t⟹*true   = _ , stu σ-iszeroTrue , map r-iszero t⟹*true
    ... | _ , val false            , t⟹*false  = _ , stu σ-iszeroFalse , map r-iszero t⟹*false
    ... | _ , val (num zero)       , t⟹*zero   = _ , val true , map r-iszero t⟹*zero ∷ʳ r-iszeroZero
    ... | _ , val (num (suc nvᵤ))  , t⟹*sucu   = _ , val false , map r-iszero t⟹*sucu ∷ʳ r-iszeroSuc nvᵤ
    halt (if t₁ then t₂ else t₃)                 with halt t₁ | halt t₂ | halt t₃
    ... | _ , stu σᵤ₁              , t₁⟹*u₁    | _ | _                    = _ , stu (σ-if σᵤ₁) , map r-if t₁⟹*u₁
    ... | _ , val true             , t₁⟹*true  | _ , σ/vᵤ₂ , t₂⟹*u₂ | _ = _ , σ/vᵤ₂ , (map r-if t₁⟹*true) ++ (r-ifTrue ∷ t₂⟹*u₂)
    ... | _ , val false            , t₁⟹*false | _ | _ , σ/vᵤ₃ , t₃⟹*u₃ = _ , σ/vᵤ₃ , (map r-if t₁⟹*false) ++ (r-ifFalse ∷ t₃⟹*u₃)
    ... | _ , val (num zero)       , t₁⟹*zero  | _ | _                    = _ , stu σ-ifZero , map r-if t₁⟹*zero
    ... | _ , val (num (suc nvᵤ₁)) , t₁⟹*sucu  | _ | _                    = _ , stu (σ-ifSuc nvᵤ₁) , map r-if t₁⟹*sucu


-- Echo of Theorem 3.5.12.

    halt′ : ∀ t → ∃ λ u → NormalForm u × t ⟹* u
    halt′ t                          with halt t
    ... | _ , stu (_ , nfᵤ) , t⟹*u = _ , nfᵤ      , t⟹*u
    ... | _ , val vᵤ        , t⟹*u = _ , v→nf vᵤ , t⟹*u


-- TODO: Is this used?

    _∈*_ : Rel₀ Term
    _∈*_ = _∈_ *

    _∈*′_ : Rel₀ Term
    _∈*′_ = _∈_ *′


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

module NumbersAndBooleansGoWrong-Part1
  where
    data Term : Set₀ where
      wrong true false zero : Term
      suc pred iszero       : (t : Term) → Term
      if_then_else          : (t₁ t₂ t₃ : Term) → Term

    data NumericValue : Pred₀ Term where
      zero : NumericValue zero
      suc  : ∀ {t} → (nvₜ : NumericValue t) → NumericValue (suc t)

    data Value : Pred₀ Term where
      wrong : Value wrong
      true  : Value true
      false : Value false
      num   : ∀ {t} → (nvₜ : NumericValue t) → Value t

    data BadNat : Pred₀ Term where
      wrong : BadNat wrong
      true  : BadNat true
      false : BadNat false

    data BadBool : Pred₀ Term where
      wrong : BadBool wrong
      num   : ∀ {t} → (nvₜ : NumericValue t) → BadBool t


-- Echo of Definition 3.5.3.

    infix 3 _⟹_
    data _⟹_ : Rel₀ Term where
      r-sucWrong    : ∀ {t} → (bnₜ : BadNat t) → suc t ⟹ wrong
      r-suc         : ∀ {t u} → (t⟹u : t ⟹ u) → suc t ⟹ suc u
      r-predWrong   : ∀ {t} → (bnₜ : BadNat t) → pred t ⟹ wrong
      r-predZero    : pred zero ⟹ zero
      r-predSuc     : ∀ {t} → (nvₜ : NumericValue t) → pred (suc t) ⟹ t
      r-pred        : ∀ {t u} → (t⟹u : t ⟹ u) → pred t ⟹ pred u
      r-iszeroWrong : ∀ {t} → (bnₜ : BadNat t) → iszero t ⟹ wrong
      r-iszeroZero  : iszero zero ⟹ true
      r-iszeroSuc   : ∀ {t} → (nvₜ : NumericValue t) → iszero (suc t) ⟹ false
      r-iszero      : ∀ {t u} → (t⟹u : t ⟹ u) → iszero t ⟹ iszero u
      r-ifWrong     : ∀ {t₁ t₂ t₃} → (bbₜ₁ : BadBool t₁) → if t₁ then t₂ else t₃ ⟹ wrong
      r-ifTrue      : ∀ {t₂ t₃} → if true then t₂ else t₃ ⟹ t₂
      r-ifFalse     : ∀ {t₂ t₃} → if false then t₂ else t₃ ⟹ t₃
      r-if          : ∀ {t₁ t₂ t₃ u₁} → (t₁⟹u₁ : t₁ ⟹ u₁) → if t₁ then t₂ else t₃ ⟹ if u₁ then t₂ else t₃


-- Echo of Definition 3.5.6.

    open NormalForms _⟹_ public


-- Echo of Theorem 3.5.7.

    bn→¬nv : ∀ {t} → BadNat t → ¬ NumericValue t
    bn→¬nv wrong = λ ()
    bn→¬nv true  = λ ()
    bn→¬nv false = λ ()

    nv→nf : ∀ {t} → NumericValue t → NormalForm t
    nv→nf zero      = λ ()
    nv→nf (suc nvₜ) = λ where
      (r-sucWrong bnₜ) → nvₜ ↯ bn→¬nv bnₜ
      (r-suc t⟹u)    → t⟹u ↯ nv→nf nvₜ

    v→nf : ∀ {t} → Value t → NormalForm t
    v→nf wrong     = λ ()
    v→nf true      = λ ()
    v→nf false     = λ ()
    v→nf (num nvₜ) = nv→nf nvₜ

    bn→nf : ∀ {t} → BadNat t → NormalForm t
    bn→nf wrong = λ ()
    bn→nf true  = λ ()
    bn→nf false = λ ()

    bb→nf : ∀ {t} → BadBool t → NormalForm t
    bb→nf wrong     = λ ()
    bb→nf (num nvₜ) = nv→nf nvₜ


-- Echo of Theorem 3.5.4.  Also Lemma A.3.

    ⟹-det : ∀ {t u u′} → t ⟹ u → t ⟹ u′ → u ≡ u′
    ⟹-det (r-sucWrong _)       (r-sucWrong _)       = refl
    ⟹-det (r-sucWrong bnₜ)     (r-suc t⟹u′)       = t⟹u′ ↯ bn→nf bnₜ
    ⟹-det (r-suc t⟹u)        (r-sucWrong bnₜ)     = t⟹u ↯ bn→nf bnₜ
    ⟹-det (r-suc t⟹u)        (r-suc t⟹u′)       = suc & ⟹-det t⟹u t⟹u′
    ⟹-det (r-predWrong _)      (r-predWrong _)      = refl
    ⟹-det (r-predWrong ())     r-predZero
    ⟹-det (r-predWrong ())     (r-predSuc _)
    ⟹-det (r-predWrong bnₜ)    (r-pred t⟹u′)      = t⟹u′ ↯ bn→nf bnₜ
    ⟹-det r-predZero           (r-predWrong ())
    ⟹-det r-predZero           r-predZero           = refl
    ⟹-det r-predZero           (r-pred zero⟹u′)   = zero⟹u′ ↯ nv→nf zero
    ⟹-det (r-predSuc _)        (r-predWrong ())
    ⟹-det (r-predSuc _)        (r-predSuc _)        = refl
    ⟹-det (r-predSuc nvₜ)      (r-pred suct⟹u′)   = suct⟹u′ ↯ nv→nf (suc nvₜ)
    ⟹-det (r-pred t⟹u)       (r-predWrong bnₜ)    = t⟹u ↯ bn→nf bnₜ
    ⟹-det (r-pred zero⟹u)    r-predZero           = zero⟹u ↯ nv→nf zero
    ⟹-det (r-pred suct⟹u)    (r-predSuc nvₜ)      = suct⟹u ↯ nv→nf (suc nvₜ)
    ⟹-det (r-pred t⟹u)       (r-pred t⟹u′)      = pred & ⟹-det t⟹u t⟹u′
    ⟹-det (r-iszeroWrong _)    (r-iszeroWrong bn₂)  = refl
    ⟹-det (r-iszeroWrong ())   r-iszeroZero
    ⟹-det (r-iszeroWrong ())   (r-iszeroSuc _)
    ⟹-det (r-iszeroWrong bnₜ)  (r-iszero t⟹u′)    = t⟹u′ ↯ bn→nf bnₜ
    ⟹-det r-iszeroZero         (r-iszeroWrong ())
    ⟹-det r-iszeroZero         r-iszeroZero         = refl
    ⟹-det r-iszeroZero         (r-iszero zero⟹u′) = zero⟹u′ ↯ nv→nf zero
    ⟹-det (r-iszeroSuc _)      (r-iszeroWrong ())
    ⟹-det (r-iszeroSuc _)      (r-iszeroSuc _)      = refl
    ⟹-det (r-iszeroSuc nvₜ)    (r-iszero suct⟹u′) = suct⟹u′ ↯ nv→nf (suc nvₜ)
    ⟹-det (r-iszero t⟹u)     (r-iszeroWrong bnₜ)  = t⟹u ↯ bn→nf bnₜ
    ⟹-det (r-iszero zero⟹u)  r-iszeroZero         = zero⟹u ↯ nv→nf zero
    ⟹-det (r-iszero suct⟹u)  (r-iszeroSuc nvₜ)    = suct⟹u ↯ nv→nf (suc nvₜ)
    ⟹-det (r-iszero t⟹u)     (r-iszero t⟹u′)    = iszero & ⟹-det t⟹u t⟹u′
    ⟹-det (r-ifWrong _)        (r-ifWrong _)        = refl
    ⟹-det (r-ifWrong (num ())) r-ifTrue
    ⟹-det (r-ifWrong (num ())) r-ifFalse
    ⟹-det (r-ifWrong bbₜ)      (r-if t₁⟹u₁′)      = t₁⟹u₁′ ↯ bb→nf bbₜ
    ⟹-det r-ifTrue             (r-ifWrong (num ()))
    ⟹-det r-ifTrue             r-ifTrue             = refl
    ⟹-det r-ifTrue             (r-if true⟹u₁′)    = true⟹u₁′ ↯ v→nf true
    ⟹-det r-ifFalse            (r-ifWrong (num ()))
    ⟹-det r-ifFalse            r-ifFalse            = refl
    ⟹-det r-ifFalse            (r-if false⟹u₁′)   = false⟹u₁′ ↯ v→nf false
    ⟹-det (r-if t₁⟹u₁)       (r-ifWrong bbₜ₁)     = t₁⟹u₁ ↯ bb→nf bbₜ₁
    ⟹-det (r-if true⟹u₁)     r-ifTrue             = true⟹u₁ ↯ v→nf true
    ⟹-det (r-if false⟹u₁)    r-ifFalse            = false⟹u₁ ↯ v→nf false
    ⟹-det (r-if t₁⟹u₁)       (r-if t₁⟹u₁′)      = (λ u₁″ → if u₁″ then _ else _) & ⟹-det t₁⟹u₁ t₁⟹u₁′


-- Every term is either a value, or reducible to another term.

    data Value/Reducible : Pred₀ Term where
      val : ∀ {t} → (v : Value t) → Value/Reducible t
      red : ∀ {t} → (ρ : Reducible t) → Value/Reducible t

    classify : ∀ t → Value/Reducible t
    classify wrong                   = val wrong
    classify true                    = val true
    classify false                   = val false
    classify zero                    = val (num zero)
    classify (suc t)                 with classify t
    ... | val wrong                  = red (_ , r-sucWrong wrong)
    ... | val true                   = red (_ , r-sucWrong true)
    ... | val false                  = red (_ , r-sucWrong false)
    ... | val (num nvₜ)              = val (num (suc nvₜ))
    ... | red (_ , t⟹u)            = red (_ , r-suc t⟹u)
    classify (pred t)                with classify t
    ... | val wrong                  = red (_ , r-predWrong wrong)
    ... | val true                   = red (_ , r-predWrong true)
    ... | val false                  = red (_ , r-predWrong false)
    ... | val (num zero)             = red (_ , r-predZero)
    ... | val (num (suc nvₜ))        = red (_ , r-predSuc nvₜ)
    ... | red (_ , t⟹u)            = red (_ , r-pred t⟹u)
    classify (iszero t)              with classify t
    ... | val wrong                  = red (_ , r-iszeroWrong wrong)
    ... | val true                   = red (_ , r-iszeroWrong true)
    ... | val false                  = red (_ , r-iszeroWrong false)
    ... | val (num zero)             = red (_ , r-iszeroZero)
    ... | val (num (suc nvₜ))        = red (_ , r-iszeroSuc nvₜ)
    ... | red (_ , t⟹u)            = red (_ , r-iszero t⟹u)
    classify (if t₁ then t₂ else t₃) with classify t₁
    ... | val wrong                  = red (_ , r-ifWrong wrong)
    ... | val true                   = red (_ , r-ifTrue)
    ... | val false                  = red (_ , r-ifFalse)
    ... | val (num nvₜ₁)             = red (_ , r-ifWrong (num nvₜ₁))
    ... | red (_ , t₁⟹u₁)          = red (_ , r-if t₁⟹u₁)


-- Echo of Theorem 3.5.8.

    nf→v : ∀ {t} → NormalForm t → Value t
    nf→v {t} nfₜ         with classify t
    ... | val vₜ          = vₜ
    ... | red (_ , t⟹u) = t⟹u ↯ nfₜ


-- Echo of Definition 3.5.9 and Theorem 3.5.11.

    open MultiStepReduction _⟹_ public
    open UniquenessOfNormalForms _⟹_ ⟹-det public

    {-# DISPLAY _* _⟹_ = _⟹*_ #-}
    {-# DISPLAY _*′ _⟹_ = _⟹*′_ #-}


-- Equipment for showing termination.

    _⇓_ : Rel₀ Term
    t ⇓ u = Value u × t ⟹* u

    _⇓ : Pred₀ Term
    t ⇓ = ∃ λ u → t ⇓ u

    halt : ∀ t → t ⇓
    halt wrong                            = _ , wrong , []
    halt true                             = _ , true , []
    halt false                            = _ , false , []
    halt zero                             = _ , num zero , []
    halt (suc t)                          with halt t
    ... | _ , wrong         , t⟹*wrong  = _ , wrong , map r-suc t⟹*wrong ∷ʳ r-sucWrong wrong
    ... | _ , true          , t⟹*true   = _ , wrong , map r-suc t⟹*true ∷ʳ r-sucWrong true
    ... | _ , false         , t⟹*false  = _ , wrong , map r-suc t⟹*false ∷ʳ r-sucWrong false
    ... | _ , num nvᵤ       , t⟹*u      = _ , num (suc nvᵤ) , map r-suc t⟹*u
    halt (pred t)                         with halt t
    ... | _ , wrong         , t⟹*wrong  = _ , wrong , map r-pred t⟹*wrong ∷ʳ r-predWrong wrong
    ... | _ , true          , t⟹*true   = _ , wrong , map r-pred t⟹*true ∷ʳ r-predWrong true
    ... | _ , false         , t⟹*false  = _ , wrong , map r-pred t⟹*false ∷ʳ r-predWrong false
    ... | _ , num zero      , t⟹*zero   = _ , num zero , map r-pred t⟹*zero ∷ʳ r-predZero
    ... | _ , num (suc nvᵤ) , t⟹*sucu   = _ , num nvᵤ , map r-pred t⟹*sucu ∷ʳ r-predSuc nvᵤ
    halt (iszero t)                       with halt t
    ... | _ , wrong         , t⟹*wrong  = _ , wrong , map r-iszero t⟹*wrong ∷ʳ r-iszeroWrong wrong
    ... | _ , true          , t⟹*true   = _ , wrong , map r-iszero t⟹*true ∷ʳ r-iszeroWrong true
    ... | _ , false         , t⟹*false  = _ , wrong , map r-iszero t⟹*false ∷ʳ r-iszeroWrong false
    ... | _ , num zero      , t⟹*zero   = _ , true , map r-iszero t⟹*zero ∷ʳ r-iszeroZero
    ... | _ , num (suc nvᵤ) , t⟹*sucu   = _ , false , map r-iszero t⟹*sucu ∷ʳ r-iszeroSuc nvᵤ
    halt (if t₁ then t₂ else t₃)          with halt t₁ | halt t₂ | halt t₃
    ... | _ , wrong         , t₁⟹*wrong | _ | _                  = _ , wrong , map r-if t₁⟹*wrong ∷ʳ r-ifWrong wrong
    ... | _ , true          , t₁⟹*true  | _ , vᵤ₂ , t₂⟹*u₂ | _ = _ , vᵤ₂ , (map r-if t₁⟹*true) ++ (r-ifTrue ∷ t₂⟹*u₂)
    ... | _ , false         , t₁⟹*false | _ | _ , vᵤ₃ , t₃⟹*u₃ = _ , vᵤ₃ , (map r-if t₁⟹*false) ++ (r-ifFalse ∷ t₃⟹*u₃)
    ... | _ , num nvᵤ₁      , t₁⟹*u     | _ | _                  = _ , wrong , map r-if t₁⟹*u ∷ʳ r-ifWrong (num nvᵤ₁)


-- Echo of Theorem 3.5.12.

    halt′ : ∀ t → ∃ λ u → NormalForm u × t ⟹* u
    halt′ t               with halt t
    ... | _ , vᵤ , t⟹*u = _ , v→nf vᵤ , t⟹*u


-- NOTE: Continued in Chapter3a.agda


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
-- 3.5.18. Exercise [⋆⋆ ↛]
-- “Suppose we want to change the evaluation strategy of our language so that the `then` and `else`
-- branches of an `if` expression are evaluated (in that order) _before_ the guard is evaluated.
-- Show how the reduction rules need to change to achieve this effect.”
-- (skipped)


----------------------------------------------------------------------------------------------------
--
-- 3.6. Notes


----------------------------------------------------------------------------------------------------
