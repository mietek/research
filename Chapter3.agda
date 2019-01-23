----------------------------------------------------------------------------------------------------

module Chapter3 where

open import Data.Empty public using (⊥)

open import Data.List public using (List ; [] ; _∷_)

import Data.Nat as Nat
open Nat public using (_≤_ ; _<_ ; _+_ ; s≤s ; suc ; zero)
  renaming (ℕ to Nat)

import Data.Nat.Properties as Nat
open Nat.≤-Reasoning public

open import Data.Product public using (_×_ ; _,_ ; Σ ; ∃ ; proj₁ ; proj₂)

open import Data.Unit public using (⊤)

open import Function public using (case_of_)

open import Level public using (_⊔_ ; 0ℓ)

open import Relation.Binary public using (Decidable ; DecSetoid ; Rel)

import Relation.Binary.PropositionalEquality as PropEq
open PropEq public using (_≡_ ; _≢_ ; refl ; subst)
  renaming (cong to _&_ ; sym to _⁻¹)

import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
open Star public using ()
  renaming (Star to _* ; ε to [] ; _◅_ to _∷_ ; _◅◅_ to _++_)

open import Relation.Nullary public using (¬_ ; Dec ; no ; yes)

open import Relation.Nullary.Negation public using ()
  renaming (contradiction to _↯_)

open import Relation.Unary public using (Pred)


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

¬¬snoc : ∀ {a ℓ} {A : Set a} {R : A → A → Set ℓ} →
         ∀ {x y z} → (R *) x y → R y z → ¬ ¬ ((R *) x z)
¬¬snoc R*xy Ryz ¬R*xz = (R*xy ++ (Ryz ∷ [])) ↯ ¬R*xz

undo : ∀ {a ℓ} {A : Set a} {R : A → A → Set ℓ} →
       ∀ {x y z} → R y z → ¬ ((R *) x z) → ¬ ((R *) x y)
undo Ryz ¬R*xz R*xy = ¬¬snoc R*xy Ryz ¬R*xz


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
    pred _                ≟ if _ then _ else _   = no λ ()
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
          ≤⟨ Nat.+-monoˡ-≤ (length (consts t₃))
                           (length-triangular (consts t₁) (consts t₂)) ⟩
            length (consts t₁) + length (consts t₂) + length (consts t₃)
          ≤⟨ Nat.+-mono-≤ (Nat.+-mono-≤ (lem-333 t₁)
                                        (lem-333 t₂))
                          (lem-333 t₃) ⟩
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




-- TODO

{-
    _∈?_ : Decidable _∈_
    s ∈? true                            = no λ ()
    s ∈? false                           = no λ ()
    s ∈? zero                            = no λ ()
    s ∈? suc t                           with s ≟ t
    ... | yes refl                       = yes suc
    ... | no s≢t                         = no λ where suc → refl ↯ s≢t
    s ∈? pred t                          with s ≟ t
    ... | yes refl                       = yes pred
    ... | no s≢t                         = no λ where pred → refl ↯ s≢t
    s ∈? iszero t                        with s ≟ t
    ... | yes refl                       = yes iszero
    ... | no s≢t                         = no λ where iszero → refl ↯ s≢t
    s ∈? if t₁ then t₂ else t₃           with s ≟ t₁ | s ≟ t₂ | s ≟ t₃
    ... | yes refl | _        | _        = yes if₁
    ... | no s≢t₁  | yes refl | _        = yes if₂
    ... | no s≢t₁  | no s≢t₂  | yes refl = yes if₃
    ... | no s≢t₁  | no s≢t₂  | no s≢t₃  = no λ where if₁ → refl ↯ s≢t₁
                                                      if₂ → refl ↯ s≢t₂
                                                      if₃ → refl ↯ s≢t₃

    _∈*?_ : Decidable (_∈_ *)
    s ∈*? t with s ≟ t
    ... | yes refl = yes []
    ... | no s≢t   with s ∈? t
    ... | yes s∈t  = yes (s∈t ∷ [])
    ... | no s∉t   = {!!}

    module _ {a ℓ} {A : Set a} {R : A → A → Set ℓ} (R? : Decidable R) where
      R*? : Decidable (R *)
      R*? x y with R? x y
      ... | yes Rxy = yes (Rxy ∷ [])
      ... | no ¬Rxy = {!!}
-}




-- As an exercise, we’re going to define structural induction using three methods.  First, a direct
-- definition using pattern matching.

    module Ind-Struct-Direct
      where
        ind-struct : ∀ {ℓ} {P : Pred Term ℓ} →
                     (∀ t → (∀ s →  s ∈ t → P s) → P t) → ∀ t → P t
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

        ind-struct : ∀ {ℓ} {P : Pred Term ℓ} →
                     (∀ t → (∀ s → s ∈ t → P s) → P t) → ∀ t → P t
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
        lem-333 : ∀ s → length (consts s) ≤ size s
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

        lem-333 : ∀ s → length (consts s) ≤ size s
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

        lem-333 : ∀ s → length (consts s) ≤ size s
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
-- We say `t ⟹ u` to mean that `t` reduces to `u` in one step.

    infix 3 _⟹_
    data _⟹_ : Rel₀ Term where
      r-ifTrue  : ∀ {t₂ t₃} → if true then t₂ else t₃ ⟹ t₂
      r-ifFalse : ∀ {t₂ t₃} → if false then t₂ else t₃ ⟹ t₃
      r-if      : ∀ {t₁ t₂ t₃ u₁} → (r₁ : t₁ ⟹ u₁) →
                  if t₁ then t₂ else t₃ ⟹ if u₁ then t₂ else t₃


----------------------------------------------------------------------------------------------------
--
-- 3.5.4. Theorem [Determinacy of one-step reduction]
-- “If `t ⟹ u₁` and `t ⟹ u₂`, then `u₁ = u₂`.
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
    nf→¬ρ nf (_ , r) = r ↯ nf

    ¬ρ→nf : ∀ {t} → ¬ Reducible t → NormalForm t
    ¬ρ→nf ¬ρ r = (_ , r) ↯ ¬ρ


-- We also need to jump ahead to Theorem 3.5.7, and show that every value is in normal form.

module BooleansOnly-Part2
  where
    open BooleansOnly-Part1 public
    open NormalForms _⟹_ public

    v→nf : ∀ {t} → Value t → NormalForm t
    v→nf true  = λ ()
    v→nf false = λ ()

    ⟹-det : ∀ {t u₁ u₂} → t ⟹ u₁ → t ⟹ u₂ → u₁ ≡ u₂
    ⟹-det r-ifTrue  r-ifTrue  = refl
    ⟹-det r-ifTrue  (r-if r₂) = r₂ ↯ v→nf true
    ⟹-det r-ifFalse r-ifFalse = refl
    ⟹-det r-ifFalse (r-if r₂) = r₂ ↯ v→nf false
    ⟹-det (r-if r₁) r-ifTrue  = r₁ ↯ v→nf true
    ⟹-det (r-if r₁) r-ifFalse = r₁ ↯ v→nf false
    ⟹-det (r-if r₁) (r-if r₂) = (λ t₁ → if t₁ then _ else _) & ⟹-det r₁ r₂


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
      val : ∀ {t} → (v : Value t) → Value/Reducible t
      red : ∀ {t} → (ρ : Reducible t) → Value/Reducible t

    classify : ∀ t → Value/Reducible t
    classify true                    = val true
    classify false                   = val false
    classify (if t₁ then t₂ else t₃) with classify t₁
    ... | val true                   = red (_ , r-ifTrue)
    ... | val false                  = red (_ , r-ifFalse)
    ... | red (_ , r₁)               = red (_ , r-if r₁)

    nf→v : ∀ {t} → NormalForm t → Value t
    nf→v nf          with classify _
    ... | val v       = v
    ... | red (_ , r) = r ↯ nf


----------------------------------------------------------------------------------------------------
--
-- 3.5.9. Definition
-- “The _multi-step reduction_ relation `⟹*` is the reflexive, transitive closure of one-step
-- reduction.  That is, it is the smallest relation such that (1) if `t ⟹ u` then `t ⟹* u`,
-- (2) `t ⟹* t` for all `t`, and (3) if `s ⟹* t` and `t ⟹* u`, then `s ⟹* u`.”
--
-- We say `t ⟹* u` to mean that `t` reduces to `u` in multiple steps.  We give this definition
-- in a generic manner, using equipment from the Agda standard library, and we include some related
-- utilities.

module MultiStepReduction {a ℓ} {A : Set a}
    (_⟹_ : Rel A ℓ)
  where
    infix 3 _⟹*_
    _⟹*_ : Rel A (a ⊔ ℓ)
    _⟹*_ = _⟹_ *

    _∷ʳ_ : ∀ {s t u} → s ⟹* t → t ⟹ u → s ⟹* u
    rs ∷ʳ r = rs ++ (r ∷ [])

    map : ∀ {f : A → A} → (∀ {t u} → t ⟹ u → f t ⟹ f u) →
          ∀ {t u} → t ⟹* u → f t ⟹* f u
    map {f = f} = Star.gmap f


----------------------------------------------------------------------------------------------------
--
-- 3.5.10. Exercise [*]
-- “Rephrase Definition 3.5.9 as a set of inference rules.”
-- (redundant)


----------------------------------------------------------------------------------------------------
--
-- 3.5.11. Theorem [Uniqueness of normal forms]
-- “If `t ⟹* u₁` and `t ⟹* u₂`, where `u₁` and `u₂` are both normal forms, then `u₁ ≡ u₂`.”

module UniquenessOfNormalForms {a ℓ} {A : Set a}
    (_⟹_ : Rel A ℓ)
    (⟹-det : ∀ {t u₁ u₂} → t ⟹ u₁ → t ⟹ u₂ → u₁ ≡ u₂)
  where
    open NormalForms _⟹_
    open MultiStepReduction _⟹_

    ⟹*-unf : ∀ {t u₁ u₂} → NormalForm u₁ → NormalForm u₂ → t ⟹* u₁ → t ⟹* u₂ → u₁ ≡ u₂
    ⟹*-unf nf₁ nf₂ []         []         = refl
    ⟹*-unf nf₁ nf₂ []         (r₂ ∷ rs₂) = r₂ ↯ nf₁
    ⟹*-unf nf₁ nf₂ (r₁ ∷ rs₁) []         = r₁ ↯ nf₂
    ⟹*-unf nf₁ nf₂ (r₁ ∷ rs₁) (r₂ ∷ rs₂) with ⟹-det r₁ r₂
    ... | refl                             = ⟹*-unf nf₁ nf₂ rs₁ rs₂


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

    halt-if : ∀ {s₁ t₁ t₂ t₃ tₙ} → s₁ ⟹* t₁ → if t₁ then t₂ else t₃ ⟹ tₙ → tₙ ⇓ →
              if s₁ then t₂ else t₃ ⇓
    halt-if rs₁ rₙ (uₙ , vₙ , rsₙ) = uₙ , vₙ , map r-if rs₁ ++ rₙ ∷ rsₙ

    halt : ∀ t → t ⇓
    halt true                    = _ , true , []
    halt false                   = _ , false , []
    halt (if t₁ then t₂ else t₃) with halt t₁
    ... | .true  , true  , rs₁   = halt-if rs₁ r-ifTrue (halt t₂)
    ... | .false , false , rs₁   = halt-if rs₁ r-ifFalse (halt t₃)

    halt′ : ∀ t → ∃ λ u → NormalForm u × t ⟹* u
    halt′ t          with halt t
    ... | u , v , rs = u , v→nf v , rs


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
-- if `t ⟹ u₁` and `t ⟹ u₂`, then `u₁ ≡ u₂`.”

module NumbersAndBooleans-Part2
  where
    open NumbersAndBooleans-Part1 public

    data NumericValue : Pred₀ Term where
      zero : NumericValue zero
      suc  : ∀ {t} → (nv : NumericValue t) → NumericValue (suc t)

    data Value : Pred₀ Term where
      true  : Value true
      false : Value false
      num   : ∀ {t} → (nv : NumericValue t) → Value t


-- Echo of Definition 3.5.3.

    infix 3 _⟹_
    data _⟹_ : Rel₀ Term where
      r-suc        : ∀ {t u} → (r : t ⟹ u) → suc t ⟹ suc u
      r-predZero   : pred zero ⟹ zero
      r-predSuc    : ∀ {t} → (nv : NumericValue t) → pred (suc t) ⟹ t
      r-pred       : ∀ {t u} → (r : t ⟹ u) → pred t ⟹ pred u
      r-iszeroZero : iszero zero ⟹ true
      r-iszeroSuc  : ∀ {t} → (nv : NumericValue t) → iszero (suc t) ⟹ false
      r-iszero     : ∀ {t u} → (r : t ⟹ u) → iszero t ⟹ iszero u
      r-ifTrue     : ∀ {t₂ t₃} → if true then t₂ else t₃ ⟹ t₂
      r-ifFalse    : ∀ {t₂ t₃} → if false then t₂ else t₃ ⟹ t₃
      r-if         : ∀ {t₁ t₂ t₃ u₁} → (r₁ : t₁ ⟹ u₁) →
                     if t₁ then t₂ else t₃ ⟹ if u₁ then t₂ else t₃


-- Echo of Definition 3.5.6.

    open NormalForms _⟹_ public


-- Echo of Theorem 3.5.7.

    nv→nf : ∀ {t} → NumericValue t → NormalForm t
    nv→nf zero     = λ ()
    nv→nf (suc nv) = λ where (r-suc r) → r ↯ nv→nf nv

    v→nf : ∀ {t} → Value t → NormalForm t
    v→nf true     = λ ()
    v→nf false    = λ ()
    v→nf (num nv) = nv→nf nv


-- Echo of Theorem 3.5.4.

    ⟹-det : ∀ {t u₁ u₂} → t ⟹ u₁ → t ⟹ u₂ → u₁ ≡ u₂
    ⟹-det (r-suc r₁)        (r-suc r₂)        = suc & ⟹-det r₁ r₂
    ⟹-det r-predZero        r-predZero        = refl
    ⟹-det r-predZero        (r-pred r₂)       = r₂ ↯ nv→nf zero
    ⟹-det (r-predSuc nv₁)   (r-predSuc nv₂)   = refl
    ⟹-det (r-predSuc nv₁)   (r-pred r₂)       = r₂ ↯ nv→nf (suc nv₁)
    ⟹-det (r-pred r₁)       r-predZero        = r₁ ↯ nv→nf zero
    ⟹-det (r-pred r₁)       (r-predSuc nv₂)   = r₁ ↯ nv→nf (suc nv₂)
    ⟹-det (r-pred r₁)       (r-pred r₂)       = pred & ⟹-det r₁ r₂
    ⟹-det r-iszeroZero      r-iszeroZero      = refl
    ⟹-det r-iszeroZero      (r-iszero r₂)     = r₂ ↯ nv→nf zero
    ⟹-det (r-iszeroSuc nv₁) (r-iszeroSuc nv₂) = refl
    ⟹-det (r-iszeroSuc nv₁) (r-iszero r₂)     = r₂ ↯ nv→nf (suc nv₁)
    ⟹-det (r-iszero r₁)     r-iszeroZero      = r₁ ↯ nv→nf zero
    ⟹-det (r-iszero r₁)     (r-iszeroSuc nv₂) = r₁ ↯ nv→nf (suc nv₂)
    ⟹-det (r-iszero r₁)     (r-iszero r₂)     = iszero & ⟹-det r₁ r₂
    ⟹-det r-ifTrue          r-ifTrue          = refl
    ⟹-det r-ifTrue          (r-if r₂)         = r₂ ↯ v→nf true
    ⟹-det r-ifFalse         r-ifFalse         = refl
    ⟹-det r-ifFalse         (r-if r₂)         = r₂ ↯ v→nf false
    ⟹-det (r-if r₁)         r-ifTrue          = r₁ ↯ v→nf true
    ⟹-det (r-if r₁)         r-ifFalse         = r₁ ↯ v→nf false
    ⟹-det (r-if r₁)         (r-if r₂)         = (λ s₁ → if s₁ then _ else _) & ⟹-det r₁ r₂


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
      stu : ∀ {t} → (σ : Stuck t) → Stuck/Value/Reducible t
      val : ∀ {t} → (v : Value t) → Stuck/Value/Reducible t
      red : ∀ {t} → (ρ : Reducible t) → Stuck/Value/Reducible t

    σ-suc : ∀ {t} → Stuck t → Stuck (suc t)
    σ-suc (¬v , nf) = (λ where (num (suc nv)) → num nv ↯ ¬v)
                    , (λ where (r-suc r) → r ↯ nf)

    σ-sucTrue : Stuck (suc true)
    σ-sucTrue = (λ where (num (suc ())))
              , (λ where (r-suc ()))

    σ-sucFalse : Stuck (suc false)
    σ-sucFalse = (λ where (num (suc ())))
               , (λ where (r-suc ()))

    σ-pred : ∀ {t} → Stuck t → Stuck (pred t)
    σ-pred (¬v , nf) = (λ where (num ()))
                     , (λ where r-predZero     → num zero ↯ ¬v
                                (r-predSuc nv) → num (suc nv) ↯ ¬v
                                (r-pred r)     → r ↯ nf)

    σ-predTrue : Stuck (pred true)
    σ-predTrue = (λ where (num ()))
               , (λ where (r-pred ()))

    σ-predFalse : Stuck (pred false)
    σ-predFalse = (λ where (num ()))
                , (λ where (r-pred ()))

    σ-iszero : ∀ {t} → Stuck t → Stuck (iszero t)
    σ-iszero (¬v , nf) = (λ where (num ()))
                       , (λ where r-iszeroZero     → num zero ↯ ¬v
                                  (r-iszeroSuc nv) → num (suc nv) ↯ ¬v
                                  (r-iszero r)     → r ↯ nf)

    σ-iszeroTrue : Stuck (iszero true)
    σ-iszeroTrue = (λ where (num ()))
                 , (λ where (r-iszero ()))

    σ-iszeroFalse : Stuck (iszero false)
    σ-iszeroFalse = (λ where (num ()))
                  , (λ where (r-iszero ()))

    σ-if : ∀ {t₁ t₂ t₃} → Stuck t₁ → Stuck (if t₁ then t₂ else t₃)
    σ-if (¬v₁ , nf₁) = (λ where (num ()))
                     , (λ where r-ifTrue  → true ↯ ¬v₁
                                r-ifFalse → false ↯ ¬v₁
                                (r-if r₁) → r₁ ↯ nf₁)

    σ-ifZero : ∀ {t₂ t₃} → Stuck (if zero then t₂ else t₃)
    σ-ifZero = (λ where (num ()))
             , (λ where (r-if ()))

    σ-ifSuc : ∀ {nv₁ t₂ t₃} → NumericValue nv₁ → Stuck (if (suc nv₁) then t₂ else t₃)
    σ-ifSuc nv₁ = (λ where (num ()))
                , (λ where (r-if (r-suc r₁)) → r₁ ↯ nv→nf nv₁)

    classify : ∀ t → Stuck/Value/Reducible t
    classify true                    = val true
    classify false                   = val false
    classify zero                    = val (num zero)
    classify (suc t)                 with classify t
    ... | stu σ                      = stu (σ-suc σ)
    ... | val true                   = stu σ-sucTrue
    ... | val false                  = stu σ-sucFalse
    ... | val (num nv)               = val (num (suc nv))
    ... | red (_ , r)                = red (_ , r-suc r)
    classify (pred t)                with classify t
    ... | stu σ                      = stu (σ-pred σ)
    ... | val true                   = stu σ-predTrue
    ... | val false                  = stu σ-predFalse
    ... | val (num zero)             = red (_ , r-predZero)
    ... | val (num (suc nv))         = red (_ , r-predSuc nv)
    ... | red (_ , r)                = red (_ , r-pred r)
    classify (iszero t)              with classify t
    ... | stu σ                      = stu (σ-iszero σ)
    ... | val true                   = stu σ-iszeroTrue
    ... | val false                  = stu σ-iszeroFalse
    ... | val (num zero)             = red (_ , r-iszeroZero)
    ... | val (num (suc nv))         = red (_ , r-iszeroSuc nv)
    ... | red (_ , r)                = red (_ , r-iszero r)
    classify (if t₁ then t₂ else t₃) with classify t₁
    ... | stu σ₁                     = stu (σ-if σ₁)
    ... | val true                   = red (_ , r-ifTrue)
    ... | val false                  = red (_ , r-ifFalse)
    ... | val (num zero)             = stu σ-ifZero
    ... | val (num (suc nv₁))        = stu (σ-ifSuc nv₁)
    ... | red (_ , r₁)               = red (_ , r-if r₁)


-- Echo of Theorem 3.5.8.

    data Stuck/Value : Pred₀ Term where
      stu : ∀ {t} → (σ : Stuck t) → Stuck/Value t
      val : ∀ {t} → (v : Value t) → Stuck/Value t

    nf→σ/v : ∀ {t} → NormalForm t → Stuck/Value t
    nf→σ/v nf        with classify _
    ... | stu σ       = stu σ
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

    halt-if : ∀ {s₁ t₁ t₂ t₃ tₙ} → s₁ ⟹* t₁ → if t₁ then t₂ else t₃ ⟹ tₙ → tₙ ⇓ →
              if s₁ then t₂ else t₃ ⇓
    halt-if rs₁ rₙ (uₙ , vₙ , rsₙ) = uₙ , vₙ , map r-if rs₁ ++ rₙ ∷ rsₙ

    halt : ∀ t → t ⇓
    halt true                                  = _ , val true , []
    halt false                                 = _ , val false , []
    halt zero                                  = _ , val (num zero) , []
    halt (suc t)                               with halt t
    ... | _        , stu σ               , rs  = _ , stu (σ-suc σ) , map r-suc rs
    ... | .true    , val true            , rs  = _ , stu σ-sucTrue , map r-suc rs
    ... | .false   , val false           , rs  = _ , stu σ-sucFalse , map r-suc rs
    ... | ._       , val (num nv)        , rs  = _ , val (num (suc nv)) , map r-suc rs
    halt (pred t)                              with halt t
    ... | _        , stu σ               , rs  = _ , stu (σ-pred σ) , map r-pred rs
    ... | .true    , val true            , rs  = _ , stu σ-predTrue , map r-pred rs
    ... | .false   , val false           , rs  = _ , stu σ-predFalse , map r-pred rs
    ... | .zero    , val (num zero)      , rs  = _ , val (num zero) , map r-pred rs ∷ʳ r-predZero
    ... | .(suc _) , val (num (suc nv))  , rs  = _ , val (num nv) , map r-pred rs ∷ʳ r-predSuc nv
    halt (iszero t)                            with halt t
    ... | _        , stu σ               , rs  = _ , stu (σ-iszero σ) , map r-iszero rs
    ... | .true    , val true            , rs  = _ , stu σ-iszeroTrue , map r-iszero rs
    ... | .false   , val false           , rs  = _ , stu σ-iszeroFalse , map r-iszero rs
    ... | .zero    , val (num zero)      , rs  = _ , val true , map r-iszero rs ∷ʳ r-iszeroZero
    ... | .(suc _) , val (num (suc nv))  , rs  = _ , val false , map r-iszero rs ∷ʳ r-iszeroSuc nv
    halt (if t₁ then t₂ else t₃)               with halt t₁
    ... | _        , stu σ₁              , rs₁ = _ , stu (σ-if σ₁) , map r-if rs₁
    ... | .true    , val true            , rs₁ = halt-if rs₁ r-ifTrue (halt t₂)
    ... | .false   , val false           , rs₁ = halt-if rs₁ r-ifFalse (halt t₃)
    ... | .zero    , val (num zero)      , rs₁ = _ , stu σ-ifZero , map r-if rs₁
    ... | .(suc _) , val (num (suc nv₁)) , rs₁ = _ , stu (σ-ifSuc nv₁) , map r-if rs₁


-- Echo of Theorem 3.5.12.

    halt′ : ∀ t → ∃ λ u → NormalForm u × t ⟹* u
    halt′ t                     with halt t
    ... | u , stu (_ , nf) , rs = u , nf      , rs
    ... | u , val v        , rs = u , v→nf v , rs


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
      suc pred iszero       : (t : Term) → Term
      if_then_else          : (t₁ t₂ t₃ : Term) → Term

    data NumericValue : Pred₀ Term where
      zero : NumericValue zero
      suc  : ∀ {t} → (nv : NumericValue t) → NumericValue (suc t)

    data Value : Pred₀ Term where
      wrong : Value wrong
      true  : Value true
      false : Value false
      num   : ∀ {t} → (nv : NumericValue t) → Value t

    data BadNat : Pred₀ Term where
      wrong : BadNat wrong
      true  : BadNat true
      false : BadNat false

    data BadBool : Pred₀ Term where
      wrong : BadBool wrong
      num   : ∀ {t} → (nv : NumericValue t) → BadBool t


-- Echo of Definition 3.5.3.

    infix 3 _⟹_
    data _⟹_ : Rel₀ Term where
      r-sucWrong    : ∀ {t} → (bn : BadNat t) → suc t ⟹ wrong
      r-suc         : ∀ {t u} → (r : t ⟹ u) → suc t ⟹ suc u
      r-predWrong   : ∀ {t} → (bn : BadNat t) → pred t ⟹ wrong
      r-predZero    : pred zero ⟹ zero
      r-predSuc     : ∀ {t} → (nv : NumericValue t) → pred (suc t) ⟹ t
      r-pred        : ∀ {t u} → (r : t ⟹ u) → pred t ⟹ pred u
      r-iszeroWrong : ∀ {t} → (bn : BadNat t) → iszero t ⟹ wrong
      r-iszeroZero  : iszero zero ⟹ true
      r-iszeroSuc   : ∀ {t} → (nv : NumericValue t) → iszero (suc t) ⟹ false
      r-iszero      : ∀ {t u} → (r : t ⟹ u) → iszero t ⟹ iszero u
      r-ifWrong     : ∀ {t₁ t₂ t₃} → (bb : BadBool t₁) → if t₁ then t₂ else t₃ ⟹ wrong
      r-ifTrue      : ∀ {t₂ t₃} → if true then t₂ else t₃ ⟹ t₂
      r-ifFalse     : ∀ {t₂ t₃} → if false then t₂ else t₃ ⟹ t₃
      r-if          : ∀ {t₁ t₂ t₃ u₁} → (r : t₁ ⟹ u₁) →
                      if t₁ then t₂ else t₃ ⟹ if u₁ then t₂ else t₃


-- Echo of Definition 3.5.6.

    open NormalForms _⟹_ public


-- Echo of Theorem 3.5.7.

    bn→¬nv : ∀ {t} → BadNat t → ¬ NumericValue t
    bn→¬nv wrong = λ ()
    bn→¬nv true  = λ ()
    bn→¬nv false = λ ()

    nv→nf : ∀ {t} → NumericValue t → NormalForm t
    nv→nf zero     = λ ()
    nv→nf (suc nv) = λ where
      (r-sucWrong bn) → nv ↯ bn→¬nv bn
      (r-suc r)       → r ↯ nv→nf nv

    v→nf : ∀ {t} → Value t → NormalForm t
    v→nf wrong    = λ ()
    v→nf true     = λ ()
    v→nf false    = λ ()
    v→nf (num nv) = nv→nf nv

    bn→nf : ∀ {t} → BadNat t → NormalForm t
    bn→nf wrong = λ ()
    bn→nf true  = λ ()
    bn→nf false = λ ()

    bb→nf : ∀ {t} → BadBool t → NormalForm t
    bb→nf wrong    = λ ()
    bb→nf (num nv) = nv→nf nv


-- Echo of Theorem 3.5.4.  Also Lemma A.3.

    ⟹-det : ∀ {t u₁ u₂} → t ⟹ u₁ → t ⟹ u₂ → u₁ ≡ u₂
    ⟹-det (r-sucWrong bn₁)     (r-sucWrong bn₂)    = refl
    ⟹-det (r-sucWrong bn₁)     (r-suc r₂)          = r₂ ↯ bn→nf bn₁
    ⟹-det (r-suc r₁)           (r-sucWrong bn₂)    = r₁ ↯ bn→nf bn₂
    ⟹-det (r-suc r₁)           (r-suc r₂)          = suc & ⟹-det r₁ r₂
    ⟹-det (r-predWrong bn₁)    (r-predWrong bn₂)   = refl
    ⟹-det (r-predWrong ())     r-predZero
    ⟹-det (r-predWrong ())     (r-predSuc nv₂)
    ⟹-det (r-predWrong bn₁)    (r-pred r₂)         = r₂ ↯ bn→nf bn₁
    ⟹-det r-predZero (         r-predWrong ())
    ⟹-det r-predZero           r-predZero          = refl
    ⟹-det r-predZero           (r-pred r₂)         = r₂ ↯ nv→nf zero
    ⟹-det (r-predSuc nv₁)      (r-predWrong ())
    ⟹-det (r-predSuc nv₁)      (r-predSuc nv₂)     = refl
    ⟹-det (r-predSuc nv₁)      (r-pred r₂)         = r₂ ↯ nv→nf (suc nv₁)
    ⟹-det (r-pred r₁)          (r-predWrong bn₂)   = r₁ ↯ bn→nf bn₂
    ⟹-det (r-pred r₁)          r-predZero          = r₁ ↯ nv→nf zero
    ⟹-det (r-pred r₁)          (r-predSuc nv₂)     = r₁ ↯ nv→nf (suc nv₂)
    ⟹-det (r-pred r₁)          (r-pred r₂)         = pred & ⟹-det r₁ r₂
    ⟹-det (r-iszeroWrong bn₁)  (r-iszeroWrong bn₂) = refl
    ⟹-det (r-iszeroWrong ())   r-iszeroZero
    ⟹-det (r-iszeroWrong ())   (r-iszeroSuc nv₂)
    ⟹-det (r-iszeroWrong bn₁)  (r-iszero r₂)       = r₂ ↯ bn→nf bn₁
    ⟹-det r-iszeroZero         (r-iszeroWrong ())
    ⟹-det r-iszeroZero         r-iszeroZero        = refl
    ⟹-det r-iszeroZero         (r-iszero r₂)       = r₂ ↯ nv→nf zero
    ⟹-det (r-iszeroSuc nv₁)    (r-iszeroWrong ())
    ⟹-det (r-iszeroSuc nv₁)    (r-iszeroSuc nv₂)   = refl
    ⟹-det (r-iszeroSuc nv₁)    (r-iszero r₂)       = r₂ ↯ nv→nf (suc nv₁)
    ⟹-det (r-iszero r₁)        (r-iszeroWrong bn₂) = r₁ ↯ bn→nf bn₂
    ⟹-det (r-iszero r₁)        r-iszeroZero        = r₁ ↯ nv→nf zero
    ⟹-det (r-iszero r₁)        (r-iszeroSuc nv₂)   = r₁ ↯ nv→nf (suc nv₂)
    ⟹-det (r-iszero r₁)        (r-iszero r₂)       = iszero & ⟹-det r₁ r₂
    ⟹-det (r-ifWrong bb₁)      (r-ifWrong bb₂)     = refl
    ⟹-det (r-ifWrong (num ())) r-ifTrue
    ⟹-det (r-ifWrong (num ())) r-ifFalse
    ⟹-det (r-ifWrong bb₁)      (r-if r₂)           = r₂ ↯ bb→nf bb₁
    ⟹-det r-ifTrue             (r-ifWrong (num ()))
    ⟹-det r-ifTrue             r-ifTrue            = refl
    ⟹-det r-ifTrue             (r-if r₂)           = r₂ ↯ v→nf true
    ⟹-det r-ifFalse            (r-ifWrong (num ()))
    ⟹-det r-ifFalse            r-ifFalse           = refl
    ⟹-det r-ifFalse            (r-if r₂)           = r₂ ↯ v→nf false
    ⟹-det (r-if r₁)            (r-ifWrong bb₂)     = r₁ ↯ bb→nf bb₂
    ⟹-det (r-if r₁)            r-ifTrue            = r₁ ↯ v→nf true
    ⟹-det (r-if r₁)            r-ifFalse           = r₁ ↯ v→nf false
    ⟹-det (r-if r₁)            (r-if r₂)           = (λ s₁ → if s₁ then _ else _) &
                                                         ⟹-det r₁ r₂


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
    ... | val (num nv)               = val (num (suc nv))
    ... | red (_ , r)                = red (_ , r-suc r)
    classify (pred t)                with classify t
    ... | val wrong                  = red (_ , r-predWrong wrong)
    ... | val true                   = red (_ , r-predWrong true)
    ... | val false                  = red (_ , r-predWrong false)
    ... | val (num zero)             = red (_ , r-predZero)
    ... | val (num (suc nv))         = red (_ , r-predSuc nv)
    ... | red (_ , r)                = red (_ , r-pred r)
    classify (iszero t)              with classify t
    ... | val wrong                  = red (_ , r-iszeroWrong wrong)
    ... | val true                   = red (_ , r-iszeroWrong true)
    ... | val false                  = red (_ , r-iszeroWrong false)
    ... | val (num zero)             = red (_ , r-iszeroZero)
    ... | val (num (suc nv))         = red (_ , r-iszeroSuc nv)
    ... | red (_ , r)                = red (_ , r-iszero r)
    classify (if t₁ then t₂ else t₃) with classify t₁
    ... | val wrong                  = red (_ , r-ifWrong wrong)
    ... | val true                   = red (_ , r-ifTrue)
    ... | val false                  = red (_ , r-ifFalse)
    ... | val (num nv₁)              = red (_ , r-ifWrong (num nv₁))
    ... | red (_ , r₁)               = red (_ , r-if r₁)


-- Echo of Theorem 3.5.8.

    nf→v : ∀ {t} → NormalForm t → Value t
    nf→v nf          with classify _
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

    halt-if : ∀ {s₁ t₁ t₂ t₃ tₙ} → s₁ ⟹* t₁ → if t₁ then t₂ else t₃ ⟹ tₙ → tₙ ⇓ →
              if s₁ then t₂ else t₃ ⇓
    halt-if rs₁ rₙ (uₙ , vₙ , rsₙ) = uₙ , vₙ , map r-if rs₁ ++ rₙ ∷ rsₙ

    halt : ∀ t → t ⇓
    halt wrong                         = _ , wrong , []
    halt true                          = _ , true , []
    halt false                         = _ , false , []
    halt zero                          = _ , num zero , []
    halt (suc t)                       with halt t
    ... | .wrong , wrong         , rs  = _ , wrong , map r-suc rs ∷ʳ r-sucWrong wrong
    ... | .true  , true          , rs  = _ , wrong , map r-suc rs ∷ʳ r-sucWrong true
    ... | .false , false         , rs  = _ , wrong , map r-suc rs ∷ʳ r-sucWrong false
    ... | _      , num nv        , rs  = _ , num (suc nv) , map r-suc rs
    halt (pred t)                      with halt t
    ... | .wrong , wrong         , rs  = _ , wrong , map r-pred rs ∷ʳ r-predWrong wrong
    ... | .true  , true          , rs  = _ , wrong , map r-pred rs ∷ʳ r-predWrong true
    ... | .false , false         , rs  = _ , wrong , map r-pred rs ∷ʳ r-predWrong false
    ... | _      , num zero      , rs  = _ , num zero , map r-pred rs ∷ʳ r-predZero
    ... | _      , num (suc nv)  , rs  = _ , num nv , map r-pred rs ∷ʳ r-predSuc nv
    halt (iszero t)                    with halt t
    ... | .wrong , wrong         , rs  = _ , wrong , map r-iszero rs ∷ʳ r-iszeroWrong wrong
    ... | .true  , true          , rs  = _ , wrong , map r-iszero rs ∷ʳ r-iszeroWrong true
    ... | .false , false         , rs  = _ , wrong , map r-iszero rs ∷ʳ r-iszeroWrong false
    ... | _      , num zero      , rs  = _ , true , map r-iszero rs ∷ʳ r-iszeroZero
    ... | _      , num (suc nv)  , rs  = _ , false , map r-iszero rs ∷ʳ r-iszeroSuc nv
    halt (if t₁ then t₂ else t₃)       with halt t₁
    ... | .wrong , wrong         , rs₁ = _ , wrong , map r-if rs₁ ∷ʳ r-ifWrong wrong
    ... | .true  , true          , rs₁ = halt-if rs₁ r-ifTrue (halt t₂)
    ... | .false , false         , rs₁ = halt-if rs₁ r-ifFalse (halt t₃)
    ... | _      , num nv₁       , rs₁ = _ , wrong , map r-if rs₁ ∷ʳ r-ifWrong (num nv₁)


-- Echo of Theorem 3.5.12.

    halt′ : ∀ t → ∃ λ u → NormalForm u × t ⟹* u
    halt′ t          with halt t
    ... | u , v , rs = u , v→nf v , rs


----------------------------------------------------------------------------------------------------
--
-- Work in progress


    data _∈_ : Rel₀ Term where
      suc    : ∀ {t} → t ∈ suc t
      pred   : ∀ {t} → t ∈ pred t
      iszero : ∀ {t} → t ∈ iszero t
      if₁    : ∀ {t₁ t₂ t₃} → t₁ ∈ if t₁ then t₂ else t₃
      if₂    : ∀ {t₁ t₂ t₃} → t₂ ∈ if t₁ then t₂ else t₃
      if₃    : ∀ {t₁ t₂ t₃} → t₃ ∈ if t₁ then t₂ else t₃

    _∈*_ : Rel₀ Term
    _∈*_ = _∈_ *

    _∉*_ : Rel₀ Term
    s ∉* t = ¬ (s ∈* t)

    Wrong : Pred₀ Term
    Wrong t = wrong ∈* t

    data GoodTerm : Pred₀ Term where
      true         : GoodTerm true
      false        : GoodTerm false
      zero         : GoodTerm zero
      suc          : ∀ {t} → (gt : GoodTerm t) → GoodTerm (suc t)
      pred         : ∀ {t} → (gt : GoodTerm t) → GoodTerm (pred t)
      iszero       : ∀ {t} → (gt : GoodTerm t) → GoodTerm (iszero t)
      if_then_else : ∀ {t₁ t₂ t₃} → (gt₁ : GoodTerm t₁) (gt₂ : GoodTerm t₂) (gt₃ : GoodTerm t₃) →
                     GoodTerm (if t₁ then t₂ else t₃)

    gt-uniq : ∀ {t} → (gt : GoodTerm t) (gt′ : GoodTerm t) → gt ≡ gt′
    gt-uniq true                       true         = refl
    gt-uniq false                      false        = refl
    gt-uniq zero                       zero         = refl
    gt-uniq (suc gt)                   (suc gt′)    with gt-uniq gt gt′
    ... | refl                                       = refl
    gt-uniq (pred gt)                  (pred gt′)   with gt-uniq gt gt′
    ... | refl                                      = refl
    gt-uniq (iszero gt)                (iszero gt′) with gt-uniq gt gt′
    ... | refl                                      = refl
    gt-uniq (if gt₁ then gt₂ else gt₃) (if gt₁′ then gt₂′ else gt₃′)
      with gt-uniq gt₁ gt₁′ | gt-uniq gt₂ gt₂′ | gt-uniq gt₃ gt₃′
    ... | refl | refl | refl                        = refl


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
