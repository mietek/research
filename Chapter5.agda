---------------------------------------------------------------------------------------------------------------

module Chapter5 where

open import Agda.Builtin.FromString public
  using (IsString ; fromString)

open import Data.Bool public
  using (Bool ; T ; false ; true)

open import Data.String public
  using (String)

import Data.String.Unsafe as String

open import Function public
  using (_∘_ ; case_of_)

open import Prelude public
open import Prelude-UniqueList public
open import Prelude-WellFounded public


---------------------------------------------------------------------------------------------------------------
--
-- TODO

data Name : Set₀ where
  name : String → Name

_≟ᴺ_ : Decidable {A = Name} _≡_
name x ≟ᴺ name y with x String.≟ y
... | yes refl = yes refl
... | no x≢y   = no λ where refl → refl ↯ x≢y

instance
  Name-isString : IsString Name
  Name-isString = record
    { Constraint = λ s → ⊤
    ; fromString = λ s → name s
    }

Name-decSetoid : DecSetoid _ _
Name-decSetoid = record
  { Carrier = Name
  ; _≈_     = _≡_
  ; isDecEquivalence = record
    { isEquivalence = ≡-isEquivalence
    ; _≟_           = _≟ᴺ_
    }
  }

module UniqueList-Name = MakeUniqueList (Name-decSetoid)

---------------------------------------------------------------------------------------------------------------
--
-- 5. The untyped lambda-calculus
--

---------------------------------------------------------------------------------------------------------------
--
-- 5.1. Basics
-- “The syntax of the lambda-calculus comprises just three sorts of terms. …”
--
-- We skip ahead to Definition 5.3.1 in order to be ready for the preliminary exercises.

module LC-Part1
  where
    infixl 7 _$_
    data Term : Set₀ where
      `_   : ∀ (x : Name) → Term
      ƛ_∙_ : ∀ (x : Name) (t : Term) → Term
      _$_  : ∀ (t₁ t₂ : Term) → Term

    instance
      Term-isString : IsString Term
      Term-isString = record
        { Constraint = λ s → ⊤
        ; fromString = λ s → ` name s
        }


---------------------------------------------------------------------------------------------------------------
--
-- • Abstract and concrete syntax
-- • Variables and metavariables
-- • Scope
-- • Operational semantics


---------------------------------------------------------------------------------------------------------------
--
-- 5.2. Programming in the lambda-calculus
--
-- • Multiple arguments
-- • Church booleans

    tru  = ƛ "t" ∙ ƛ "f" ∙ "t"
    fls  = ƛ "t" ∙ ƛ "f" ∙ "f"
    test = ƛ "l" ∙ ƛ "m" ∙ ƛ "n" ∙ "l" $ "m" $ "n"
    and  = ƛ "b" ∙ ƛ "c" ∙ "b" $ "c" $ fls


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.1. Exercise [⋆]
-- “Define logical `or` and `not` functions.”

    or  = ƛ "b" ∙ ƛ "c" ∙ "b" $ tru $ "c"
    not = ƛ "b" ∙ "b" $ fls $ tru


---------------------------------------------------------------------------------------------------------------
--
-- • Pairs

    pair = ƛ "f" ∙ ƛ "s" ∙ ƛ "b" ∙ "b" $ "f" $ "s"
    fst  = ƛ "p" ∙ "p" $ tru
    snd  = ƛ "p" ∙ "p" $ fls


---------------------------------------------------------------------------------------------------------------
--
-- • Church numerals

    c₀ = ƛ "s" ∙ ƛ "z" ∙ "z"
    c₁ = ƛ "s" ∙ ƛ "z" ∙ "s" $ "z"
    c₂ = ƛ "s" ∙ ƛ "z" ∙ "s" $ ("s" $ "z")
    c₃ = ƛ "s" ∙ ƛ "z" ∙ "s" $ ("s" $ ("s" $ "z"))

    sc = ƛ "n" ∙ ƛ "s" ∙ ƛ "z" ∙ "s" $ ("n" $ "s" $ "z")


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.2. Exercise [⋆⋆]
-- “Find another way to define the successor function on Church numerals.”

    sc2 = ƛ "n" ∙ ƛ "s" ∙ ƛ "z" ∙ "n" $ "s" $ ("s" $ "z")


---------------------------------------------------------------------------------------------------------------

    plus  = ƛ "m" ∙ ƛ "n" ∙ ƛ "s" ∙ ƛ "z" ∙ "m" $ "s" $ ("n" $ "s" $ "z")
    times = ƛ "m" ∙ ƛ "n" ∙ "m" $ (plus $ "n") $ c₀


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.3. Exercise [⋆⋆]
-- “Is it possible to define multiplication on Church numerals without using `plus`?”

    times2 = ƛ "m" ∙ ƛ "n" ∙ ƛ "s" ∙ ƛ "z" ∙ "m" $ ("n" $ "s") $ "z"
    times3 = ƛ "m" ∙ ƛ "n" ∙ ƛ "s" ∙ "m" $ ("n" $ "s")


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.4. Exercise [Recommended, ⋆⋆]
-- “Define a term for raising one number to the power of another.”

    pow = ƛ "n" ∙ ƛ "k" ∙ "k" $ (times $ "n") $ c₁


---------------------------------------------------------------------------------------------------------------

    iszro = ƛ "m" ∙ "m" $ (ƛ "x" ∙ fls) $ tru

    zz  = pair $ c₀ $ c₀
    ss  = ƛ "p" ∙ pair $ (snd $ "p") $ (plus $ c₁ $ (snd $ "p"))
    prd = ƛ "m" ∙ fst $ ("m" $ ss $ zz)


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.5. Exercise [⋆⋆]
-- “Use `prd` to define a subtraction function.”

    minus = ƛ "m" ∙ ƛ "n" ∙ "n" $ prd $ "m"


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.6. Exercise [⋆⋆]
-- “Approximately how many steps of evaluation (as a function of `n`) are required to calculate `prd cₙ`?”
-- (skipped)


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.7. Exercise [⋆⋆]
-- “Write a function `equal` that tests two numbers for equality and returns a Church boolean.”

    equal = ƛ "m" ∙ ƛ "n" ∙ {!!}


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.8. Exercise [Recommended, ⋆⋆⋆]
-- “A list can be represented in the lambda-calculus by its `fold` function. … What would the representation
-- of `nil` be?  Write a function `cons` that takes an element `h` and a list (that is, a fold function) `t`
-- and returns a similar representation of the list formed by prepending `h` to `t`.  Write `isnil` and `head`
-- functions, each taking a list parameter.  Finally, write a `tail` function for this representation of lists
-- (this is quite a bit harder and requires a trick analogous to the one used to define `prd` for numbers).

    nil   = {!!}
    cons  = {!!}
    isnil = {!!}
    head  = {!!}

    tail = {!!}


---------------------------------------------------------------------------------------------------------------
--
-- • Enriching the calculus

module LCNB
  where
    infixl 7 _$_
    data Term : Set₀ where
      `_   : ∀ (x : Name) → Term
      ƛ_∙_ : ∀ (x : Name) (t : Term) → Term
      _$_  : ∀ (t₁ t₂ : Term) → Term
      true false zero : Term
      suc pred iszero : ∀ (t : Term) → Term
      if_then_else    : ∀ (t₁ t₂ t₃ : Term) → Term

    instance
      Term-isString : IsString Term
      Term-isString = record
        { Constraint = λ s → ⊤
        ; fromString = λ s → ` name s
        }

    tru   = ƛ "t" ∙ ƛ "f" ∙ "t"
    fls   = ƛ "t" ∙ ƛ "f" ∙ "f"
    test  = ƛ "l" ∙ ƛ "m" ∙ ƛ "n" ∙ "l" $ "m" $ "n"
    and   = ƛ "b" ∙ ƛ "c" ∙ "b" $ "c" $ fls
    or    = ƛ "b" ∙ ƛ "c" ∙ "b" $ tru $ "c"
    not   = ƛ "b" ∙ "b" $ fls $ tru
    pair  = ƛ "f" ∙ ƛ "s" ∙ ƛ "b" ∙ "b" $ "f" $ "s"
    fst   = ƛ "p" ∙ "p" $ tru
    snd   = ƛ "p" ∙ "p" $ fls
    c₀    = ƛ "s" ∙ ƛ "z" ∙ "z"
    c₁    = ƛ "s" ∙ ƛ "z" ∙ "s" $ "z"
    c₂    = ƛ "s" ∙ ƛ "z" ∙ "s" $ ("s" $ "z")
    c₃    = ƛ "s" ∙ ƛ "z" ∙ "s" $ ("s" $ ("s" $ "z"))
    sc    = ƛ "n" ∙ ƛ "s" ∙ ƛ "z" ∙ "s" $ ("n" $ "s" $ "z")
    plus  = ƛ "m" ∙ ƛ "n" ∙ ƛ "s" ∙ ƛ "z" ∙ "m" $ "s" $ ("n" $ "s" $ "z")
    times = ƛ "m" ∙ ƛ "n" ∙ "m" $ (plus $ "n") $ c₀
    pow   = ƛ "n" ∙ ƛ "k" ∙ "k" $ (times $ "n") $ c₁
    iszro = ƛ "m" ∙ "m" $ (ƛ "x" ∙ fls) $ tru
    zz    = pair $ c₀ $ c₀
    ss    = ƛ "p" ∙ pair $ (snd $ "p") $ (plus $ c₁ $ (snd $ "p"))
    prd   = ƛ "m" ∙ fst $ ("m" $ ss $ zz)
    minus = {!!}
    equal = {!!}
    nil   = {!!}
    cons  = {!!}
    isnil = {!!}
    head  = {!!}
    tail  = {!!}

    realbool   = ƛ "b" ∙ "b" $ true $ false
    churchbool = ƛ "b" ∙ if "b" then tru else fls
    realeq     = ƛ "m" ∙ ƛ "n" ∙ (equal $ "m" $ "n") $ true $ false
    realnat    = ƛ "m" ∙ "m" $ (ƛ "x" ∙ suc "x") $ zero


---------------------------------------------------------------------------------------------------------------
--
-- • Recursion

    omega = (ƛ "x" ∙ "x" $ "x") $ (ƛ "x" ∙ "x" $ "x")
    fix   = ƛ "f" ∙ (ƛ "x" ∙ "f" $ (ƛ "y" ∙ "x" $ "x" $ "y")) $ (ƛ "x" ∙ "f" $ (ƛ "y" ∙ "x" $ "x" $ "y"))

    g         = ƛ "fct" ∙ ƛ "n" ∙ if realeq $ "n" $ c₀ then c₁ else (times $ "n" $ ("fct" $ (prd $ "n")))
    factorial = fix $ "g"


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.9. Exercise [⋆]
-- “Why did we use a primitive `if` in the definition of `g`, instead of the Church-boolean `test` function on
-- Church booleans?  Show how to define the `factorial` function in terms of `test` rather than `if`.

    factorial2 = {!!}


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.10. Exercise [⋆⋆]
-- “Define a function `churchnat` that converts a primitive natural number into the corresponding Church
-- numeral.”

    churchnat = {!!}


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.11. Exercise [Recommended, ⋆⋆]
-- “Use `fix` and the encoding of lists from Exercise 5.2.8 to write a function that sums lists of Church
-- numbers.”

    sum = {!!}


---------------------------------------------------------------------------------------------------------------
--
-- • Representation


---------------------------------------------------------------------------------------------------------------
--
-- 5.3. Formalities
--
-- • Syntax


---------------------------------------------------------------------------------------------------------------
--
-- 5.3.1. Definition [Terms]
-- “The set of terms is the smallest set `T` such that…”
-- (given above)
-- “The _size_ of a term `t` can be defined exactly as we did for arithmetic expressions in Definition 3.3.2.”

module LC-Part2
  where
    open LC-Part1 public

    size : Term → Nat
    size (` x)     = 1
    size (ƛ x ∙ t) = 1 + size t
    size (t₁ $ t₂) = 1 + (size t₁ + size t₂)


---------------------------------------------------------------------------------------------------------------
--
-- TODO

    _≟ᵀ_ : Decidable {A = Term} _≡_
    (` x)     ≟ᵀ (` y)        with x ≟ᴺ y
    ... | no x≢y              = no λ where refl → refl ↯ x≢y
    ... | yes refl            = yes refl
    (` x)     ≟ᵀ (ƛ y ∙ u)    = no λ ()
    (` x)     ≟ᵀ (u₁ $ u₂)    = no λ ()
    (ƛ x ∙ t) ≟ᵀ (` y)        = no λ ()
    (ƛ x ∙ t) ≟ᵀ (ƛ y ∙ u)    with x ≟ᴺ y | t ≟ᵀ u
    ... | no x≢y   | _        = no λ where refl → refl ↯ x≢y
    ... | yes refl | no t≢u   = no λ where refl → refl ↯ t≢u
    ... | yes refl | yes refl = yes refl
    (ƛ x ∙ t) ≟ᵀ (u₁ $ u₂)    = no λ ()
    (t₁ $ t₂) ≟ᵀ (` y)        = no λ ()
    (t₁ $ t₂) ≟ᵀ (ƛ y ∙ u)    = no λ ()
    (t₁ $ t₂) ≟ᵀ (u₁ $ u₂)    with t₁ ≟ᵀ u₁ | t₂ ≟ᵀ u₂
    ... | no t₁≢u₁ | _        = no λ where refl → refl ↯ t₁≢u₁
    ... | yes refl | no t₂≢u₂ = no λ where refl → refl ↯ t₂≢u₂
    ... | yes refl | yes refl = yes refl

    Term-decSetoid : DecSetoid _ _
    Term-decSetoid = record
      { Carrier = Term
      ; _≈_     = _≡_
      ; isDecEquivalence = record
        { isEquivalence = ≡-isEquivalence
        ; _≟_           = _≟ᵀ_
        }
      }

-- NOTE: Module bug here
-- module UniqueList-Term = MakeUniqueList (Term-decSetoid)


---------------------------------------------------------------------------------------------------------------
--
-- 5.3.2. Definition
-- “The set of _free variables_ of a term `t`, written `fv(t)`, is defined as follows: …”

    module _
      where
        open UniqueList-Name

        fv : Term → UniqueList
        fv (` x)     = [ x ]
        fv (ƛ x ∙ t) = fv t ∖ [ x ]
        fv (t₁ $ t₂) = fv t₁ ∪ fv t₂


---------------------------------------------------------------------------------------------------------------
--
-- 5.3.3. Exercise [⋆⋆]
-- “Give a careful proof that `|fv(t)| ≤ size(t)` for every term `t`.”

        exe-533 : ∀ t → length (fv t) ≤ size t
        exe-533 (` x)     = ≤-refl
        exe-533 (ƛ x ∙ t) = ≤-step
          (begin
            length (fv t ∖ [ x ])
          ≤⟨ length-untitled (fv t) [ x ] ⟩
            length (fv t)
          ≤⟨ exe-533 t ⟩
            size t
          ∎)
        exe-533 (t₁ $ t₂) = ≤-step
          (begin
            length (fv t₁ ∪ fv t₂)
          ≤⟨ length-triangular (fv t₁) (fv t₂) ⟩
            length (fv t₁) + length (fv t₂)
          ≤⟨ +-mono-≤ (exe-533 t₁) (exe-533 t₂) ⟩
            size t₁ + size t₂
          ∎)


---------------------------------------------------------------------------------------------------------------
--
-- • Substitution
--
-- 5.3.4. Convention
-- “Terms that differ only in the names of bound variables are interchangeable in all contexts. …”
-- “This convention renders the substitution operation ‘as good as total,’ since whenever we find ourselves
-- about to apply it to arguments for which it is undefined, we can rename as necessary, so that the side
-- conditions are satisfied.”
--
-- Unfortunately, ‘as good as total’ is not good enough.  We’re going to need to show that we can always get a
-- name that is not in a given set of names.

        fresh : UniqueList → Name
        fresh = {!!}

---------------------------------------------------------------------------------------------------------------
--
-- 5.3.5. Definition [Substitution]

{-
        [_↦_]_ : Name → Term → Term → Term
        [ x ↦ s ] (` y)              with x ≟ᴺ y
        ... | yes refl                = s
        ... | no x≢y                  = ` y
        [ x ↦ s ] (ƛ y ∙ t)          with x ≟ᴺ y | fv s T[∌]? x
        ... | yes refl | _            = ƛ y ∙ t
        ... | no x≢y   | yes T[fvs∌x] = ƛ y ∙ [ x ↦ s ] t
        ... | no x≢y   | no ¬T[fvs∌x] = let z = fresh (fv s ∪ fv t) in
                                        ƛ z ∙ ([ x ↦ s ] {![ y ↦ ` z ] t!})
        [ x ↦ s ] (t₁ $ t₂)          = ([ x ↦ s ] t₁) $ ([ x ↦ s ] t₂)
-}

        LessSize : Rel₀ Term
        LessSize t u = size t < size u

        ls-wf : WellFounded LessSize
        ls-wf = InverseImage.wellFounded size <-wf

        FewerFVs : Rel₀ Term
        FewerFVs t u = length (fv t) < length (fv u)

        ffv-wf : WellFounded FewerFVs
        ffv-wf = InverseImage.wellFounded (length ∘ fv) <-wf



        module Nat² = Lexicographic _<_ (λ _ → _<_)

        <²-wf : WellFounded Nat²._<_
        <²-wf = Nat².wellFounded <-wf <-wf

        measure : Term → Nat × Nat
        measure t = size t , length (fv t)

        infix 3 _⋖_
        _⋖_ : Rel₀ Term
        _⋖_ = Nat²._<_ Function.on measure

        measure-wf : WellFounded _⋖_
        measure-wf = InverseImage.wellFounded measure <²-wf

        ind-measure : ∀ {ℓ} {P : Pred Term ℓ} → InductionPrinciple _⋖_ P
        ind-measure = inductionPrinciple measure-wf

        size-positive : ∀ t → 1 ≤ size t
        size-positive (` x)     = ≤-refl
        size-positive (ƛ x ∙ t) = s≤s z≤n
        size-positive (t₁ $ t₂) = s≤s z≤n

        measure-ƛ : ∀ x t → t ⋖ ƛ x ∙ t
        measure-ƛ x t = Lexicographic.left ≤-refl

        ls-$₁ : ∀ t₁ t₂ → size t₁ < size (t₁ $ t₂)
        ls-$₁ t₁ t₂ = ≤-step
          (begin
            suc (size t₁)
          ≤⟨ +-monoˡ-≤ (size t₁) (size-positive t₂) ⟩
            size t₂ + size t₁
          ≡⟨ +-comm (size t₂) (size t₁) ⟩
            size t₁ + size t₂
          ∎)

        ls-$₂ : ∀ t₁ t₂ → size t₂ < size (t₁ $ t₂)
        ls-$₂ t₁ t₂ = ≤-step
          (begin
            suc (size t₂)
          ≤⟨ +-monoˡ-≤ (size t₂) (size-positive t₁) ⟩
            size t₁ + size t₂
          ∎)

        measure-$₁ : ∀ t₁ t₂ → t₁ ⋖ t₁ $ t₂
        measure-$₁ t₁ t₂ = Lexicographic.left (ls-$₁ t₁ t₂)

        measure-$₂ : ∀ t₁ t₂ → t₂ ⋖ t₁ $ t₂
        measure-$₂ t₁ t₂ = Lexicographic.left (ls-$₂ t₁ t₂)

        sub : Term → Name → Term →  Term
        sub = ind-measure λ where
          (` y)     h x s → case x ≟ᴺ y of λ where
            (yes refl)                → s
            (no x≢y)                  → ` y
          (ƛ y ∙ t) h x s → case x ≟ᴺ y , fv s T[∌]? x of λ where
            (yes refl , _)            → ƛ y ∙ t
            (no x≢y   , yes T[fvs∌x]) → ƛ y ∙ h t (measure-ƛ y t) x s
            (no x≢y   , no ¬T[fvs∌x]) → let
                                           z = fresh (fv s ∪ fv t)
                                         in
                                           ƛ z ∙ h (h t (measure-ƛ y t) y (` z)) {!!} x s
          (t₁ $ t₂) h x s             → h t₁ (measure-$₁ t₁ t₂) x s $ h t₂ (measure-$₂ t₁ t₂) x s


-- -- ---------------------------------------------------------------------------------------------------------------
-- -- --
-- -- -- • Operational semantics
-- -- --


-- -- ---------------------------------------------------------------------------------------------------------------
-- -- --
-- -- -- 5.3.6. Exercise [⋆⋆]
-- -- -- “Adapt these rules to describe the other strategies for evaluation—full beta-reduction, normal-order, and
-- -- -- lazy evaluation.”
-- -- -- TODO


-- -- ---------------------------------------------------------------------------------------------------------------
-- -- --
-- -- -- 5.3.7. Exercise [⋆⋆ ↛]
-- -- -- “Exercise 3.5.16 gave an alternate presentation of the operational semantics of booleans and arithmetic
-- -- -- expressions in which stuck terms are defined to evaluate to a special constant `wrong`.  Extend this
-- -- -- semantics to λNB.”
-- -- -- TODO


-- -- ---------------------------------------------------------------------------------------------------------------
-- -- --
-- -- -- 5.6.8. Exercise [⋆⋆]
-- -- -- “Exercise 4.2.2 introduced a “big-step” style of evaluation for arithmetic expressions, where the basic
-- -- -- evaluation relation is ‘term `t` evaluates to final result `v`’.  Show how to formulate the evaluation rules
-- -- -- for lambda-terms in the big-step style.”


-- -- ---------------------------------------------------------------------------------------------------------------
-- -- --
-- -- -- 5.4. Notes


-- -- ---------------------------------------------------------------------------------------------------------------
