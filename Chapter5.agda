---------------------------------------------------------------------------------------------------------------

module Chapter5 where

open import Prelude public
  hiding (false ; not ; suc ; true ; zero)

import Chapter3


---------------------------------------------------------------------------------------------------------------
--
-- 5. The untyped lambda-calculus
--

---------------------------------------------------------------------------------------------------------------
--
-- 5.1. Basics
-- “The syntax of the lambda-calculus comprises just three sorts of terms. …”

record IsLC (Term : Set₀) : Set₀ where
  infixl 7 _$_
  field
    !_   : ∀ (x : Name) → Term
    ƛ_∙_ : ∀ (x : Name) (t : Term) → Term
    _$_  : ∀ (t₁ t₂ : Term) → Term

record LC : Set₁ where
  field
    Term : Set₀
    isLC : IsLC Term

  open IsLC isLC public

  instance
    Term-isString : IsString Term
    Term-isString = record
      { Constraint = λ s → ⊤
      ; fromString = λ s → ! name s
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

module Church-Part1 (lc : LC)
  where
    open LC lc

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

    power = ƛ "n" ∙ ƛ "k" ∙ "k" $ (times $ "n") $ c₁


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

    equal = ƛ "m" ∙ ƛ "n" ∙ and $ (iszro $ ("m" $ prd $ "n"))
                                $ (iszro $ ("n" $ prd $ "m"))


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.8. Exercise [Recommended, ⋆⋆⋆]
-- “A list can be represented in the lambda-calculus by its `fold` function. … What would the representation
-- of `nil` be?  Write a function `cons` that takes an element `h` and a list (that is, a fold function) `t`
-- and returns a similar representation of the list formed by prepending `h` to `t`.  Write `isnil` and `head`
-- functions, each taking a list parameter.  Finally, write a `tail` function for this representation of lists
-- (this is quite a bit harder and requires a trick analogous to the one used to define `prd` for numbers).”

    nil   = ƛ "c" ∙ ƛ "n" ∙ "n"
    cons  = ƛ "h" ∙ ƛ "t" ∙ ƛ "c" ∙ ƛ "n" ∙ "c" $ "h" $ ("t" $ "c" $ "n")
    isnil = ƛ "l" ∙ "l" $ (ƛ "h" ∙ ƛ "t" ∙ fls) $ tru
    head  = ƛ "l" ∙ "l" $ (ƛ "h" ∙ ƛ "t" ∙ "h") $ fls

    tail = ƛ "l" ∙ fst $ "l" $ (ƛ "x" ∙ ƛ "p" ∙ pair $ (snd $ "p") $ (cons $ "x" $ (snd $ "p"))) $
                               (pair $ nil $ nil)


---------------------------------------------------------------------------------------------------------------
--
-- • Enriching the calculus

record IsLCNB (Term : Set₀) : Set₀ where
  field
    isLC            : IsLC Term
    true false zero : Term
    suc pred iszero : ∀ (t : Term) → Term
    if_then_else    : ∀ (t₁ t₂ t₃ : Term) → Term

  open IsLC isLC public

record LCNB : Set₁ where
  field
    Term   : Set₀
    isLCNB : IsLCNB Term

  open IsLCNB isLCNB public

  lc : LC
  lc = record { isLC = isLC }

  open LC lc public using (Term-isString)


module Church-Part2 (lcnb : LCNB)
  where
    open LCNB lcnb
    open Church-Part1 lc

    realbool   = ƛ "b" ∙ "b" $ true $ false
    churchbool = ƛ "b" ∙ if "b" then tru else fls

    realeq     = ƛ "m" ∙ ƛ "n" ∙ (equal $ "m" $ "n") $ true $ false
    realnat    = ƛ "m" ∙ "m" $ (ƛ "x" ∙ suc "x") $ zero


---------------------------------------------------------------------------------------------------------------
--
-- • Recursion

    omega = (ƛ "x" ∙ "x" $ "x") $ (ƛ "x" ∙ "x" $ "x")

    fix = ƛ "f" ∙ (ƛ "x" ∙ "f" $ (ƛ "y" ∙ "x" $ "x" $ "y")) $
                  (ƛ "x" ∙ "f" $ (ƛ "y" ∙ "x" $ "x" $ "y"))

    f-step = ƛ "f" ∙ ƛ "n" ∙
               if realeq $ "n" $ c₀
               then c₁
               else (times $ "n" $ ("f" $ (prd $ "n")))

    factorial = fix $ f-step


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.9. Exercise [⋆]
-- “Why did we use a primitive `if` in the definition of `g`, instead of the Church-boolean `test` function on
-- Church booleans?  Show how to define the `factorial` function in terms of `test` rather than `if`.

    f-step2 = ƛ "f" ∙ ƛ "n" ∙
                test $ (iszro $ "n") $
                       (ƛ "x" ∙ c₁) $
                       (ƛ "x" ∙ (times $ "n" $ ("f" $ (prd $ "n")))) $ c₀

    factorial2 = fix $ f-step2


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.10. Exercise [⋆⋆]
-- “Define a function `churchnat` that converts a primitive natural number into the corresponding Church
-- numeral.”

    cn-step = ƛ "f" ∙ ƛ "m" ∙
                if iszero "m"
                then c₀
                else sc $ ("f" $ (pred "m"))

    churchnat = fix $ cn-step


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.11. Exercise [Recommended, ⋆⋆]
-- “Use `fix` and the encoding of lists from Exercise 5.2.8 to write a function that sums lists of Church
-- numbers.”

    s-step = ƛ "f" ∙ ƛ "l" ∙
               test $ (isnil $ "l") $
                      (ƛ "x" ∙ c₀) $
                      (ƛ "x" ∙ (plus $ (head $ "l") $ ("f" $ (tail $ "l")))) $ c₀

    sum = fix $ s-step


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
-- “The _size_ of a term `t` can be defined exactly as we did for arithmetic expressions in Definition 3.3.2.”

open Prelude using (suc ; zero)

module Functions
  where
    infixl 7 _$_
    data Term : Set₀ where
      !_   : ∀ (x : Name) → Term
      ƛ_∙_ : ∀ (x : Name) (t : Term) → Term
      _$_  : ∀ (t₁ t₂ : Term) → Term

    Functions-lc : LC
    Functions-lc = record
      { Term = Term
      ; isLC = record
        { !_   = !_
        ; ƛ_∙_ = ƛ_∙_
        ; _$_  = _$_
        }
      }

    size : Term → Nat
    size (! x)     = 1
    size (ƛ x ∙ t) = 1 + size t
    size (t₁ $ t₂) = 1 + (size t₁ + size t₂)

    size-positive : ∀ t → 1 ≤ size t
    size-positive (! x)     = ≤-refl
    size-positive (ƛ x ∙ t) = s≤s z≤n
    size-positive (t₁ $ t₂) = s≤s z≤n

    infix 5 _<ˢ_
    _<ˢ_ : Rel₀ Term
    _<ˢ_ = _<_ on size

    <ˢ-abs : ∀ x t → t <ˢ ƛ x ∙ t
    <ˢ-abs x t = ≤-refl

    <ˢ-abs′ : ∀ x t t′ → size t ≡ size t′ → t′ <ˢ ƛ x ∙ t
    <ˢ-abs′ x t t′ s≡s′ = begin
        suc (size t′)
      ≡⟨ suc & (s≡s′ ⁻¹) ⟩
        suc (size t)
      ∎

    <ˢ-app₁ : ∀ t₁ t₂ → t₁ <ˢ t₁ $ t₂
    <ˢ-app₁ t₁ t₂ = ≤-step
      (begin
        suc (size t₁)
      ≤⟨ +-monoˡ-≤ (size t₁) (size-positive t₂) ⟩
        size t₂ + size t₁
      ≡⟨ +-comm (size t₂) (size t₁) ⟩
        size t₁ + size t₂
      ∎)

    <ˢ-app₂ : ∀ t₁ t₂ → t₂ <ˢ t₁ $ t₂
    <ˢ-app₂ t₁ t₂ = ≤-step
      (begin
        suc (size t₂)
      ≤⟨ +-monoˡ-≤ (size t₂) (size-positive t₁) ⟩
        size t₁ + size t₂
      ∎)

    <ˢ-wellFounded : WellFounded _<ˢ_
    <ˢ-wellFounded = InverseImage.wellFounded size <-wellFounded

    indSize : ∀ {ℓ} {P : Pred Term ℓ} → InductionPrinciple _<ˢ_ P
    indSize = indWith <ˢ-wellFounded


---------------------------------------------------------------------------------------------------------------
--
-- Decidable equality.

    _≟ᵀ_ : Decidable {A = Term} _≡_
    (! x)     ≟ᵀ (! y)        with x ≟ᴺ y
    ... | no x≢y              = no λ where refl → refl ↯ x≢y
    ... | yes refl            = yes refl
    (! x)     ≟ᵀ (ƛ y ∙ u)    = no λ ()
    (! x)     ≟ᵀ (u₁ $ u₂)    = no λ ()
    (ƛ x ∙ t) ≟ᵀ (! y)        = no λ ()
    (ƛ x ∙ t) ≟ᵀ (ƛ y ∙ u)    with x ≟ᴺ y | t ≟ᵀ u
    ... | no x≢y   | _        = no λ where refl → refl ↯ x≢y
    ... | yes refl | no t≢u   = no λ where refl → refl ↯ t≢u
    ... | yes refl | yes refl = yes refl
    (ƛ x ∙ t) ≟ᵀ (u₁ $ u₂)    = no λ ()
    (t₁ $ t₂) ≟ᵀ (! y)        = no λ ()
    (t₁ $ t₂) ≟ᵀ (ƛ y ∙ u)    = no λ ()
    (t₁ $ t₂) ≟ᵀ (u₁ $ u₂)    with t₁ ≟ᵀ u₁ | t₂ ≟ᵀ u₂
    ... | no t₁≢u₁ | _        = no λ where refl → refl ↯ t₁≢u₁
    ... | yes refl | no t₂≢u₂ = no λ where refl → refl ↯ t₂≢u₂
    ... | yes refl | yes refl = yes refl

    Term-hasDecidableEquality : HasDecidableEquality Term
    Term-hasDecidableEquality = record { _≟_ = _≟ᵀ_ }


---------------------------------------------------------------------------------------------------------------
--
-- 5.3.2. Definition
-- “The set of _free variables_ of a term `t`, written `fv(t)`, is defined as follows: …”

    fv : Term → UniqueList Name
    fv (! x)     = [ x ]
    fv (ƛ x ∙ t) = fv t ∖ [ x ]
    fv (t₁ $ t₂) = fv t₁ ∪ fv t₂


---------------------------------------------------------------------------------------------------------------
--
-- 5.3.3. Exercise [⋆⋆]
-- “Give a careful proof that `|fv(t)| ≤ size(t)` for every term `t`.”

    exe533 : ∀ t → length (fv t) ≤ size t
    exe533 (! x)     = ≤-refl
    exe533 (ƛ x ∙ t) = ≤-step
      (begin
        length (fv t ∖ [ x ])
      ≤⟨ length-untitled (fv t) [ x ] ⟩
        length (fv t)
      ≤⟨ exe533 t ⟩
        size t
      ∎)
    exe533 (t₁ $ t₂) = ≤-step
      (begin
        length (fv t₁ ∪ fv t₂)
      ≤⟨ length-triangular (fv t₁) (fv t₂) ⟩
        length (fv t₁) + length (fv t₂)
      ≤⟨ +-mono-≤ (exe533 t₁) (exe533 t₂) ⟩
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


-- TODO: Write `fresh`.

    postulate
      fresh : UniqueList Name → Name

---------------------------------------------------------------------------------------------------------------
--
-- 5.3.5. Definition [Substitution]
--
-- A direct definition is not recognised by Agda as structurally recursive, because the termination checker
-- doesn’t know that renaming `y` to `z` in `t` is size-preserving.

    private
      module NotGood where
        {-# TERMINATING #-}
        [_↦_]_ : Name → Term → Term → Term
        [ x ↦ s ] (! y)              with x ≟ᴺ y
        ... | yes refl                = s
        ... | no x≢y                  = ! y
        [ x ↦ s ] (ƛ y ∙ t)          with x ≟ᴺ y | fv s T⟨∌⟩? x
        ... | yes refl | _            = ƛ y ∙ t
        ... | no x≢y   | yes T⟨fvs∌x⟩ = ƛ y ∙ [ x ↦ s ] t
        ... | no x≢y   | no ¬T⟨fvs∌x⟩ = let z = fresh (fv s ∪ fv t) in
                                          ƛ z ∙ [ x ↦ s ] ([ y ↦ ! z ] t)
        [ x ↦ s ] (t₁ $ t₂)          = ([ x ↦ s ] t₁) $ ([ x ↦ s ] t₂)


-- To help the termination checker, we’ll require renaming to supply evidence that size has been preserved, and
-- use this evidence for substitution.  To highlight the similarity between renaming and substitution, we give
-- both using explicit induction on size, even though renaming could also be given directly.

    ren : ∀ (t : Term) → Name → Name → ∃ λ t′ → size t ≡ size t′
    ren = indSize λ where
      (! y)     h x z → case x ≟ᴺ y of λ where
        (yes refl)                → ! z , refl
        (no x≢y)                  → ! y , refl
      (ƛ y ∙ t) h x z → case x ≟ᴺ y of λ where
        (yes refl)                → ƛ y ∙ t , refl
        (no x≢y)                  → let (t′ , s≡s′) = h t (<ˢ-abs x t) x z in
                                       ƛ y ∙ t′ , suc & s≡s′
      (t₁ $ t₂) h x z             → let (t₁′ , s₁≡s₁′) = h t₁ (<ˢ-app₁ t₁ t₂) x z in
                                     let (t₂′ , s₂≡s₂′) = h t₂ (<ˢ-app₂ t₁ t₂) x z in
                                       t₁′ $ t₂′ , (λ s₁ s₂ → suc (s₁ + s₂)) & s₁≡s₁′ ⊗ s₂≡s₂′

    sub : ∀ (t : Term) → Name → Term → Term
    sub = indSize λ where
      (! y)     h x s → case x ≟ᴺ y of λ where
        (yes refl)                → s
        (no x≢y)                  → ! y
      (ƛ y ∙ t) h x s → case x ≟ᴺ y , fv s T⟨∌⟩? x of λ where
        (yes refl , _)            → ƛ y ∙ t
        (no x≢y   , yes T⟨fvs∌x⟩) → ƛ y ∙ h t (<ˢ-abs x t) x s
        (no x≢y   , no ¬T⟨fvs∌x⟩) → let z = fresh (fv s ∪ fv t) in
                                     let (t′ , s≡s′) = ren t y z in
                                       ƛ z ∙ h t′ (<ˢ-abs′ x t t′ s≡s′) x s
      (t₁ $ t₂) h x s             → h t₁ (<ˢ-app₁ t₁ t₂) x s $ h t₂ (<ˢ-app₂ t₁ t₂) x s

    [_↦_]_ : Name → Term → Term → Term
    [ x ↦ s ] t = sub t x s


---------------------------------------------------------------------------------------------------------------
--
-- • Operational semantics

module FunctionsGetStuck
  where
    open Functions public

    data Value : Pred₀ Term where
      ƛ_∙_ : ∀ (x : Name) (t : Term) → Value (ƛ x ∙ t)


-- Echo of Definition 3.5.3.

    infix 3 _⇒_
    data _⇒_ : Rel₀ Term where
      r-app₁   : ∀ {t₁ t₂ u₁} → t₁ ⇒ u₁ → t₁ $ t₂ ⇒ u₁ $ t₂
      r-app₂   : ∀ {t₁ t₂ u₂} → (vₜ₁ : Value t₁) → t₂ ⇒ u₂ → t₁ $ t₂ ⇒ t₁ $ u₂
      r-appAbs : ∀ {x t₁ t₂} → (vₜ₂ : Value t₂) → (ƛ x ∙ t₁) $ t₂ ⇒ [ x ↦ t₂ ] t₁


-- Echo of Definition 3.5.6.

    open Chapter3.NormalForms _⇒_ public


-- Echo of Theorem 3.5.7.

    v→nf : ∀ {t} → Value t → NormalForm t
    v→nf (ƛ x ∙ t) = λ ()


-- Echo of Theorem 3.5.4.

    ⇒-det : ∀ {t u u′} → t ⇒ u → t ⇒ u′ → u ≡ u′
    ⇒-det (r-app₁ t₁⇒u₁)     (r-app₁ t₁⇒u₁′)     = (_$ _) & ⇒-det t₁⇒u₁ t₁⇒u₁′
    ⇒-det (r-app₁ t₁⇒u₁)     (r-app₂ vₜ₁ _)       = t₁⇒u₁ ↯ v→nf vₜ₁
    ⇒-det (r-app₁ ())         (r-appAbs _)
    ⇒-det (r-app₂ vₜ₁ _)      (r-app₁ t₁⇒u₁)      = t₁⇒u₁ ↯ v→nf vₜ₁
    ⇒-det (r-app₂ vₜ₁ t₂⇒u₂) (r-app₂ vₜ₂ t₂⇒u₂′) = (_ $_) & ⇒-det t₂⇒u₂ t₂⇒u₂′
    ⇒-det (r-app₂ _ t₂⇒u₂)   (r-appAbs vₜ₂)       = t₂⇒u₂ ↯ v→nf vₜ₂
    ⇒-det (r-appAbs _)        (r-app₁ ())
    ⇒-det (r-appAbs vₜ₂)      (r-app₂ _ t₂⇒u₂)    = t₂⇒u₂ ↯ v→nf vₜ₂
    ⇒-det (r-appAbs vₜ₂)      (r-appAbs vₜ₂′)      = refl


-- Every term is either stuck, a value, or reducible to another term.

    Stuck : Pred₀ Term
    Stuck t = ¬ Value t × NormalForm t

    data Stuck/Value/Reducible : Pred₀ Term where
      stu : ∀ {t} → (σₜ : Stuck t) → Stuck/Value/Reducible t
      val : ∀ {t} → (vₜ : Value t) → Stuck/Value/Reducible t
      red : ∀ {t} → (rₜ : Reducible t) → Stuck/Value/Reducible t

    σ-appStuck₁ : ∀ {t₁ t₂} → Stuck t₁ → Stuck (t₁ $ t₂)
    σ-appStuck₁ (¬vₜ₁ , nfₜ₁) = (λ ())
                              , (λ where (r-app₁ t₁⇒u₁)     → t₁⇒u₁ ↯ nfₜ₁
                                         (r-app₂ vₜ₁ t₂⇒u₂) → vₜ₁ ↯ ¬vₜ₁
                                         (r-appAbs vₜ₂)      → (ƛ _ ∙ _) ↯ ¬vₜ₁)

    σ-appStuck₂ : ∀ {t₁ t₂} → Value t₁ → Stuck t₂ → Stuck (t₁ $ t₂)
    σ-appStuck₂ vₜ₁ (¬vₜ₂ , nfₜ₂) = (λ ())
                                  , (λ where (r-app₁ t₁⇒u₁)     → t₁⇒u₁ ↯ v→nf vₜ₁
                                             (r-app₂ vₜ₁ t₂⇒u₂) → t₂⇒u₂ ↯ nfₜ₂
                                             (r-appAbs vₜ₂)      → vₜ₂ ↯ ¬vₜ₂)

    classify : ∀ t → Stuck/Value/Reducible t
    classify (! x)     = stu ((λ ()) , (λ ()))
    classify (ƛ x ∙ t) = val (ƛ x ∙ t)
    classify (t₁ $ t₂) with classify t₁ | classify t₂
    ... | stu σₜ₁          | _                = stu (σ-appStuck₁ σₜ₁)
    ... | val vₜ₁          | stu σₜ₂          = stu (σ-appStuck₂ vₜ₁ σₜ₂)
    ... | val (ƛ _ ∙ _)    | val vₜ₂          = red (_ , r-appAbs vₜ₂)
    ... | val vₜ₁          | red (_ , t₂⇒u₂) = red (_ , r-app₂ vₜ₁ t₂⇒u₂)
    ... | red (_ , t₁⇒u₁) | _                = red (_ , r-app₁ t₁⇒u₁)


-- Echo of Theorem 3.5.8.

    data Stuck/Value : Pred₀ Term where
      stu : ∀ {t} → (σₜ : Stuck t) → Stuck/Value t
      val : ∀ {t} → (vₜ : Value t) → Stuck/Value t

    nf→σ/v : ∀ {t} → NormalForm t → Stuck/Value t
    nf→σ/v {t} nfₜ  with classify t
    ... | stu σₜ         = stu σₜ
    ... | val vₜ         = val vₜ
    ... | red (_ , t⇒u) = t⇒u ↯ nfₜ


-- Echo of Definition 3.5.9 and Theorem 3.5.11.

    open Chapter3.MultiStepReduction _⇒_ public
    open Chapter3.UniquenessOfNormalForms _⇒_ ⇒-det public

    rs-app₁ : ∀ {t₁ t₂ u₁} → t₁ ⇒* u₁ → t₁ $ t₂ ⇒* u₁ $ t₂
    rs-app₁ = map r-app₁

    rs-app₂ : ∀ {t₁ t₂ u₂} → (vₜ₁ : Value t₁) → t₂ ⇒* u₂ → t₁ $ t₂ ⇒* t₁ $ u₂
    rs-app₂ vₜ₁ = map (r-app₂ vₜ₁)

    rs-appAbs : ∀ {x t₁ t₂} → (vₜ₂ : Value t₂) → (ƛ x ∙ t₁) $ t₂ ⇒* [ x ↦ t₂ ] t₁
    rs-appAbs vₜ₂ = r-appAbs vₜ₂ ◅ ε


---------------------------------------------------------------------------------------------------------------
--
-- 5.3.6. Exercise [⋆⋆]
-- “Adapt these rules to describe the other strategies for evaluation—full beta-reduction, normal-order, and
-- lazy evaluation.”

module NonDeterministic
  where
    open Functions public

    infix 3 _⇒_
    data _⇒_ : Rel₀ Term where
      r-app₁   : ∀ {t₁ t₂ u₁} → t₁ ⇒ u₁ → t₁ $ t₂ ⇒ u₁ $ t₂
      r-app₂   : ∀ {t₁ t₂ u₂} → t₂ ⇒ u₂ → t₁ $ t₂ ⇒ t₁ $ u₂
      r-appAbs : ∀ {x t₁ t₂} → (ƛ x ∙ t₁) $ t₂ ⇒ [ x ↦ t₂ ] t₁


module NormalOrder
  where
    open Functions public

    mutual
      data NormalForm : Pred₀ Term where
        ƛ_∙_ : ∀ x {t} → (nfₜ : NormalForm t) → NormalForm (ƛ x ∙ t)
        nanf : ∀ {t} → (nanfₜ : NonAbstractionNormalForm t) → NormalForm t

      data NonAbstractionNormalForm : Pred₀ Term where
        !_  : ∀ x → NonAbstractionNormalForm (! x)
        _$_ : ∀ {t₁ t₂} → (nanfₜ₁ : NonAbstractionNormalForm t₁) (nfₜ₂ : NormalForm t₂) →
              NonAbstractionNormalForm (t₁ $ t₂)

    data NonAbstraction : Pred₀ Term where
      !_  : ∀ x → NonAbstraction (! x)
      _$_ : ∀ t₁ t₂ → NonAbstraction (t₁ $ t₂)

    infix 3 _⇒_
    data _⇒_ : Rel₀ Term where
      r-app₁   : ∀ {t₁ t₂ u₁} → (naₜ₁ : NonAbstraction t₁) (naᵤ₁ : NonAbstraction u₁) → t₁ ⇒ u₁ →
                 t₁ $ t₂ ⇒ u₁ $ t₂
      r-app₂   : ∀ {t₁ t₂ u₂} → (nanfₜ₁ : NonAbstractionNormalForm t₁) → t₂ ⇒ u₂ → t₁ $ t₂ ⇒ t₁ $ u₂
      r-appAbs : ∀ {x t₁ t₂} → (ƛ x ∙ t₁) $ t₂ ⇒ [ x ↦ t₂ ] t₁


module CallByName
  where
    open Functions public

    data Value : Pred₀ Term where
      ƛ_∙_ : ∀ (x : Name) (t : Term) → Value (ƛ x ∙ t)

    infix 3 _⇒_
    data _⇒_ : Rel₀ Term where
      r-app₁   : ∀ {t₁ t₂ u₁} → t₁ ⇒ u₁ → t₁ $ t₂ ⇒ u₁ $ t₂
      r-appAbs : ∀ {x t₁ t₂} → (ƛ x ∙ t₁) $ t₂ ⇒ [ x ↦ t₂ ] t₁


---------------------------------------------------------------------------------------------------------------
--
-- 5.3.7. Exercise [⋆⋆ ↛]
-- “Exercise 3.5.16 gave an alternate presentation of the operational semantics of booleans and arithmetic
-- expressions in which stuck terms are defined to evaluate to a special constant `wrong`.  Extend this
-- semantics to λNB.”
-- (skipped)


---------------------------------------------------------------------------------------------------------------
--
-- 5.3.8. Exercise [⋆⋆]
-- “Exercise 4.2.2 introduced a “big-step” style of evaluation for arithmetic expressions, where the basic
-- evaluation relation is ‘term `t` evaluates to final result `v`’.  Show how to formulate the evaluation rules
-- for lambda-terms in the big-step style.”

private
  module Exercise538 where
    open FunctionsGetStuck

    infix 3 _⇓_
    data _⇓_ : Rel₀ Term where
      e-val    : ∀ {t} → (vₜ : Value t) → t ⇓ t
      e-appAbs : ∀ {x t₁ t₂ u₁ u₂ u} → (vᵤ₂ : Value u₂) → t₁ ⇓ ƛ x ∙ u₁ → t₂ ⇓ u₂ → [ x ↦ u₂ ] u₁ ⇓ u →
                 t₁ $ t₂ ⇓ u


-- As an exercise, we show that the small-step and big-step semantics coincide.

    exe568-ltr : ∀ {t u} → (vᵤ : Value u) → t ⇓ u → t ⇒* u
    exe568-ltr vᵤ (e-val vₜ)
        = ε
    exe568-ltr vᵤ (e-appAbs vᵤ₂ t₁⇓ƛx∙u₁ t₂⇓u₂ [x↦u₂]u₁⇓u)
        = rs-app₁ (exe568-ltr (ƛ _ ∙ _) t₁⇓ƛx∙u₁) ◅◅
          rs-app₂ (ƛ _ ∙ _) (exe568-ltr vᵤ₂ t₂⇓u₂) ◅◅
          rs-appAbs vᵤ₂ ◅◅
          (exe568-ltr vᵤ [x↦u₂]u₁⇓u)

    lem-app₁ : ∀ {t₁ t₂ u} → (vᵤ : Value u) → t₁ $ t₂ ⇒* u →
               ∃ λ x → ∃ λ u₁ → ∃ λ u₂ → Value u₂ × t₁ ⇒* ƛ x ∙ u₁ × t₂ ⇒* u₂ × [ x ↦ u₂ ] u₁ ⇒* u
    lem-app₁ () ε
    lem-app₁ vᵤ (r-app₁ t₁⇒i₁ ◅ i₁$t₂⇒*u) with lem-app₁ vᵤ i₁$t₂⇒*u
    ... | x , u₁ , u₂ , vᵤ₂ , i₁⇒*ƛx∙u₁          , t₂⇒*u₂ , [x↦u₂]u₁⇒*u
        = x , u₁ , u₂ , vᵤ₂ , t₁⇒i₁ ◅ i₁⇒*ƛx∙u₁ , t₂⇒*u₂ , [x↦u₂]u₁⇒*u
    lem-app₁ vᵤ (r-app₂ vₜ₁ t₂⇒i₂ ◅ t₁$i₂⇒*u) with lem-app₁ vᵤ t₁$i₂⇒*u
    ... | x , u₁ , u₂ , vᵤ₂ , t₁⇒*ƛx∙u₁ , i₂⇒*u₂          , [x↦u₂]u₁⇒*u
        = x , u₁ , u₂ , vᵤ₂ , t₁⇒*ƛx∙u₁ , t₂⇒i₂ ◅ i₂⇒*u₂ , [x↦u₂]u₁⇒*u
    lem-app₁ vᵤ (r-appAbs {x} {t₁} vₜ₂ ◅ [x↦t₂]t₁⇒*u)
        = x , t₁ , _ , vₜ₂ , ε , ε , [x↦t₂]t₁⇒*u

    lem-app₂ : ∀ {x t₂ u u₁} → (vᵤ : Value u) → ƛ x ∙ u₁ $ t₂ ⇒* u →
               ∃ λ u₂ → Value u₂ × t₂ ⇒* u₂ × [ x ↦ u₂ ] u₁ ⇒* u
    lem-app₂ () ε
    lem-app₂ vᵤ (r-app₁ () ◅ _)
    lem-app₂ vᵤ (r-app₂ vₜ₁ t₂⇒i₂ ◅ t₁$i₂⇒*u) with lem-app₂ vᵤ t₁$i₂⇒*u
    ... | u₂ , vᵤ₂ , i₂⇒*u₂ , [x↦u₂]t₁⇒*u
        = u₂ , vᵤ₂ , t₂⇒i₂ ◅ i₂⇒*u₂ , [x↦u₂]t₁⇒*u
    lem-app₂ vᵤ (r-appAbs vₜ₂ ◅ [x↦t₂]t₁⇒*u)
        = _ , vₜ₂ , ε , [x↦t₂]t₁⇒*u


-- TODO: Rewrite `exe568-rtl` using explicit induction.

    private
      module NotGood where
        {-# TERMINATING #-}
        exe568-rtl : ∀ {t u} → (vᵤ : Value u) → t ⇒* u → t ⇓ u
        exe568-rtl vᵤ ε
            = e-val vᵤ
        exe568-rtl vᵤ (r-app₁ t₁⇒i₁ ◅ i₁$t₂⇒*u) with lem-app₁ vᵤ i₁$t₂⇒*u
        ... | x , u₁ , u₂ , vᵤ₂ , i₁⇒*ƛx∙u₁ , t₂⇒*u₂ , [x↦u₂]u₁⇒*u
            = e-appAbs vᵤ₂ (exe568-rtl (ƛ _ ∙ _) (t₁⇒i₁ ◅ i₁⇒*ƛx∙u₁))
                           (exe568-rtl vᵤ₂ t₂⇒*u₂)
                           (exe568-rtl vᵤ [x↦u₂]u₁⇒*u)
        exe568-rtl vᵤ (r-app₂ vₜ₁@(ƛ _ ∙ _) t₂⇒i₂ ◅ t₁$i₂⇒*u) with lem-app₂ vᵤ t₁$i₂⇒*u
        ... | u₂ , vᵤ₂ , i₂⇒*u₂ , [x↦u₂]u₁⇒*u
            = e-appAbs vᵤ₂ (e-val vₜ₁)
                           (exe568-rtl vᵤ₂ (t₂⇒i₂ ◅ i₂⇒*u₂))
                           (exe568-rtl vᵤ [x↦u₂]u₁⇒*u)
        exe568-rtl vᵤ (r-appAbs vₜ₂ ◅ [x↦t₂]t₁⇒*u)
            = e-appAbs vₜ₂ (e-val (ƛ _ ∙ _))
                           (e-val vₜ₂)
                           (exe568-rtl vᵤ [x↦t₂]t₁⇒*u)

        exe568 : ∀ {t u} → (vᵤ : Value u) → (t ⇓ u) ↔ (t ⇒* u)
        exe568 vᵤ = exe568-ltr vᵤ , exe568-rtl vᵤ


---------------------------------------------------------------------------------------------------------------
--
-- 5.4. Notes


---------------------------------------------------------------------------------------------------------------
