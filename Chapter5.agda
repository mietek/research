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
--
-- TODO: Comment this

record IsλC (Term : Set₀) : Set₀ where
  infixl 7 _$_
  field
    `_   : ∀ (x : Name) → Term
    ƛ_∙_ : ∀ (x : Name) (t : Term) → Term
    _$_  : ∀ (t₁ t₂ : Term) → Term

record λC : Set₁ where
  field
    Term : Set₀
    isλC : IsλC Term

  open IsλC isλC public

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

module Church-Part1 (λc : λC)
  where
    open λC λc

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

-- TODO

    -- equal = ƛ "m" ∙ ƛ "n" ∙ {!!}


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.8. Exercise [Recommended, ⋆⋆⋆]
-- “A list can be represented in the lambda-calculus by its `fold` function. … What would the representation
-- of `nil` be?  Write a function `cons` that takes an element `h` and a list (that is, a fold function) `t`
-- and returns a similar representation of the list formed by prepending `h` to `t`.  Write `isnil` and `head`
-- functions, each taking a list parameter.  Finally, write a `tail` function for this representation of lists
-- (this is quite a bit harder and requires a trick analogous to the one used to define `prd` for numbers).

-- TODO

    -- nil   = {!!}
    -- cons  = {!!}
    -- isnil = {!!}
    -- head  = {!!}
    --
    -- tail = {!!}


---------------------------------------------------------------------------------------------------------------
--
-- • Enriching the calculus
--
-- TODO: Comment this

record IsλCNB (Term : Set₀) : Set₀ where
  field
    isλC            : IsλC Term
    true false zero : Term
    suc pred iszero : ∀ (t : Term) → Term
    if_then_else    : ∀ (t₁ t₂ t₃ : Term) → Term

  open IsλC isλC public

record λCNB : Set₁ where
  field
    Term   : Set₀
    isλCNB : IsλCNB Term

  open IsλCNB isλCNB public

  λc : λC
  λc = record { isλC = isλC }

  open λC λc public using (Term-isString)


module Church-Part2 (λcnb : λCNB)
  where
    open λCNB λcnb
    open Church-Part1 λc

    realbool   = ƛ "b" ∙ "b" $ true $ false
    churchbool = ƛ "b" ∙ if "b" then tru else fls

-- TODO

    -- realeq     = ƛ "m" ∙ ƛ "n" ∙ (equal $ "m" $ "n") $ true $ false
    realnat    = ƛ "m" ∙ "m" $ (ƛ "x" ∙ suc "x") $ zero


---------------------------------------------------------------------------------------------------------------
--
-- • Recursion

    omega = (ƛ "x" ∙ "x" $ "x") $ (ƛ "x" ∙ "x" $ "x")
    fix   = ƛ "f" ∙ (ƛ "x" ∙ "f" $ (ƛ "y" ∙ "x" $ "x" $ "y")) $ (ƛ "x" ∙ "f" $ (ƛ "y" ∙ "x" $ "x" $ "y"))

-- TODO

    -- g         = ƛ "fct" ∙ ƛ "n" ∙ if realeq $ "n" $ c₀ then c₁ else (times $ "n" $ ("fct" $ (prd $ "n")))
    -- factorial = fix $ "g"


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.9. Exercise [⋆]
-- “Why did we use a primitive `if` in the definition of `g`, instead of the Church-boolean `test` function on
-- Church booleans?  Show how to define the `factorial` function in terms of `test` rather than `if`.

-- TODO

    -- factorial2 = {!!}


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.10. Exercise [⋆⋆]
-- “Define a function `churchnat` that converts a primitive natural number into the corresponding Church
-- numeral.”

-- TODO

    -- churchnat = {!!}


---------------------------------------------------------------------------------------------------------------
--
-- 5.2.11. Exercise [Recommended, ⋆⋆]
-- “Use `fix` and the encoding of lists from Exercise 5.2.8 to write a function that sums lists of Church
-- numbers.”

    -- sum = {!!}


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

open Prelude using (suc ; zero)

module Functions
  where
    infixl 7 _$_
    data Term : Set₀ where
      `_   : ∀ (x : Name) → Term
      ƛ_∙_ : ∀ (x : Name) (t : Term) → Term
      _$_  : ∀ (t₁ t₂ : Term) → Term

    size : Term → Nat
    size (` x)     = 1
    size (ƛ x ∙ t) = 1 + size t
    size (t₁ $ t₂) = 1 + (size t₁ + size t₂)

    size-positive : ∀ t → 1 ≤ size t
    size-positive (` x)     = ≤-refl
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


-- TODO: Will this be needed?

    Functions-λc : λC
    Functions-λc = record
      { Term = Term
      ; isλC = record
        { `_   = `_
        ; ƛ_∙_ = ƛ_∙_
        ; _$_  = _$_
        }
      }


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

    Term-hasDecidableEquality : HasDecidableEquality Term
    _≟_ {{Term-hasDecidableEquality}} = _≟ᵀ_


---------------------------------------------------------------------------------------------------------------
--
-- 5.3.2. Definition
-- “The set of _free variables_ of a term `t`, written `fv(t)`, is defined as follows: …”

    fv : Term → UniqueList Name
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
--
-- TODO: Write this

    postulate
      fresh : UniqueList Name → Name
    -- fresh = {!!}

---------------------------------------------------------------------------------------------------------------
--
-- 5.3.5. Definition [Substitution]
--
-- TODO: Comment this

    module NotGood
      where
        {-# TERMINATING #-}
        [_↦_]_ : Name → Term → Term → Term
        [ x ↦ s ] (` y)              with x ≟ᴺ y
        ... | yes refl                = s
        ... | no x≢y                  = ` y
        [ x ↦ s ] (ƛ y ∙ t)          with x ≟ᴺ y | fv s T⟨∌⟩? x
        ... | yes refl | _            = ƛ y ∙ t
        ... | no x≢y   | yes T⟨fvs∌x⟩ = ƛ y ∙ [ x ↦ s ] t
        ... | no x≢y   | no ¬T⟨fvs∌x⟩ = let z = fresh (fv s ∪ fv t) in
                                        ƛ z ∙ [ x ↦ s ] ([ y ↦ ` z ] t)
        [ x ↦ s ] (t₁ $ t₂)          = ([ x ↦ s ] t₁) $ ([ x ↦ s ] t₂)

    ren : ∀ (t : Term) (x : Name) (z : Name) → ∃ λ t″ → size t ≡ size t″
    ren = indSize λ where
      (` y)     h x z → case x ≟ᴺ y of λ where
        (yes refl)                → ` z , refl
        (no x≢y)                  → ` y , refl
      (ƛ y ∙ t) h x z → case x ≟ᴺ y of λ where
        (yes refl)                → ƛ y ∙ t , refl
        (no x≢y)                  → let (t′ , s≡s′) = h t (<ˢ-abs x t) x z in
                                       ƛ y ∙ t′ , suc & s≡s′
      (t₁ $ t₂) h x z             → let (t₁′ , s₁≡s₁′) = h t₁ (<ˢ-app₁ t₁ t₂) x z in
                                     let (t₂′ , s₂≡s₂′) = h t₂ (<ˢ-app₂ t₁ t₂) x z in
                                       t₁′ $ t₂′ , (λ s₁ s₂ → suc (s₁ + s₂)) & s₁≡s₁′ ⊗ s₂≡s₂′

    sub : ∀ (t : Term) (x : Name) (s : Term) → Term
    sub = indSize λ where
      (` y)     h x s → case x ≟ᴺ y of λ where
        (yes refl)                → s
        (no x≢y)                  → ` y
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
    classify (` x)     = stu ((λ ()) , (λ ()))
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
-- TODO


---------------------------------------------------------------------------------------------------------------
--
-- 5.3.7. Exercise [⋆⋆ ↛]
-- “Exercise 3.5.16 gave an alternate presentation of the operational semantics of booleans and arithmetic
-- expressions in which stuck terms are defined to evaluate to a special constant `wrong`.  Extend this
-- semantics to λNB.”
-- TODO


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

    exe568-ltr : ∀ {t u} → (vᵤ : Value u) → t ⇓ u → t ⇒* u
    exe568-ltr vᵤ (e-val vₜ)                                = ε
    exe568-ltr vᵤ (e-appAbs vᵤ₂ t₁⇓ƛx∙u₁ t₂⇓u₂ [x↦u₂]u₁⇓u) = rs-app₁ (exe568-ltr (ƛ _ ∙ _) t₁⇓ƛx∙u₁) ◅◅
                                                              rs-app₂ (ƛ _ ∙ _) (exe568-ltr vᵤ₂ t₂⇓u₂) ◅◅
                                                              rs-appAbs vᵤ₂ ◅◅
                                                              (exe568-ltr vᵤ [x↦u₂]u₁⇓u)

-- TODO

    -- exe568-rtl : ∀ {t u} → (vᵤ : Value u) → t ⇒* u → t ⇓ u
    -- exe568-rtl vᵤ ε                               = e-val vᵤ
    -- exe568-rtl vᵤ (r-app₁ t₁⇒i₁ ◅ i₁$t₂⇒*u)     = {!!}
    -- exe568-rtl vᵤ (r-app₂ vₜ₁ t₂⇒i₂ ◅ t₁$i₂⇒*u) = {!!}
    -- exe568-rtl vᵤ (r-appAbs vₜ₂ ◅ [x↦t₂]t₁⇒*u)  = {!!}

---------------------------------------------------------------------------------------------------------------
--
-- 5.4. Notes


---------------------------------------------------------------------------------------------------------------
