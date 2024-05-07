---------------------------------------------------------------------------------------------------------------

module A201901.Chapter3 where

open import A201901.Prelude public


---------------------------------------------------------------------------------------------------------------
--
-- 3. Untyped arithmetic expressions
--
-- 3.1. Introduction
--
-- 3.2. Syntax


---------------------------------------------------------------------------------------------------------------
--
-- 3.2.1. Definition [Terms, inductively]
-- “The set of _terms_ is the smallest set `T` such that …”

module NumbersAndBooleans-Part1
  where
    data Term : Set₀ where
      true false zero : Term
      suc pred iszero : ∀ (t : Term) → Term
      if_then_else    : ∀ (t₁ t₂ t₃ : Term) → Term


---------------------------------------------------------------------------------------------------------------
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


---------------------------------------------------------------------------------------------------------------
--
-- 3.3. Induction on terms
--
-- Since we’re working in type theory, we’re going to need a type of containers that are not allowed to contain
-- duplicate elements, `UniqueList`.  To put terms in such a container, we’re going to need a decidable
-- equality on terms.  Therefore, we’re going to show that the built-in Agda equality, `_≡_`, is decidable for
-- terms.

    _≟ᵀ_ : Decidable {A = Term} _≡_
    true                  ≟ᵀ true                  = yes refl
    true                  ≟ᵀ false                 = no λ ()
    true                  ≟ᵀ zero                  = no λ ()
    true                  ≟ᵀ suc _                 = no λ ()
    true                  ≟ᵀ pred _                = no λ ()
    true                  ≟ᵀ iszero _              = no λ ()
    true                  ≟ᵀ if _ then _ else _    = no λ ()
    false                 ≟ᵀ true                  = no λ ()
    false                 ≟ᵀ false                 = yes refl
    false                 ≟ᵀ zero                  = no λ ()
    false                 ≟ᵀ suc _                 = no λ ()
    false                 ≟ᵀ pred _                = no λ ()
    false                 ≟ᵀ iszero _              = no λ ()
    false                 ≟ᵀ if _ then _ else _    = no λ ()
    zero                  ≟ᵀ true                  = no λ ()
    zero                  ≟ᵀ false                 = no λ ()
    zero                  ≟ᵀ zero                  = yes refl
    zero                  ≟ᵀ suc _                 = no λ ()
    zero                  ≟ᵀ pred _                = no λ ()
    zero                  ≟ᵀ iszero _              = no λ ()
    zero                  ≟ᵀ if _ then _ else _    = no λ ()
    suc _                 ≟ᵀ true                  = no λ ()
    suc _                 ≟ᵀ false                 = no λ ()
    suc _                 ≟ᵀ zero                  = no λ ()
    suc t                 ≟ᵀ suc u                 with t ≟ᵀ u
    ... | no t≢u                                   = no λ where refl → refl ↯ t≢u
    ... | yes refl                                 = yes refl
    suc _                 ≟ᵀ pred _                = no λ ()
    suc _                 ≟ᵀ iszero _              = no λ ()
    suc _                 ≟ᵀ if _ then _ else _    = no λ ()
    pred _                ≟ᵀ true                  = no λ ()
    pred _                ≟ᵀ false                 = no λ ()
    pred _                ≟ᵀ zero                  = no λ ()
    pred _                ≟ᵀ suc _                 = no λ ()
    pred t                ≟ᵀ pred u                with t ≟ᵀ u
    ... | no t≢u                                   = no λ where refl → refl ↯ t≢u
    ... | yes refl                                 = yes refl
    pred _                ≟ᵀ iszero _              = no λ ()
    pred _                ≟ᵀ if _ then _ else _    = no λ ()
    iszero _              ≟ᵀ true                  = no λ ()
    iszero _              ≟ᵀ false                 = no λ ()
    iszero _              ≟ᵀ zero                  = no λ ()
    iszero _              ≟ᵀ suc _                 = no λ ()
    iszero _              ≟ᵀ pred _                = no λ ()
    iszero t              ≟ᵀ iszero u              with t ≟ᵀ u
    ... | no t≢u                                   = no λ where refl → refl ↯ t≢u
    ... | yes refl                                 = yes refl
    iszero _              ≟ᵀ if _ then _ else _    = no λ ()
    if _ then _ else _    ≟ᵀ true                  = no λ ()
    if _ then _ else _    ≟ᵀ false                 = no λ ()
    if _ then _ else _    ≟ᵀ zero                  = no λ ()
    if _ then _ else _    ≟ᵀ suc _                 = no λ ()
    if _ then _ else _    ≟ᵀ pred _                = no λ ()
    if _ then _ else _    ≟ᵀ iszero _              = no λ ()
    if t₁ then t₂ else t₃ ≟ᵀ if u₁ then u₂ else u₃ with t₁ ≟ᵀ u₁ | t₂ ≟ᵀ u₂ | t₃ ≟ᵀ u₃
    ... | no t₁≢u₁ | _        | _                  = no λ where refl → refl ↯ t₁≢u₁
    ... | yes refl | no t₂≢u₂ | _                  = no λ where refl → refl ↯ t₂≢u₂
    ... | yes refl | yes refl | no t₃≢u₃           = no λ where refl → refl ↯ t₃≢u₃
    ... | yes refl | yes refl | yes refl           = yes refl

    instance
      Term-hasDecidableEquality : HasDecidableEquality Term
      Term-hasDecidableEquality = record { _≟_ = _≟ᵀ_ }


---------------------------------------------------------------------------------------------------------------
--
-- 3.3.1. Definition
-- “The set of constants appearing in a term `t`, written `consts(t)`, is defined as follows: …”

    consts : Term → UniqueList Term
    consts true                    = [ true ]
    consts false                   = [ false ]
    consts zero                    = [ zero ]
    consts (suc t)                 = consts t
    consts (pred t)                = consts t
    consts (iszero t)              = consts t
    consts (if t₁ then t₂ else t₃) = consts t₁ ∪ consts t₂ ∪ consts t₃


---------------------------------------------------------------------------------------------------------------
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
    depth (if t₁ then t₂ else t₃) = 1 + (depth t₁ ⊔ depth t₂ ⊔ depth t₃)


---------------------------------------------------------------------------------------------------------------
--
-- 3.3.3. Lemma
-- “The number of distinct constants in a term `t` is no greater than the size of `t` (i.e.,
-- `|consts(t)| ≤ size(t)`).”
--
-- As an exercise, we’re going to prove Lemma 3.3.3 using four methods.  First, the most natural method to use
-- in Agda, a direct proof using pattern matching.

    lem333 : ∀ t → length (consts t) ≤ size t
    lem333 true                    = ≤-refl
    lem333 false                   = ≤-refl
    lem333 zero                    = ≤-refl
    lem333 (suc t)                 = ≤-step (lem333 t)
    lem333 (pred t)                = ≤-step (lem333 t)
    lem333 (iszero t)              = ≤-step (lem333 t)
    lem333 (if t₁ then t₂ else t₃) = ≤-step
      (begin
        length (consts t₁ ∪ consts t₂ ∪ consts t₃)
      ≤⟨ length-triangular (consts t₁ ∪ consts t₂) (consts t₃) ⟩
        length (consts t₁ ∪ consts t₂) + length (consts t₃)
      ≤⟨ +-monoˡ-≤ (length (consts t₃)) (length-triangular (consts t₁) (consts t₂)) ⟩
        length (consts t₁) + length (consts t₂) + length (consts t₃)
      ≤⟨ +-mono-≤ (+-mono-≤ (lem333 t₁) (lem333 t₂))
                  (lem333 t₃) ⟩
        size t₁ + size t₂ + size t₃
      ∎)


---------------------------------------------------------------------------------------------------------------
--
-- 3.3.4. Theorem [Principles of induction on terms]
--
-- 3.3.4.a. Structural induction
-- “If, for each term `t`, given `P(s)` for all immediate subterms `s` of `t` we can show `P(t)`, then `P(t)`
-- holds for all `t`.
--
-- We’re going to start by defining what it means for a term to be an immediate subterm of another term.

    data _∈_ : Rel₀ Term where
      suc    : ∀ {t} → t ∈ suc t
      pred   : ∀ {t} → t ∈ pred t
      iszero : ∀ {t} → t ∈ iszero t
      if₁    : ∀ {t₁ t₂ t₃} → t₁ ∈ if t₁ then t₂ else t₃
      if₂    : ∀ {t₁ t₂ t₃} → t₂ ∈ if t₁ then t₂ else t₃
      if₃    : ∀ {t₁ t₂ t₃} → t₃ ∈ if t₁ then t₂ else t₃


-- As an exercise, we’re going to define structural induction using two methods.  First, a direct definition
-- using pattern matching.

    indStruct : ∀ {ℓ} {P : Pred Term ℓ} → (∀ t → (∀ s →  s ∈ t → P s) → P t) → ∀ t → P t
    indStruct h t@true                 = h t λ s ()
    indStruct h t@false                = h t λ s ()
    indStruct h t@zero                 = h t λ s ()
    indStruct h t@(suc _)              = h t λ where s suc    → indStruct h s
    indStruct h t@(pred _)             = h t λ where s pred   → indStruct h s
    indStruct h t@(iszero _)           = h t λ where s iszero → indStruct h s
    indStruct h t@(if _ then _ else _) = h t λ where s if₁    → indStruct h s
                                                     s if₂    → indStruct h s
                                                     s if₃    → indStruct h s


-- Second, a definition based on well-founded induction and accessibility, using equipment from the Agda
-- standard library.  Some of the definitions referenced are a little difficult to understand, as acknowledged
-- in the documentation.

    ∈-wellFounded : WellFounded _∈_
    ∈-wellFounded s = acc λ where
      t suc    → ∈-wellFounded t
      t pred   → ∈-wellFounded t
      t iszero → ∈-wellFounded t
      t₁ if₁   → ∈-wellFounded t₁
      t₂ if₂   → ∈-wellFounded t₂
      t₃ if₃   → ∈-wellFounded t₃

    indStruct-stdlib : ∀ {ℓ} {P : Pred Term ℓ} → InductionPrinciple _∈_ P
    indStruct-stdlib = indWith ∈-wellFounded


-- A proof of Lemma 3.3.3 using structural induction.

    lem333-struct : ∀ t → length (consts t) ≤ size t
    lem333-struct = indStruct λ where
      true                    h → ≤-refl
      false                   h → ≤-refl
      zero                    h → ≤-refl
      (suc t)                 h → ≤-step (h t suc)
      (pred t)                h → ≤-step (h t pred)
      (iszero t)              h → ≤-step (h t iszero)
      (if t₁ then t₂ else t₃) h → ≤-step
        (begin
          length (consts t₁ ∪ consts t₂ ∪ consts t₃)
        ≤⟨ length-triangular (consts t₁ ∪ consts t₂) (consts t₃) ⟩
          length (consts t₁ ∪ consts t₂) + length (consts t₃)
        ≤⟨ +-monoˡ-≤ (length (consts t₃)) (length-triangular (consts t₁) (consts t₂)) ⟩
          length (consts t₁) + length (consts t₂) + length (consts t₃)
        ≤⟨ +-mono-≤ (+-mono-≤ (h t₁ if₁) (h t₂ if₂))
                    (h t₃ if₃) ⟩
          size t₁ + size t₂ + size t₃
        ∎)


---------------------------------------------------------------------------------------------------------------
--
-- 3.3.4.b. Induction on size
-- “If, for each term `t`, given `P(s)` for all `s` such that `size(s) < size(t)` we can show `P(t)`, then
-- `P(t)` holds for all `t`.”
--
-- A definition based on well-founded induction.

    _<ˢ_ : Rel₀ Term
    _<ˢ_ = _<_ on size

    <ˢ-if₁ : ∀ t₁ t₂ t₃ → t₁ <ˢ if t₁ then t₂ else t₃
    <ˢ-if₁ t₁ t₂ t₃ = s≤s (m≤m+n+o (size t₁) (size t₂) (size t₃))

    <ˢ-if₂ : ∀ t₁ t₂ t₃ → t₂ <ˢ if t₁ then t₂ else t₃
    <ˢ-if₂ t₁ t₂ t₃ = s≤s (n≤m+n+o (size t₁) (size t₂) (size t₃))

    <ˢ-if₃ : ∀ t₁ t₂ t₃ → t₃ <ˢ if t₁ then t₂ else t₃
    <ˢ-if₃ t₁ t₂ t₃ = s≤s (o≤m+n+o (size t₁) (size t₂) (size t₃))

    <ˢ-wellFounded : WellFounded _<ˢ_
    <ˢ-wellFounded = InverseImage.wellFounded size <-wellFounded

    indSize : ∀ {ℓ} {P : Pred Term ℓ} → InductionPrinciple _<ˢ_ P
    indSize = indWith <ˢ-wellFounded


-- Another proof of Lemma 3.3.3 using induction on size.

    lem333-size : ∀ t → length (consts t) ≤ size t
    lem333-size = indSize λ where
      true                    h → ≤-refl
      false                   h → ≤-refl
      zero                    h → ≤-refl
      (suc t)                 h → ≤-step (h t ≤-refl)
      (pred t)                h → ≤-step (h t ≤-refl)
      (iszero t)              h → ≤-step (h t ≤-refl)
      (if t₁ then t₂ else t₃) h → ≤-step
        (begin
          length (consts t₁ ∪ consts t₂ ∪ consts t₃)
        ≤⟨ length-triangular (consts t₁ ∪ consts t₂) (consts t₃) ⟩
          length (consts t₁ ∪ consts t₂) + length (consts t₃)
        ≤⟨ +-monoˡ-≤ (length (consts t₃)) (length-triangular (consts t₁) (consts t₂)) ⟩
          length (consts t₁) + length (consts t₂) + length (consts t₃)
        ≤⟨ +-mono-≤ (+-mono-≤ (h t₁ (<ˢ-if₁ t₁ t₂ t₃)) (h t₂ (<ˢ-if₂ t₁ t₂ t₃)))
                    (h t₃ (<ˢ-if₃ t₁ t₂ t₃)) ⟩
          size t₁ + size t₂ + size t₃
        ∎)


---------------------------------------------------------------------------------------------------------------
--
-- 3.3.4.c. Induction on depth
-- “If, for each term `t`, given `P(s)` for all `s` such that `depth(s) < depth(t)` we can show `P(t)`, then
-- `P(t)` holds for all `t`.”
--
-- A definition based on well-founded induction.

    _<ᵈ_ : Rel₀ Term
    _<ᵈ_ = _<_ on depth

    <ᵈ-if₁ : ∀ t₁ t₂ t₃ → t₁ <ᵈ if t₁ then t₂ else t₃
    <ᵈ-if₁ t₁ t₂ t₃ = s≤s (m≤m⊔n⊔o (depth t₁) (depth t₂) (depth t₃))

    <ᵈ-if₂ : ∀ t₁ t₂ t₃ → t₂ <ᵈ if t₁ then t₂ else t₃
    <ᵈ-if₂ t₁ t₂ t₃ = s≤s (n≤m⊔n⊔o (depth t₁) (depth t₂) (depth t₃))

    <ᵈ-if₃ : ∀ t₁ t₂ t₃ → t₃ <ᵈ if t₁ then t₂ else t₃
    <ᵈ-if₃ t₁ t₂ t₃ = s≤s (o≤m⊔n⊔o (depth t₁) (depth t₂) (depth t₃))

    <ᵈ-wellFounded : WellFounded _<ᵈ_
    <ᵈ-wellFounded = InverseImage.wellFounded depth <-wellFounded

    indDepth : ∀ {ℓ} {P : Pred Term ℓ} → InductionPrinciple _<ᵈ_ P
    indDepth = indWith <ᵈ-wellFounded


-- Another proof of Lemma 3.3.3 using induction on depth.

    lem333-depth : ∀ t → length (consts t) ≤ size t
    lem333-depth = indDepth λ where
      true                    h → ≤-refl
      false                   h → ≤-refl
      zero                    h → ≤-refl
      (suc t)                 h → ≤-step (h t ≤-refl)
      (pred t)                h → ≤-step (h t ≤-refl)
      (iszero t)              h → ≤-step (h t ≤-refl)
      (if t₁ then t₂ else t₃) h → ≤-step
        (begin
          length (consts t₁ ∪ consts t₂ ∪ consts t₃)
        ≤⟨ length-triangular (consts t₁ ∪ consts t₂) (consts t₃) ⟩
          length (consts t₁ ∪ consts t₂) + length (consts t₃)
        ≤⟨ +-monoˡ-≤ (length (consts t₃)) (length-triangular (consts t₁) (consts t₂)) ⟩
          length (consts t₁) + length (consts t₂) + length (consts t₃)
        ≤⟨ +-mono-≤ (+-mono-≤ (h t₁ (<ᵈ-if₁ t₁ t₂ t₃)) (h t₂ (<ᵈ-if₂ t₁ t₂ t₃)))
                    (h t₃ (<ᵈ-if₃ t₁ t₂ t₃)) ⟩
          size t₁ + size t₂ + size t₃
        ∎)


---------------------------------------------------------------------------------------------------------------
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
      if_then_else : ∀ (t₁ t₂ t₃ : Term) → Term

    data Value : Pred₀ Term where
      true  : Value true
      false : Value false


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.1. Definition
-- “An _instance_ of an inference rule is obtained by consistently replacing each metavariable by the same term
-- in the rule’s conclusion and all its premises (if any).”
--
-- In Agda, we model inference rules as constructors of inductive type families.  Thus, instances of inference
-- rules are obtained using Agda’s built-in notion of substitution.
--
-- 3.5.2. Definition
-- “A rule is _satisfied_ by a relation if, for each instance of the rule, either the conclusion is in the
-- relation or one of the premises is not.”
--
-- In our model, a rule is satisfied by an inductive type family if, given evidence for all of the premises, a
-- constructor of the type family serves as evidence for the conclusion.


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.3. Definition
-- “The _one-step reduction_ relation `⇒` is the smallest binary relation on terms satisfying the three rules
-- in …”
--
-- We say `t ⇒ u` to mean that `t` reduces to `u` in one step.

    infix 3 _⇒_
    data _⇒_ : Rel₀ Term where
      r-ifTrue  : ∀ {t₂ t₃} → if true then t₂ else t₃ ⇒ t₂
      r-ifFalse : ∀ {t₂ t₃} → if false then t₂ else t₃ ⇒ t₃
      r-if      : ∀ {t₁ t₂ t₃ u₁} → t₁ ⇒ u₁ → if t₁ then t₂ else t₃ ⇒ if u₁ then t₂ else t₃


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.4. Theorem [Determinacy of one-step reduction]
-- “If `t ⇒ u` and `t ⇒ u′`, then `u ≡ u′`.
--
-- Before we can prove this theorem, we need to jump ahead to Definition 3.5.6 and say what it means for a term
-- to be in _normal form_.  In type theory, it is often more convenient to use a positive definition.  For this
-- reason, we also define what it means for a term to be _reducible_.  We give both definitions in a generic
-- manner, parametrised by the one-step reduction relation, so that they can be reused in later sections.

module NormalForms {t ℓ} {Term : Set t}
    (_⇒_ : Rel Term ℓ)
  where
    NormalForm : Pred Term (t ⊔ᴸ ℓ)
    NormalForm t = ∀ {u} → ¬ (t ⇒ u)

    Reducible : Pred Term (t ⊔ᴸ ℓ)
    Reducible t = ∃ λ u → t ⇒ u

    nf→¬r : ∀ {t} → NormalForm t → ¬ Reducible t
    nf→¬r nfₜ (_ , t⇒u) = t⇒u ↯ nfₜ

    ¬r→nf : ∀ {t} → ¬ Reducible t → NormalForm t
    ¬r→nf ¬rₜ t⇒u = (_ , t⇒u) ↯ ¬rₜ


-- We also need to jump ahead to Theorem 3.5.7, and show that every value is in normal form.

module BooleansOnly-Part2
  where
    open BooleansOnly-Part1 public
    open NormalForms _⇒_ public

    v→nf : ∀ {t} → Value t → NormalForm t
    v→nf true  = λ ()
    v→nf false = λ ()

    ⇒-det : ∀ {t u u′} → t ⇒ u → t ⇒ u′ → u ≡ u′
    ⇒-det r-ifTrue      r-ifTrue       = refl
    ⇒-det r-ifTrue      (r-if t⇒u₁′)  = t⇒u₁′ ↯ v→nf true
    ⇒-det r-ifFalse     r-ifFalse      = refl
    ⇒-det r-ifFalse     (r-if f⇒u₁′)  = f⇒u₁′ ↯ v→nf false
    ⇒-det (r-if t⇒u₁)  r-ifTrue       = t⇒u₁ ↯ v→nf true
    ⇒-det (r-if f⇒u₁)  r-ifFalse      = f⇒u₁ ↯ v→nf false
    ⇒-det (r-if t₁⇒u₁) (r-if t₁⇒u₁′) = (λ u₁″ → if u₁″ then _ else _) & ⇒-det t₁⇒u₁ t₁⇒u₁′


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.5. Exercise [⋆]
-- “Spell out the induction principle used in the preceding proof, in the style of Theorem 3.3.4.”
-- (skipped)
--
-- 3.5.6. Definition
-- “A term `t` is in _normal form_ if no evaluation rule applies to it—i.e., if there is no `t′` such that
-- `t ⇒ t′`.  (We sometimes say ‘`t` is a normal form’ as shorthand for ‘`t` is a term in normal form.’)”
-- (given above)
--
-- 3.5.7. Theorem
-- “Every value is in normal form.”
-- (given above)


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.8. Theorem
-- “If `t` is in normal form, then `t` is a value.”
--
-- To prove this theorem, we’re first going to show that every term is either a value, or reducible to another
-- term.

    data Value/Reducible : Pred₀ Term where
      val : ∀ {t} → (vₜ : Value t) → Value/Reducible t
      red : ∀ {t} → (rₜ : Reducible t) → Value/Reducible t

    classify : ∀ t → Value/Reducible t
    classify true                    = val true
    classify false                   = val false
    classify (if t₁ then t₂ else t₃) with classify t₁
    ... | val true                   = red (_ , r-ifTrue)
    ... | val false                  = red (_ , r-ifFalse)
    ... | red (_ , t₁⇒u₁)           = red (_ , r-if t₁⇒u₁)

    nf→v : ∀ {t} → NormalForm t → Value t
    nf→v {t} nfₜ        with classify t
    ... | val vₜ         = vₜ
    ... | red (_ , t⇒u) = t⇒u ↯ nfₜ


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.9. Definition
-- “The _multi-step reduction_ relation `⇒*` is the reflexive, transitive closure of one-step reduction.  That
-- is, it is the smallest relation such that (1) if `t ⇒ u` then `t ⇒* u`, (2) `t ⇒* t` for all `t`, and (3)
-- if `s ⇒* t` and `t ⇒* u`, then `s ⇒* u`.”
--
-- We say `t ⇒* u` to mean that `t` reduces to `u` in multiple steps.  We give this definition in a generic
-- manner.

module MultiStepReduction {a ℓ} {A : Set a}
    (_⇒_ : Rel A ℓ)
  where
    infix 3 _⇒*_
    _⇒*_ : Rel A (a ⊔ᴸ ℓ)
    _⇒*_ = _⇒_ *


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.10. Exercise [*]
-- “Rephrase Definition 3.5.9 as a set of inference rules.”
-- (redundant)


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.11. Theorem [Uniqueness of normal forms]
-- “If `t ⇒* u` and `t ⇒* u′`, where `u` and `u′` are both normal forms, then `u ≡ u′`.”

module UniquenessOfNormalForms {a ℓ} {A : Set a}
    (_⇒_ : Rel A ℓ)
    (⇒-det : ∀ {t u u′} → t ⇒ u → t ⇒ u′ → u ≡ u′)
  where
    open NormalForms _⇒_
    open MultiStepReduction _⇒_

    ⇒*-unf : ∀ {t u u′} → NormalForm u → NormalForm u′ → t ⇒* u → t ⇒* u′ → u ≡ u′
    ⇒*-unf nfₜ nfₜ′ ε              ε                 = refl
    ⇒*-unf nfₜ nfᵤ′ ε              (t⇒x′ ◅ x′⇒*u′) = t⇒x′ ↯ nfₜ
    ⇒*-unf nfᵤ nfₜ  (t⇒x ◅ x⇒*u) ε                 = t⇒x ↯ nfₜ
    ⇒*-unf nfᵤ nfᵤ′ (t⇒x ◅ x⇒*u) (t⇒x′ ◅ x′⇒*u′) with ⇒-det t⇒x t⇒x′
    ... | refl                                        = ⇒*-unf nfᵤ nfᵤ′ x⇒*u x′⇒*u′


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.12. Theorem [Termination of evaluation]
-- “For every term `t` there is some normal form `u` such that `t ⇒* u`.”
--
-- We first derive multi-step analogues of single-step reduction rules, then show a variant of this theorem
-- that uses the notion of value instead of normal form.

module BooleansOnly-Part3
  where
    open BooleansOnly-Part2 public
    open MultiStepReduction _⇒_ public
    open UniquenessOfNormalForms _⇒_ ⇒-det public

    rs-ifTrue : ∀ {t₂ t₃} → if true then t₂ else t₃ ⇒* t₂
    rs-ifTrue = r-ifTrue ◅ ε

    rs-ifFalse : ∀ {t₂ t₃} → if false then t₂ else t₃ ⇒* t₃
    rs-ifFalse = r-ifFalse ◅ ε

    rs-if : ∀ {t₁ t₂ t₃ u₁} → t₁ ⇒* u₁ → if t₁ then t₂ else t₃ ⇒* if u₁ then t₂ else t₃
    rs-if = map r-if

    halt : ∀ t → ∃ λ u → Value u × t ⇒* u
    halt true                                        = _ , true , ε
    halt false                                       = _ , false , ε
    halt (if t₁ then t₂ else t₃)                     with halt t₁ | halt t₂ | halt t₃
    ... | _ , true  , t₁⇒*t | _ , vᵤ₂ , t₂⇒*u₂ | _ = _ , vᵤ₂ , rs-if t₁⇒*t ◅◅ rs-ifTrue ◅◅ t₂⇒*u₂
    ... | _ , false , t₁⇒*f | _ | _ , vᵤ₃ , t₃⇒*u₃ = _ , vᵤ₃ , rs-if t₁⇒*f ◅◅ rs-ifFalse ◅◅ t₃⇒*u₃

    halt′ : ∀ t → ∃ λ u → NormalForm u × t ⇒* u
    halt′ t               with halt t
    ... | _ , vᵤ , t⇒*u = _ , v→nf vᵤ , t⇒*u


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.13. Exercise [Recommended, ⋆⋆]
-- “1. Suppose we add a new rule…”
-- “2. Suppose instead that we add this rule…”
-- (skipped)


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.14. Exercise [⋆⋆]
-- ”Show that Theorem 3.5.4 is also valid for the reduction relation on arithmetic expressions: if `t ⇒ u` and
-- `t ⇒ u′`, then `u ≡ u′`.”

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

    infix 3 _⇒_
    data _⇒_ : Rel₀ Term where
      r-suc        : ∀ {t u} → t ⇒ u → suc t ⇒ suc u
      r-predZero   : pred zero ⇒ zero
      r-predSuc    : ∀ {t} → (nvₜ : NumericValue t) → pred (suc t) ⇒ t
      r-pred       : ∀ {t u} → t ⇒ u → pred t ⇒ pred u
      r-iszeroZero : iszero zero ⇒ true
      r-iszeroSuc  : ∀ {t} → (nvₜ : NumericValue t) → iszero (suc t) ⇒ false
      r-iszero     : ∀ {t u} → t ⇒ u → iszero t ⇒ iszero u
      r-ifTrue     : ∀ {t₂ t₃} → if true then t₂ else t₃ ⇒ t₂
      r-ifFalse    : ∀ {t₂ t₃} → if false then t₂ else t₃ ⇒ t₃
      r-if         : ∀ {t₁ t₂ t₃ u₁} → t₁ ⇒ u₁ → if t₁ then t₂ else t₃ ⇒ if u₁ then t₂ else t₃


-- Echo of Definition 3.5.6.

    open NormalForms _⇒_ public


-- Echo of Theorem 3.5.7.

    nv→nf : ∀ {t} → NumericValue t → NormalForm t
    nv→nf zero      = λ ()
    nv→nf (suc nvₜ) = λ where (r-suc t⇒u) → t⇒u ↯ nv→nf nvₜ

    v→nf : ∀ {t} → Value t → NormalForm t
    v→nf true      = λ ()
    v→nf false     = λ ()
    v→nf (num nvₜ) = nv→nf nvₜ


-- Echo of Theorem 3.5.4.

    ⇒-det : ∀ {t u u′} → t ⇒ u → t ⇒ u′ → u ≡ u′
    ⇒-det (r-suc t⇒u)        (r-suc t⇒u′)     = suc & ⇒-det t⇒u t⇒u′
    ⇒-det r-predZero          r-predZero        = refl
    ⇒-det r-predZero          (r-pred z⇒u′)    = z⇒u′ ↯ nv→nf zero
    ⇒-det (r-predSuc _)       (r-predSuc _)     = refl
    ⇒-det (r-predSuc nvₜ)     (r-pred st⇒u′)   = st⇒u′ ↯ nv→nf (suc nvₜ)
    ⇒-det (r-pred z⇒u)       r-predZero        = z⇒u ↯ nv→nf zero
    ⇒-det (r-pred st⇒u)      (r-predSuc nvₜ)   = st⇒u ↯ nv→nf (suc nvₜ)
    ⇒-det (r-pred t⇒u)       (r-pred t⇒u′)    = pred & ⇒-det t⇒u t⇒u′
    ⇒-det r-iszeroZero        r-iszeroZero      = refl
    ⇒-det r-iszeroZero        (r-iszero z⇒u′ ) = z⇒u′ ↯ nv→nf zero
    ⇒-det (r-iszeroSuc _)     (r-iszeroSuc _)   = refl
    ⇒-det (r-iszeroSuc nvₜ)   (r-iszero st⇒u′) = st⇒u′ ↯ nv→nf (suc nvₜ)
    ⇒-det (r-iszero z⇒u)     r-iszeroZero      = z⇒u ↯ nv→nf zero
    ⇒-det (r-iszero st⇒u)    (r-iszeroSuc nvₜ) = st⇒u ↯ nv→nf (suc nvₜ)
    ⇒-det (r-iszero t⇒u)     (r-iszero t⇒u′)  = iszero & ⇒-det t⇒u t⇒u′
    ⇒-det r-ifTrue            r-ifTrue          = refl
    ⇒-det r-ifTrue            (r-if t⇒u₁′)     = t⇒u₁′ ↯ v→nf true
    ⇒-det r-ifFalse           r-ifFalse         = refl
    ⇒-det r-ifFalse           (r-if f⇒u₁′)     = f⇒u₁′ ↯ v→nf false
    ⇒-det (r-if t⇒u₁)        r-ifTrue          = t⇒u₁ ↯ v→nf true
    ⇒-det (r-if f⇒u₁)        r-ifFalse         = f⇒u₁ ↯ v→nf false
    ⇒-det (r-if t₁⇒u₁)       (r-if t₁⇒u₁′)    = (λ u₁″ → if u₁″ then _ else _) & ⇒-det t₁⇒u₁ t₁⇒u₁′


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.15. Definition
-- “A closed term is _stuck_ if it is in normal form but not a value.”
--
-- As an exercise, we’re going to show that evaluation of expressions-that--get-stuck is terminating.

module NumbersAndBooleansGetStuck
  where
    open NumbersAndBooleans-Part2 public


-- Every term is either stuck, a value, or reducible to another term.

    Stuck : Pred₀ Term
    Stuck t = ¬ Value t × NormalForm t

    data Stuck/Value/Reducible : Pred₀ Term where
      stu : ∀ {t} → (σₜ : Stuck t) → Stuck/Value/Reducible t
      val : ∀ {t} → (vₜ : Value t) → Stuck/Value/Reducible t
      red : ∀ {t} → (rₜ : Reducible t) → Stuck/Value/Reducible t

    σ-sucStuck : ∀ {t} → Stuck t → Stuck (suc t)
    σ-sucStuck (¬vₜ , nfₜ) = (λ where (num (suc nvₜ)) → num nvₜ ↯ ¬vₜ)
                           , (λ where (r-suc t⇒u) → t⇒u ↯ nfₜ)

    σ-sucTrue : Stuck (suc true)
    σ-sucTrue = (λ where (num (suc ())))
              , (λ where (r-suc ()))

    σ-sucFalse : Stuck (suc false)
    σ-sucFalse = (λ where (num (suc ())))
               , (λ where (r-suc ()))

    σ-predStuck : ∀ {t} → Stuck t → Stuck (pred t)
    σ-predStuck (¬vₜ , nfₜ) = (λ where (num ()))
                            , (λ where r-predZero      → num zero ↯ ¬vₜ
                                       (r-predSuc nvₜ) → num (suc nvₜ) ↯ ¬vₜ
                                       (r-pred t⇒u)   → t⇒u ↯ nfₜ)

    σ-predTrue : Stuck (pred true)
    σ-predTrue = (λ where (num ()))
               , (λ where (r-pred ()))

    σ-predFalse : Stuck (pred false)
    σ-predFalse = (λ where (num ()))
                , (λ where (r-pred ()))

    σ-iszeroStuck : ∀ {t} → Stuck t → Stuck (iszero t)
    σ-iszeroStuck (¬vₜ , nfₜ) = (λ where (num ()))
                              , (λ where r-iszeroZero      → num zero ↯ ¬vₜ
                                         (r-iszeroSuc nvₜ) → num (suc nvₜ) ↯ ¬vₜ
                                         (r-iszero t⇒u)   → t⇒u ↯ nfₜ)

    σ-iszeroTrue : Stuck (iszero true)
    σ-iszeroTrue = (λ where (num ()))
                 , (λ where (r-iszero ()))

    σ-iszeroFalse : Stuck (iszero false)
    σ-iszeroFalse = (λ where (num ()))
                  , (λ where (r-iszero ()))

    σ-ifStuck : ∀ {t₁ t₂ t₃} → Stuck t₁ → Stuck (if t₁ then t₂ else t₃)
    σ-ifStuck (¬vₜ₁ , nfₜ₁) = (λ where (num ()))
                            , (λ where r-ifTrue      → true ↯ ¬vₜ₁
                                       r-ifFalse     → false ↯ ¬vₜ₁
                                       (r-if t₁⇒u₁) → t₁⇒u₁ ↯ nfₜ₁)

    σ-ifZero : ∀ {t₂ t₃} → Stuck (if zero then t₂ else t₃)
    σ-ifZero = (λ where (num ()))
             , (λ where (r-if ()))

    σ-ifSuc : ∀ {t₁ t₂ t₃} → NumericValue t₁ → Stuck (if (suc t₁) then t₂ else t₃)
    σ-ifSuc nvₜ₁ = (λ where (num ()))
                 , (λ where (r-if (r-suc t₁⇒u₁)) → t₁⇒u₁ ↯ nv→nf nvₜ₁)

    classify : ∀ t → Stuck/Value/Reducible t
    classify true                    = val true
    classify false                   = val false
    classify zero                    = val (num zero)
    classify (suc t)                 with classify t
    ... | stu σₜ                     = stu (σ-sucStuck σₜ)
    ... | val true                   = stu σ-sucTrue
    ... | val false                  = stu σ-sucFalse
    ... | val (num nvₜ)              = val (num (suc nvₜ))
    ... | red (_ , t⇒u)             = red (_ , r-suc t⇒u)
    classify (pred t)                with classify t
    ... | stu σₜ                     = stu (σ-predStuck σₜ)
    ... | val true                   = stu σ-predTrue
    ... | val false                  = stu σ-predFalse
    ... | val (num zero)             = red (_ , r-predZero)
    ... | val (num (suc nvₜ))        = red (_ , r-predSuc nvₜ)
    ... | red (_ , t⇒u)             = red (_ , r-pred t⇒u)
    classify (iszero t)              with classify t
    ... | stu σₜ                     = stu (σ-iszeroStuck σₜ)
    ... | val true                   = stu σ-iszeroTrue
    ... | val false                  = stu σ-iszeroFalse
    ... | val (num zero)             = red (_ , r-iszeroZero)
    ... | val (num (suc nvₜ))        = red (_ , r-iszeroSuc nvₜ)
    ... | red (_ , t⇒u)             = red (_ , r-iszero t⇒u)
    classify (if t₁ then t₂ else t₃) with classify t₁
    ... | stu σₜ₁                    = stu (σ-ifStuck σₜ₁)
    ... | val true                   = red (_ , r-ifTrue)
    ... | val false                  = red (_ , r-ifFalse)
    ... | val (num zero)             = stu σ-ifZero
    ... | val (num (suc nvₜ₁))       = stu (σ-ifSuc nvₜ₁)
    ... | red (_ , t₁⇒u₁)           = red (_ , r-if t₁⇒u₁)


-- Echo of Theorem 3.5.8.

    data Stuck/Value : Pred₀ Term where
      stu : ∀ {t} → (σₜ : Stuck t) → Stuck/Value t
      val : ∀ {t} → (vₜ : Value t) → Stuck/Value t

    nf→σ/v : ∀ {t} → NormalForm t → Stuck/Value t
    nf→σ/v {t} nfₜ      with classify t
    ... | stu σₜ         = stu σₜ
    ... | val vₜ         = val vₜ
    ... | red (_ , t⇒u) = t⇒u ↯ nfₜ


-- Echo of Definition 3.5.9 and Theorem 3.5.11.

    open MultiStepReduction _⇒_ public
    open UniquenessOfNormalForms _⇒_ ⇒-det public


-- Derived multi-step reduction rules.  Also Lemma A6.

    rs-suc : ∀ {t u} → t ⇒* u → suc t ⇒* suc u
    rs-suc = map r-suc

    rs-predZero : pred zero ⇒* zero
    rs-predZero = r-predZero ◅ ε

    rs-predSuc : ∀ {t} → (nvₜ : NumericValue t) → pred (suc t) ⇒* t
    rs-predSuc nvₜ = r-predSuc nvₜ ◅ ε

    rs-pred : ∀ {t u} → t ⇒* u → pred t ⇒* pred u
    rs-pred = map r-pred

    rs-iszeroZero : iszero zero ⇒* true
    rs-iszeroZero = r-iszeroZero ◅ ε

    rs-iszeroSuc : ∀ {t} → (nvₜ : NumericValue t) → iszero (suc t) ⇒* false
    rs-iszeroSuc nvₜ = r-iszeroSuc nvₜ ◅ ε

    rs-iszero : ∀ {t u} → t ⇒* u → iszero t ⇒* iszero u
    rs-iszero = map r-iszero

    rs-ifTrue : ∀ {t₂ t₃} → if true then t₂ else t₃ ⇒* t₂
    rs-ifTrue = r-ifTrue ◅ ε

    rs-ifFalse : ∀ {t₂ t₃} → if false then t₂ else t₃ ⇒* t₃
    rs-ifFalse = r-ifFalse ◅ ε

    rs-if : ∀ {t₁ t₂ t₃ u₁} → t₁ ⇒* u₁ → if t₁ then t₂ else t₃ ⇒* if u₁ then t₂ else t₃
    rs-if = map r-if


-- Echo of Theorem 3.5.12.

    halt : ∀ t → ∃ λ u → Stuck/Value u × t ⇒* u
    halt true                                        = _ , val true , ε
    halt false                                       = _ , val false , ε
    halt zero                                        = _ , val (num zero) , ε
    halt (suc t)                                     with halt t
    ... | _ , stu σᵤ               , t⇒*u           = _ , stu (σ-sucStuck σᵤ) , rs-suc t⇒*u
    ... | _ , val true             , t⇒*t           = _ , stu σ-sucTrue , rs-suc t⇒*t
    ... | _ , val false            , t⇒*f           = _ , stu σ-sucFalse , rs-suc t⇒*f
    ... | _ , val (num nvᵤ)        , t⇒*u           = _ , val (num (suc nvᵤ)) , rs-suc t⇒*u
    halt (pred t)                                    with halt t
    ... | _ , stu σᵤ               , t⇒*u           = _ , stu (σ-predStuck σᵤ) , rs-pred t⇒*u
    ... | _ , val true             , t⇒*t           = _ , stu σ-predTrue , rs-pred t⇒*t
    ... | _ , val false            , t⇒*f           = _ , stu σ-predFalse , rs-pred t⇒*f
    ... | _ , val (num zero)       , t⇒*z           = _ , val (num zero) , rs-pred t⇒*z ◅◅ rs-predZero
    ... | _ , val (num (suc nvᵤ))  , t⇒*su          = _ , val (num nvᵤ) , rs-pred t⇒*su ◅◅ rs-predSuc nvᵤ
    halt (iszero t)                                  with halt t
    ... | _ , stu σᵤ               , t⇒*u           = _ , stu (σ-iszeroStuck σᵤ) , rs-iszero t⇒*u
    ... | _ , val true             , t⇒*t           = _ , stu σ-iszeroTrue , rs-iszero t⇒*t
    ... | _ , val false            , t⇒*f           = _ , stu σ-iszeroFalse , rs-iszero t⇒*f
    ... | _ , val (num zero)       , t⇒*z           = _ , val true , rs-iszero t⇒*z ◅◅ rs-iszeroZero
    ... | _ , val (num (suc nvᵤ))  , t⇒*su          = _ , val false , rs-iszero t⇒*su ◅◅ rs-iszeroSuc nvᵤ
    halt (if t₁ then t₂ else t₃)                     with halt t₁ | halt t₂ | halt t₃
    ... | _ , stu σᵤ₁              , t₁⇒*u₁ | _ | _ = _ , stu (σ-ifStuck σᵤ₁) , rs-if t₁⇒*u₁
    ... | _ , val true             , t₁⇒*t  | _ , σ/vᵤ₂ , t₂⇒*u₂ | _
                                                     = _ , σ/vᵤ₂ , rs-if t₁⇒*t ◅◅ rs-ifTrue ◅◅ t₂⇒*u₂
    ... | _ , val false            , t₁⇒*f  | _ | _ , σ/vᵤ₃ , t₃⇒*u₃
                                                     = _ , σ/vᵤ₃ , rs-if t₁⇒*f ◅◅ rs-ifFalse ◅◅ t₃⇒*u₃
    ... | _ , val (num zero)       , t₁⇒*z  | _ | _ = _ , stu σ-ifZero , rs-if t₁⇒*z
    ... | _ , val (num (suc nvᵤ₁)) , t₁⇒*su | _ | _ = _ , stu (σ-ifSuc nvᵤ₁) , rs-if t₁⇒*su

    halt′ : ∀ t → ∃ λ u → NormalForm u × t ⇒* u
    halt′ t                         with halt t
    ... | _ , stu (_ , nfᵤ) , t⇒*u = _ , nfᵤ      , t⇒*u
    ... | _ , val vᵤ        , t⇒*u = _ , v→nf vᵤ , t⇒*u


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.16. Exercise [Recommended, ⋆⋆⋆]
-- ”A different way of formalizing meaningless states of the abstract machine is to introduce a new term called
-- `wrong` and augment the operational semantics with rules that explicitly generate `wrong` in all the
-- situations where the present semantics gets stuck.  To do this in detail, …”
-- “Show that these two treatments of run-time errors agree by (1) finding a precise way of stating the
-- intuition that ‘the two treatments agree,’ and (2) proving it.”
--
-- We’re going to start by showing that evaluation of expressions-that-go-wrong is terminating.  First, we echo
-- Definition 3.2.1, and define the augmented system.

module NumbersAndBooleansGoWrong
  where
    data Term : Set₀ where
      wrong true false zero : Term
      suc pred iszero       : ∀ (t : Term) → Term
      if_then_else          : ∀ (t₁ t₂ t₃ : Term) → Term

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

    infix 3 _⇒_
    data _⇒_ : Rel₀ Term where
      r-sucWrong    : ∀ {t} → (bnₜ : BadNat t) → suc t ⇒ wrong
      r-suc         : ∀ {t u} → t ⇒ u → suc t ⇒ suc u
      r-predWrong   : ∀ {t} → (bnₜ : BadNat t) → pred t ⇒ wrong
      r-predZero    : pred zero ⇒ zero
      r-predSuc     : ∀ {t} → (nvₜ : NumericValue t) → pred (suc t) ⇒ t
      r-pred        : ∀ {t u} → t ⇒ u → pred t ⇒ pred u
      r-iszeroWrong : ∀ {t} → (bnₜ : BadNat t) → iszero t ⇒ wrong
      r-iszeroZero  : iszero zero ⇒ true
      r-iszeroSuc   : ∀ {t} → (nvₜ : NumericValue t) → iszero (suc t) ⇒ false
      r-iszero      : ∀ {t u} → t ⇒ u → iszero t ⇒ iszero u
      r-ifWrong     : ∀ {t₁ t₂ t₃} → (bbₜ₁ : BadBool t₁) → if t₁ then t₂ else t₃ ⇒ wrong
      r-ifTrue      : ∀ {t₂ t₃} → if true then t₂ else t₃ ⇒ t₂
      r-ifFalse     : ∀ {t₂ t₃} → if false then t₂ else t₃ ⇒ t₃
      r-if          : ∀ {t₁ t₂ t₃ u₁} → t₁ ⇒ u₁ → if t₁ then t₂ else t₃ ⇒ if u₁ then t₂ else t₃


-- Echo of Definition 3.5.6.

    open NormalForms _⇒_ public


-- Echo of Theorem 3.5.7.

    bn→¬nv : ∀ {t} → BadNat t → ¬ NumericValue t
    bn→¬nv wrong = λ ()
    bn→¬nv true  = λ ()
    bn→¬nv false = λ ()

    nv→nf : ∀ {t} → NumericValue t → NormalForm t
    nv→nf zero      = λ ()
    nv→nf (suc nvₜ) = λ where
      (r-sucWrong bnₜ) → nvₜ ↯ bn→¬nv bnₜ
      (r-suc t⇒u)     → t⇒u ↯ nv→nf nvₜ

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

    ⇒-det : ∀ {t u u′} → t ⇒ u → t ⇒ u′ → u ≡ u′
    ⇒-det (r-sucWrong _)       (r-sucWrong _)       = refl
    ⇒-det (r-sucWrong bnₜ)     (r-suc t⇒u′)        = t⇒u′ ↯ bn→nf bnₜ
    ⇒-det (r-suc t⇒u)         (r-sucWrong bnₜ)     = t⇒u ↯ bn→nf bnₜ
    ⇒-det (r-suc t⇒u)         (r-suc t⇒u′)        = suc & ⇒-det t⇒u t⇒u′
    ⇒-det (r-predWrong _)      (r-predWrong _)      = refl
    ⇒-det (r-predWrong ())     r-predZero
    ⇒-det (r-predWrong ())     (r-predSuc _)
    ⇒-det (r-predWrong bnₜ)    (r-pred t⇒u′)       = t⇒u′ ↯ bn→nf bnₜ
    ⇒-det r-predZero           (r-predWrong ())
    ⇒-det r-predZero           r-predZero           = refl
    ⇒-det r-predZero           (r-pred z⇒u′)       = z⇒u′ ↯ nv→nf zero
    ⇒-det (r-predSuc _)        (r-predWrong ())
    ⇒-det (r-predSuc _)        (r-predSuc _)        = refl
    ⇒-det (r-predSuc nvₜ)      (r-pred st⇒u′)      = st⇒u′ ↯ nv→nf (suc nvₜ)
    ⇒-det (r-pred t⇒u)        (r-predWrong bnₜ)    = t⇒u ↯ bn→nf bnₜ
    ⇒-det (r-pred z⇒u)        r-predZero           = z⇒u ↯ nv→nf zero
    ⇒-det (r-pred st⇒u)       (r-predSuc nvₜ)      = st⇒u ↯ nv→nf (suc nvₜ)
    ⇒-det (r-pred t⇒u)        (r-pred t⇒u′)       = pred & ⇒-det t⇒u t⇒u′
    ⇒-det (r-iszeroWrong _)    (r-iszeroWrong bn₂)  = refl
    ⇒-det (r-iszeroWrong ())   r-iszeroZero
    ⇒-det (r-iszeroWrong ())   (r-iszeroSuc _)
    ⇒-det (r-iszeroWrong bnₜ)  (r-iszero t⇒u′)     = t⇒u′ ↯ bn→nf bnₜ
    ⇒-det r-iszeroZero         (r-iszeroWrong ())
    ⇒-det r-iszeroZero         r-iszeroZero         = refl
    ⇒-det r-iszeroZero         (r-iszero z⇒u′)     = z⇒u′ ↯ nv→nf zero
    ⇒-det (r-iszeroSuc _)      (r-iszeroWrong ())
    ⇒-det (r-iszeroSuc _)      (r-iszeroSuc _)      = refl
    ⇒-det (r-iszeroSuc nvₜ)    (r-iszero st⇒u′)    = st⇒u′ ↯ nv→nf (suc nvₜ)
    ⇒-det (r-iszero t⇒u)      (r-iszeroWrong bnₜ)  = t⇒u ↯ bn→nf bnₜ
    ⇒-det (r-iszero z⇒u)      r-iszeroZero         = z⇒u ↯ nv→nf zero
    ⇒-det (r-iszero st⇒u)     (r-iszeroSuc nvₜ)    = st⇒u ↯ nv→nf (suc nvₜ)
    ⇒-det (r-iszero t⇒u)      (r-iszero t⇒u′)     = iszero & ⇒-det t⇒u t⇒u′
    ⇒-det (r-ifWrong _)        (r-ifWrong _)        = refl
    ⇒-det (r-ifWrong (num ())) r-ifTrue
    ⇒-det (r-ifWrong (num ())) r-ifFalse
    ⇒-det (r-ifWrong bbₜ)      (r-if t₁⇒u₁′)       = t₁⇒u₁′ ↯ bb→nf bbₜ
    ⇒-det r-ifTrue             (r-ifWrong (num ()))
    ⇒-det r-ifTrue             r-ifTrue             = refl
    ⇒-det r-ifTrue             (r-if t⇒u₁′)        = t⇒u₁′ ↯ v→nf true
    ⇒-det r-ifFalse            (r-ifWrong (num ()))
    ⇒-det r-ifFalse            r-ifFalse            = refl
    ⇒-det r-ifFalse            (r-if f⇒u₁′)        = f⇒u₁′ ↯ v→nf false
    ⇒-det (r-if t₁⇒u₁)        (r-ifWrong bbₜ₁)     = t₁⇒u₁ ↯ bb→nf bbₜ₁
    ⇒-det (r-if t⇒u₁)         r-ifTrue             = t⇒u₁ ↯ v→nf true
    ⇒-det (r-if f⇒u₁)         r-ifFalse            = f⇒u₁ ↯ v→nf false
    ⇒-det (r-if t₁⇒u₁)        (r-if t₁⇒u₁′)       = (λ u₁″ → if u₁″ then _ else _) & ⇒-det t₁⇒u₁ t₁⇒u₁′


-- Every term is either a value, or reducible to another term.

    data Value/Reducible : Pred₀ Term where
      val : ∀ {t} → (v : Value t) → Value/Reducible t
      red : ∀ {t} → (r : Reducible t) → Value/Reducible t

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
    ... | red (_ , t⇒u)             = red (_ , r-suc t⇒u)
    classify (pred t)                with classify t
    ... | val wrong                  = red (_ , r-predWrong wrong)
    ... | val true                   = red (_ , r-predWrong true)
    ... | val false                  = red (_ , r-predWrong false)
    ... | val (num zero)             = red (_ , r-predZero)
    ... | val (num (suc nvₜ))        = red (_ , r-predSuc nvₜ)
    ... | red (_ , t⇒u)             = red (_ , r-pred t⇒u)
    classify (iszero t)              with classify t
    ... | val wrong                  = red (_ , r-iszeroWrong wrong)
    ... | val true                   = red (_ , r-iszeroWrong true)
    ... | val false                  = red (_ , r-iszeroWrong false)
    ... | val (num zero)             = red (_ , r-iszeroZero)
    ... | val (num (suc nvₜ))        = red (_ , r-iszeroSuc nvₜ)
    ... | red (_ , t⇒u)             = red (_ , r-iszero t⇒u)
    classify (if t₁ then t₂ else t₃) with classify t₁
    ... | val wrong                  = red (_ , r-ifWrong wrong)
    ... | val true                   = red (_ , r-ifTrue)
    ... | val false                  = red (_ , r-ifFalse)
    ... | val (num nvₜ₁)             = red (_ , r-ifWrong (num nvₜ₁))
    ... | red (_ , t₁⇒u₁)           = red (_ , r-if t₁⇒u₁)


-- Echo of Theorem 3.5.8.

    nf→v : ∀ {t} → NormalForm t → Value t
    nf→v {t} nfₜ        with classify t
    ... | val vₜ         = vₜ
    ... | red (_ , t⇒u) = t⇒u ↯ nfₜ


-- Echo of Definition 3.5.9 and Theorem 3.5.11.

    open MultiStepReduction _⇒_ public
    open UniquenessOfNormalForms _⇒_ ⇒-det public


-- Derived multi-step reduction rules.

    rs-sucWrong : ∀ {t} → (bnₜ : BadNat t) → suc t ⇒* wrong
    rs-sucWrong bnₜ = r-sucWrong bnₜ ◅ ε

    rs-suc : ∀ {t u} → t ⇒* u → suc t ⇒* suc u
    rs-suc = map r-suc

    rs-predWrong : ∀ {t} → (bnₜ : BadNat t) → pred t ⇒* wrong
    rs-predWrong bnₜ = r-predWrong bnₜ ◅ ε

    rs-predZero : pred zero ⇒* zero
    rs-predZero = r-predZero ◅ ε

    rs-predSuc : ∀ {t} → (nvₜ : NumericValue t) → pred (suc t) ⇒* t
    rs-predSuc nvₜ = r-predSuc nvₜ ◅ ε

    rs-pred : ∀ {t u} → t ⇒* u → pred t ⇒* pred u
    rs-pred = map r-pred

    rs-iszeroWrong : ∀ {t} → (bnₜ : BadNat t) → iszero t ⇒* wrong
    rs-iszeroWrong bnₜ = r-iszeroWrong bnₜ ◅ ε

    rs-iszeroZero : iszero zero ⇒* true
    rs-iszeroZero = r-iszeroZero ◅ ε

    rs-iszeroSuc : ∀ {t} → (nvₜ : NumericValue t) → iszero (suc t) ⇒* false
    rs-iszeroSuc nvₜ = r-iszeroSuc nvₜ ◅ ε

    rs-iszero : ∀ {t u} → t ⇒* u → iszero t ⇒* iszero u
    rs-iszero = map r-iszero

    rs-ifWrong : ∀ {t₁ t₂ t₃} → (bbₜ₁ : BadBool t₁) → if t₁ then t₂ else t₃ ⇒* wrong
    rs-ifWrong bbₜ₁ = r-ifWrong bbₜ₁ ◅ ε

    rs-ifTrue : ∀ {t₂ t₃} → if true then t₂ else t₃ ⇒* t₂
    rs-ifTrue = r-ifTrue ◅ ε

    rs-ifFalse : ∀ {t₂ t₃} → if false then t₂ else t₃ ⇒* t₃
    rs-ifFalse = r-ifFalse ◅ ε

    rs-if : ∀ {t₁ t₂ t₃ u₁} → t₁ ⇒* u₁ → if t₁ then t₂ else t₃ ⇒* if u₁ then t₂ else t₃
    rs-if = map r-if


-- Echo of Theorem 3.5.12.

    halt : ∀ t → ∃ λ u → Value u × t ⇒* u
    halt wrong                               = _ , wrong , ε
    halt true                                = _ , true , ε
    halt false                               = _ , false , ε
    halt zero                                = _ , num zero , ε
    halt (suc t)                             with halt t
    ... | _ , wrong         , t⇒*w          = _ , wrong , rs-suc t⇒*w ◅◅ rs-sucWrong wrong
    ... | _ , true          , t⇒*t          = _ , wrong , rs-suc t⇒*t ◅◅ rs-sucWrong true
    ... | _ , false         , t⇒*f          = _ , wrong , rs-suc t⇒*f ◅◅ rs-sucWrong false
    ... | _ , num nvᵤ       , t⇒*u          = _ , num (suc nvᵤ) , rs-suc t⇒*u
    halt (pred t)                            with halt t
    ... | _ , wrong         , t⇒*w          = _ , wrong , rs-pred t⇒*w ◅◅ rs-predWrong wrong
    ... | _ , true          , t⇒*t          = _ , wrong , rs-pred t⇒*t ◅◅ rs-predWrong true
    ... | _ , false         , t⇒*f          = _ , wrong , rs-pred t⇒*f ◅◅ rs-predWrong false
    ... | _ , num zero      , t⇒*z          = _ , num zero , rs-pred t⇒*z ◅◅ rs-predZero
    ... | _ , num (suc nvᵤ) , t⇒*su         = _ , num nvᵤ , rs-pred t⇒*su ◅◅ rs-predSuc nvᵤ
    halt (iszero t)                          with halt t
    ... | _ , wrong         , t⇒*w          = _ , wrong , rs-iszero t⇒*w ◅◅ rs-iszeroWrong wrong
    ... | _ , true          , t⇒*t          = _ , wrong , rs-iszero t⇒*t ◅◅ rs-iszeroWrong true
    ... | _ , false         , t⇒*f          = _ , wrong , rs-iszero t⇒*f ◅◅ rs-iszeroWrong false
    ... | _ , num zero      , t⇒*z          = _ , true , rs-iszero t⇒*z ◅◅ rs-iszeroZero
    ... | _ , num (suc nvᵤ) , t⇒*su         = _ , false , rs-iszero t⇒*su ◅◅ rs-iszeroSuc nvᵤ
    halt (if t₁ then t₂ else t₃)             with halt t₁ | halt t₂ | halt t₃
    ... | _ , wrong         , t₁⇒*w | _ | _ = _ , wrong , rs-if t₁⇒*w ◅◅ rs-ifWrong wrong
    ... | _ , true          , t₁⇒*t | _ , vᵤ₂ , t₂⇒*u₂ | _
                                             = _ , vᵤ₂ , rs-if t₁⇒*t ◅◅ rs-ifTrue ◅◅ t₂⇒*u₂
    ... | _ , false         , t₁⇒*f | _ | _ , vᵤ₃ , t₃⇒*u₃
                                             = _ , vᵤ₃ , rs-if t₁⇒*f ◅◅ rs-ifFalse ◅◅ t₃⇒*u₃
    ... | _ , num nvᵤ₁      , t₁⇒*u | _ | _ = _ , wrong , rs-if t₁⇒*u ◅◅ rs-ifWrong (num nvᵤ₁)

    halt′ : ∀ t → ∃ λ u → NormalForm u × t ⇒* u
    halt′ t              with halt t
    ... | _ , vᵤ , t⇒*u = _ , v→nf vᵤ , t⇒*u


---------------------------------------------------------------------------------------------------------------
--
-- We’re going to show that expressions-that-go-wrong go wrong exactly when expressions-that-get-stuck get
-- stuck.  In order to do so, we’re going to need a type of terms that are _wrongless_, i.e., that do not
-- contain `wrong` as a subterm.  For this purpose, we define a predicate on terms, `Wrongless`.

    data Wrongless : Pred₀ Term where
      true         : Wrongless true
      false        : Wrongless false
      zero         : Wrongless zero
      suc          : ∀ {t} → (ρₜ : Wrongless t) → Wrongless (suc t)
      pred         : ∀ {t} → (ρₜ : Wrongless t) → Wrongless (pred t)
      iszero       : ∀ {t} → (ρₜ : Wrongless t) → Wrongless (iszero t)
      if_then_else : ∀ {t₁ t₂ t₃} → (ρₜ₁ : Wrongless t₁) (ρₜ₂ : Wrongless t₂) (ρₜ₃ : Wrongless t₃) →
                     Wrongless (if t₁ then t₂ else t₃)


-- We say that a one-step reduction from `t` to `u` is wrongless when `u` is wrongless.  A multi-step
-- reduction is wrongless when it is composed of wrongless reductions.

    data WronglessReds : ∀ {t u} → Pred₀ (t ⇒* u) where
      ε   : ∀ {t} → WronglessReds {t} {t} ε
      _◅_ : ∀ {t i u} {r : t ⇒ i} {rs : i ⇒* u} →
            (ρᵢ : Wrongless i) (ρrs : WronglessReds rs) → WronglessReds (r ◅ rs)


-- The evidence that a term is wrongless is unique.

    ρ-uniq : ∀ {t} → (ρₜ ρₜ′ : Wrongless t) → ρₜ ≡ ρₜ′
    ρ-uniq true                       true         = refl
    ρ-uniq false                      false        = refl
    ρ-uniq zero                       zero         = refl
    ρ-uniq (suc ρₜ)                   (suc ρₜ′)    with ρ-uniq ρₜ ρₜ′
    ... | refl                                     = refl
    ρ-uniq (pred ρₜ)                  (pred ρₜ′)   with ρ-uniq ρₜ ρₜ′
    ... | refl                                     = refl
    ρ-uniq (iszero ρₜ)                (iszero ρₜ′) with ρ-uniq ρₜ ρₜ′
    ... | refl                                     = refl
    ρ-uniq (if ρₜ₁ then ρₜ₂ else ρₜ₃)
                     (if ρₜ₁′ then ρₜ₂′ else ρₜ₃′) with ρ-uniq ρₜ₁ ρₜ₁′ | ρ-uniq ρₜ₂ ρₜ₂′ | ρ-uniq ρₜ₃ ρₜ₃′
    ... | refl | refl | refl                       = refl


-- We can decide whether a term is wrongless or not.

    ρ? : ∀ t → Dec (Wrongless t)
    ρ? wrong                          = no λ ()
    ρ? true                           = yes true
    ρ? false                          = yes false
    ρ? zero                           = yes zero
    ρ? (suc t)                        with ρ? t
    ... | no ¬ρₜ                      = no λ where (suc ρₜ) → ρₜ ↯ ¬ρₜ
    ... | yes ρₜ                      = yes (suc ρₜ)
    ρ? (pred t)                       with ρ? t
    ... | no ¬ρₜ                      = no λ where (pred ρₜ) → ρₜ ↯ ¬ρₜ
    ... | yes ρₜ                      = yes (pred ρₜ)
    ρ? (iszero t)                     with ρ? t
    ... | no ¬ρₜ                      = no λ where (iszero ρₜ) → ρₜ ↯ ¬ρₜ
    ... | yes ρₜ                      = yes (iszero ρₜ)
    ρ? (if t₁ then t₂ else t₃)        with ρ? t₁ | ρ? t₂ | ρ? t₃
    ... | no ¬ρₜ₁ | _       | _       = no λ where (if ρₜ₁ then ρₜ₂ else ρₜ₃) → ρₜ₁ ↯ ¬ρₜ₁
    ... | yes ρₜ₁ | no ¬ρₜ₂ | _       = no λ where (if ρₜ₁ then ρₜ₂ else ρₜ₃) → ρₜ₂ ↯ ¬ρₜ₂
    ... | yes ρₜ₁ | yes ρₜ₂ | no ¬ρₜ₃ = no λ where (if ρₜ₁ then ρₜ₂ else ρₜ₃) → ρₜ₃ ↯ ¬ρₜ₃
    ... | yes ρₜ₁ | yes ρₜ₂ | yes ρₜ₃ = yes (if ρₜ₁ then ρₜ₂ else ρₜ₃)


---------------------------------------------------------------------------------------------------------------
--
-- Original terms and reductions can be translated to the augmented system.

private
  module Exercise3516 where
    open module O = NumbersAndBooleansGetStuck
      renaming (_⇒_ to O[_⇒_] ; _⇒*_ to O[_⇒*_])

    open module W = NumbersAndBooleansGoWrong
      renaming (_⇒_ to W[_⇒_] ; _⇒*_ to W[_⇒*_])

    o→w : O.Term → W.Term
    o→w true                    = true
    o→w false                   = false
    o→w zero                    = zero
    o→w (suc t)                 = suc (o→w t)
    o→w (pred t)                = pred (o→w t)
    o→w (iszero t)              = iszero (o→w t)
    o→w (if t₁ then t₂ else t₃) = if (o→w t₁) then (o→w t₂) else (o→w t₃)

    onv→wnv : ∀ {t} → O.NumericValue t → W.NumericValue (o→w t)
    onv→wnv zero      = zero
    onv→wnv (suc nvₜ) = suc (onv→wnv nvₜ)

    ov→wv : ∀ {t} → O.Value t → W.Value (o→w t)
    ov→wv true      = true
    ov→wv false     = false
    ov→wv (num nvₜ) = num (onv→wnv nvₜ)

    or→wr : ∀ {t u} → O[ t ⇒ u ] → W[ o→w t ⇒ o→w u ]
    or→wr (r-suc t⇒u)      = r-suc (or→wr t⇒u)
    or→wr r-predZero        = r-predZero
    or→wr (r-predSuc nvₜ)   = r-predSuc (onv→wnv nvₜ)
    or→wr (r-pred t⇒u)     = r-pred (or→wr t⇒u)
    or→wr r-iszeroZero      = r-iszeroZero
    or→wr (r-iszeroSuc nvₜ) = r-iszeroSuc (onv→wnv nvₜ)
    or→wr (r-iszero t⇒u)   = r-iszero (or→wr t⇒u)
    or→wr r-ifTrue          = r-ifTrue
    or→wr r-ifFalse         = r-ifFalse
    or→wr (r-if t₁⇒u₁)     = r-if (or→wr t₁⇒u₁)


-- Augmented wrongless terms and reductions can be translated to the original system.

    w→o : ∀ {t} → Wrongless t → O.Term
    w→o true                       = true
    w→o false                      = false
    w→o zero                       = zero
    w→o (suc ρₜ)                   = suc (w→o ρₜ)
    w→o (pred ρₜ)                  = pred (w→o ρₜ)
    w→o (iszero ρₜ)                = iszero (w→o ρₜ)
    w→o (if ρₜ₁ then ρₜ₂ else ρₜ₃) = if (w→o ρₜ₁) then (w→o ρₜ₂) else (w→o ρₜ₃)

    wnv→onv : ∀ {t} → (ρₜ : Wrongless t) → W.NumericValue t → O.NumericValue (w→o ρₜ)
    wnv→onv zero     zero      = zero
    wnv→onv (suc ρₜ) (suc nvₜ) = suc (wnv→onv ρₜ nvₜ)

    wr→or : ∀ {t u} → (ρₜ : Wrongless t) (ρᵤ : Wrongless u) → W[ t ⇒ u ] → O[ w→o ρₜ ⇒ w→o ρᵤ ]
    wr→or _                            ()          (r-sucWrong _)
    wr→or (suc ρₜ)                     (suc ρᵤ)    (r-suc t⇒u)      = r-suc (wr→or ρₜ ρᵤ t⇒u)
    wr→or _                            ()          (r-predWrong _)
    wr→or (pred zero)                  zero        r-predZero        = r-predZero
    wr→or (pred (suc ρₜ))              ρₜ′         (r-predSuc nvₜ)   with ρ-uniq ρₜ ρₜ′
    ... | refl                                                        = r-predSuc (wnv→onv ρₜ nvₜ)
    wr→or (pred ρₜ)                    (pred ρᵤ)   (r-pred t⇒u)     = r-pred (wr→or ρₜ ρᵤ t⇒u)
    wr→or _                            ()          (r-iszeroWrong _)
    wr→or (iszero zero)                true        r-iszeroZero      = r-iszeroZero
    wr→or (iszero (suc ρₜ))            false       (r-iszeroSuc nvₜ) = r-iszeroSuc (wnv→onv ρₜ nvₜ)
    wr→or (iszero ρₜ)                  (iszero ρᵤ) (r-iszero t⇒u)   = r-iszero (wr→or ρₜ ρᵤ t⇒u)
    wr→or _                            ()          (r-ifWrong _)
    wr→or (if true then ρₜ₂ else ρₜ₃)  ρᵤ          r-ifTrue          with ρ-uniq ρₜ₂ ρᵤ
    ... | refl                                                        = r-ifTrue
    wr→or (if false then ρₜ₂ else ρₜ₃) ρᵤ          r-ifFalse         with ρ-uniq ρₜ₃ ρᵤ
    ... | refl                                                        = r-ifFalse
    wr→or (if ρₜ₁ then ρₜ₂ else ρₜ₃)
                       (if ρᵤ₁ then ρₜ₂′ else ρₜ₃′) (r-if t₁⇒u₁)     with ρ-uniq ρₜ₂ ρₜ₂′ | ρ-uniq ρₜ₃ ρₜ₃′
    ... | refl | refl                                                 = r-if (wr→or ρₜ₁ ρᵤ₁ t₁⇒u₁)

    wrs→ors : ∀ {t u} → (ρₜ : Wrongless t) (ρᵤ : Wrongless u) →
               {t⇒*u : W[ t ⇒* u ]} → WronglessReds t⇒*u → O[ w→o ρₜ ⇒* w→o ρᵤ ]
    wrs→ors ρₜ ρᵤ {ε}            ε          with ρ-uniq ρₜ ρᵤ
    ... | refl                               = ε
    wrs→ors ρₜ ρᵤ {t⇒i ◅ i⇒*u} (ρₓ ◅ ρrs) = wr→or ρₜ ρₓ t⇒i ◅ wrs→ors ρₓ ρᵤ ρrs


-- Translating an original term to the augmented system produces a wrongless term.

    ρ! : ∀ t → Wrongless (o→w t)
    ρ! true                    = true
    ρ! false                   = false
    ρ! zero                    = zero
    ρ! (suc t)                 = suc (ρ! t)
    ρ! (pred t)                = pred (ρ! t)
    ρ! (iszero t)              = iszero (ρ! t)
    ρ! (if t₁ then t₂ else t₃) = if (ρ! t₁) then (ρ! t₂) else (ρ! t₃)


-- Translating a term to and from produces an identical term.

    wow-id : ∀ {t} → (ρₜ : Wrongless t) → o→w (w→o ρₜ) ≡ t
    wow-id true                       = refl
    wow-id false                      = refl
    wow-id zero                       = refl
    wow-id (suc ρₜ)                   = suc & wow-id ρₜ
    wow-id (pred ρₜ)                  = pred & wow-id ρₜ
    wow-id (iszero ρₜ)                = iszero & wow-id ρₜ
    wow-id (if ρₜ₁ then ρₜ₂ else ρₜ₃) = if_then_else & wow-id ρₜ₁ ⊗ wow-id ρₜ₂ ⊗ wow-id ρₜ₃

    owo-id : ∀ {t} → (ρₜ : Wrongless (o→w t)) → w→o ρₜ ≡ t
    owo-id {true}               true        = refl
    owo-id {false}              false       = refl
    owo-id {zero}               zero        = refl
    owo-id {suc _}              (suc ρₜ)    = suc & owo-id ρₜ
    owo-id {pred _}             (pred ρₜ)   = pred & owo-id ρₜ
    owo-id {iszero _}           (iszero ρₜ) = iszero & owo-id ρₜ
    owo-id {if _ then _ else _}
                 (if ρₜ₁ then ρₜ₂ else ρₜ₃) = if_then_else & owo-id ρₜ₁ ⊗ owo-id ρₜ₂ ⊗ owo-id ρₜ₃


---------------------------------------------------------------------------------------------------------------
--
-- Lemma A.4.
-- “If `t` is stuck then `W[ t ⇒* wrong ]`.”

    lem-a4 : ∀ {t} → O.Stuck t → W[ o→w t ⇒* wrong ]
    lem-a4 {true}                  (¬vₜ , _)    = true ↯ ¬vₜ
    lem-a4 {false}                 (¬vₜ , _)    = false ↯ ¬vₜ
    lem-a4 {zero}                  (¬vₜ , _)    = num zero ↯ ¬vₜ
    lem-a4 {suc t}                 (¬vₜ , nfₜ)  with O.classify t
    ... | stu σₜ                                = W.rs-suc (lem-a4 σₜ) ◅◅ W.rs-sucWrong wrong
    ... | val true                              = W.rs-sucWrong true
    ... | val false                             = W.rs-sucWrong false
    ... | val (num nvₜ)                         = num (suc nvₜ) ↯ ¬vₜ
    ... | red (_ , t⇒u)                        = r-suc t⇒u ↯ nfₜ
    lem-a4 {pred t}                (_   , nfₜ)  with O.classify t
    ... | stu σₜ                                = W.rs-pred (lem-a4 σₜ) ◅◅ W.rs-predWrong wrong
    ... | val true                              = W.rs-predWrong true
    ... | val false                             = W.rs-predWrong false
    ... | val (num zero)                        = r-predZero ↯ nfₜ
    ... | val (num (suc nvₜ))                   = r-predSuc nvₜ ↯ nfₜ
    ... | red (_ , t⇒u)                        = r-pred t⇒u ↯ nfₜ
    lem-a4 {iszero t}              (_   , nfₜ)  with O.classify t
    ... | stu σₜ                                = W.rs-iszero (lem-a4 σₜ) ◅◅ W.rs-iszeroWrong wrong
    ... | val true                              = W.rs-iszeroWrong true
    ... | val false                             = W.rs-iszeroWrong false
    ... | val (num zero)                        = r-iszeroZero ↯ nfₜ
    ... | val (num (suc nvₜ))                   = r-iszeroSuc nvₜ ↯ nfₜ
    ... | red (_ , t⇒u)                        = r-iszero t⇒u ↯ nfₜ
    lem-a4 {if t₁ then t₂ else t₃} (_   , nfₜ₁) with O.classify t₁
    ... | stu σₜ₁                               = W.rs-if (lem-a4 σₜ₁) ◅◅ W.rs-ifWrong wrong
    ... | val true                              = r-ifTrue ↯ nfₜ₁
    ... | val false                             = r-ifFalse ↯ nfₜ₁
    ... | val (num nvₜ₁)                        = W.rs-ifWrong (num (onv→wnv nvₜ₁))
    ... | red (_ , t₁⇒u₁)                      = r-if t₁⇒u₁ ↯ nfₜ₁


---------------------------------------------------------------------------------------------------------------
--
-- Lemma A.5.
-- “If `W[ t ⇒ u ]` in the augmented semantics and `u` contains `wrong` as a subterm, then `t` is stuck in the
-- original semantics.”

    lem-a5 : ∀ {t u} → ¬ Wrongless u → W[ o→w t ⇒ u ] → O.Stuck t
    lem-a5 {t} ¬ρᵤ t⇒u   with O.classify t
    ... | stu σₜ          = σₜ
    ... | val vₜ          = t⇒u ↯ W.v→nf (ov→wv vₜ)
    ... | red (u , t⇒u′) with W.⇒-det t⇒u (or→wr t⇒u′)
    ... | refl            = ρ! u ↯ ¬ρᵤ


---------------------------------------------------------------------------------------------------------------
--
-- Proposition A.2.
-- “For all original terms `t`, (`O[ t ⇒* u ]` where `u` is stuck) iff (`W[ t ⇒* wrong ]`).”
--
-- The left-to-right implication follows from Lemma A.4.

    prop-a2-ltr : ∀ {t} → (∃ λ u → O.Stuck u × O[ t ⇒* u ]) → W[ o→w t ⇒* wrong ]
    prop-a2-ltr (u , σ , ε)      = lem-a4 σ
    prop-a2-ltr (u , σ , r ◅ rs) = or→wr r ◅ prop-a2-ltr (u , σ , rs)


-- To show the right-to-left implication, we’re going to find the first wrongless term `u` in our multi-step
-- reduction that reduces to a non-wrongless term.

    prop-a2-find : ∀ {t} → Wrongless t → W[ t ⇒* wrong ] →
                   ∃ λ u → Wrongless u × Σ W[ t ⇒* u ] WronglessReds × ∃ λ v → ¬ Wrongless v × W[ u ⇒ v ]
    prop-a2-find {t} () ε
    prop-a2-find {t} ρₜ (t⇒i ◅⟨ i ⟩ i⇒*w)       with ρ? i
    ... | no ¬ρₓ                                  = t , ρₜ , (ε , ε) , i , ¬ρₓ , t⇒i
    ... | yes ρₓ                                  with prop-a2-find ρₓ i⇒*w
    ... | u , ρᵤ , (i⇒*u , ρrs) , v , ¬ρᵥ , u⇒v = u , ρᵤ , (t⇒i ◅ i⇒*u , ρₓ ◅ ρrs) , v , ¬ρᵥ , u⇒v


-- Then, all that remains to be done is massaging the evidence into the desired form.

    r-wow-id : ∀ {t u} → (ρₜ : Wrongless t) → W[ t ⇒ u ] ≡ W[ o→w (w→o ρₜ) ⇒ u ]
    r-wow-id ρₜ rewrite wow-id ρₜ = refl

    rs-wow-id : ∀ {t u} → (ρᵤ : Wrongless u) → W[ t ⇒* u ] ≡ W[ t ⇒* o→w (w→o ρᵤ) ]
    rs-wow-id ρᵤ rewrite wow-id ρᵤ = refl

    ρs-wow-id : ∀ {t u} {t⇒*u : W[ o→w t ⇒* u ]} → (ρᵤ : Wrongless u) →
                WronglessReds t⇒*u ≡ WronglessReds (coerce t⇒*u (rs-wow-id ρᵤ))
    ρs-wow-id ρᵤ rewrite wow-id ρᵤ = refl

    rs-owo-id : ∀ {t u} → (ρₜ : Wrongless (o→w t)) (ρᵤ : Wrongless (o→w u)) →
                O[ w→o ρₜ ⇒* w→o ρᵤ ] ≡ O[ t ⇒* u ]
    rs-owo-id ρₜ ρᵤ rewrite owo-id ρₜ | owo-id ρᵤ = refl

    prop-a2-rtl : ∀ {t} → W[ o→w t ⇒* wrong ] → (∃ λ u → O.Stuck u × O[ t ⇒* u ])
    prop-a2-rtl {t} t⇒*w                                   with prop-a2-find (ρ! t) t⇒*w
    ... | [u] , [ρᵤ] , ([t⇒*u] , [ρrs]) , v , ¬ρᵥ , [u⇒v] =
      let
        u     = w→o [ρᵤ]
        t⇒*u = coerce [t⇒*u] (rs-wow-id [ρᵤ])
        ρrs   = coerce [ρrs] (ρs-wow-id [ρᵤ])
        u⇒v  = coerce [u⇒v] (r-wow-id [ρᵤ])
        σᵤ    = lem-a5 ¬ρᵥ u⇒v
        ρₜ    = ρ! t
        ρᵤ    = ρ! u
      in
        u , σᵤ , coerce (wrs→ors ρₜ ρᵤ ρrs) (rs-owo-id ρₜ ρᵤ)


-- Finally, we conclude Exercise 3.5.16.

    prop-a2 : ∀ {t} → (∃ λ u → O.Stuck u × O[ t ⇒* u ]) ↔ W[ o→w t ⇒* wrong ]
    prop-a2 = prop-a2-ltr , prop-a2-rtl


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.17. Exercise [Recommended, ***]
-- “Two styles of operational semantics are in common use. The one used in this book is called the _small-step_
-- style, because the definition of the reduction relation shows how individual steps of computation are used
-- to rewrite a term, bit by bit, until it eventually becomes a value.  On top of this, we define a multi-step
-- reduction relation that allows us to talk about terms reducing (in many steps) to values.  An alternative
-- style, called _big-step semantics_ (or sometimes _natural semantics_), directly formulates the notion of
-- ‘this term evaluates to that final value,’ written `t ⇓ v`.  The big-step evaluation rules for our language
-- of boolean and arithmetic expressions look like this: …”
-- “Show that the small-step and big-step semantics for this language coincide, i.e. `t ⇒* v` iff `t ⇓ v`.”

private
  module Exercise3517 where
    open NumbersAndBooleansGetStuck

    data _⇓_ : Rel₀ Term where
      e-val        : ∀ {t} → (vₜ : Value t) → t ⇓ t
      e-suc        : ∀ {t u} → (nvᵤ : NumericValue u) → t ⇓ u → suc t ⇓ suc u
      e-predZero   : ∀ {t} → t ⇓ zero → pred t ⇓ zero
      e-predSuc    : ∀ {t u} → (nvᵤ : NumericValue u) → t ⇓ suc u → pred t ⇓ u
      e-iszeroZero : ∀ {t} → t ⇓ zero → iszero t ⇓ true
      e-iszeroSuc  : ∀ {t u} → (nvᵤ : NumericValue u) → t ⇓ suc u → iszero t ⇓ false
      e-ifTrue     : ∀ {t₁ t₂ t₃ u₂} → (vᵤ₂ : Value u₂) → t₁ ⇓ true → t₂ ⇓ u₂ → if t₁ then t₂ else t₃ ⇓ u₂
      e-ifFalse    : ∀ {t₁ t₂ t₃ u₃} → (vᵤ₃ : Value u₃) → t₁ ⇓ false → t₃ ⇓ u₃ → if t₁ then t₂ else t₃ ⇓ u₃


---------------------------------------------------------------------------------------------------------------
--
-- Lemma A.6.
-- “If `t₁ ⇒* u₁` then `if t₁ then t₂ else t₃ ⇒* if u₁ then t₂ else t₃`.  (And similarly for the other term
-- constructors.)”
-- (shown above)


---------------------------------------------------------------------------------------------------------------
--
-- Proposition A.7.
-- “If `t ⇓ v` then `t ⇒* v`.”

    prop-a7 : ∀ {t u} → (vᵤ : Value u) → t ⇓ u → t ⇒* u
    prop-a7 vᵤ (e-val vₜ)                 = ε
    prop-a7 vᵤ (e-suc nvᵤ t⇓u)            = rs-suc (prop-a7 (num nvᵤ) t⇓u)
    prop-a7 vᵤ (e-predZero t⇓z)           = rs-pred (prop-a7 vᵤ t⇓z) ◅◅ rs-predZero
    prop-a7 vᵤ (e-predSuc nvᵤ t⇓su)       = rs-pred (prop-a7 (num (suc nvᵤ)) t⇓su) ◅◅ rs-predSuc nvᵤ
    prop-a7 vᵤ (e-iszeroZero t⇓z)         = rs-iszero (prop-a7 (num zero) t⇓z) ◅◅ rs-iszeroZero
    prop-a7 vᵤ (e-iszeroSuc nvᵤ t⇓su)     = rs-iszero (prop-a7 (num (suc nvᵤ)) t⇓su) ◅◅ rs-iszeroSuc nvᵤ
    prop-a7 vᵤ (e-ifTrue vᵤ₂ t₁⇓t t₂⇓u₂)  = rs-if (prop-a7 true t₁⇓t) ◅◅ rs-ifTrue ◅◅ prop-a7 vᵤ₂ t₂⇓u₂
    prop-a7 vᵤ (e-ifFalse vᵤ₃ t₁⇓f t₃⇓u₃) = rs-if (prop-a7 false t₁⇓f) ◅◅ rs-ifFalse ◅◅ prop-a7 vᵤ₃ t₃⇓u₃


---------------------------------------------------------------------------------------------------------------
--
-- Lemma A.8.
-- “If `if t₁ then t₂ else t₃ ⇒* v`, then either `t₁ ⇒* true` and `t₂ ⇒* v` or `t₁ ⇒* false` and
-- `t₃ ⇒* v`.  Moreover, the evaluation sequences for `t₁` and `t₂` or `t₃` are strictly shorter than the
-- given evaluation sequence.  (And similarly for the other term constructors.)”
--
-- First, we’re going to need to show that certain multi-step reductions are impossible.

    ¬rs-numTrue : ∀ {t} → NumericValue t → ¬ (t ⇒* true)
    ¬rs-numTrue zero      (() ◅ _)
    ¬rs-numTrue (suc nvₜ) (r-suc t⇒u ◅ _) = t⇒u ↯ nv→nf nvₜ

    ¬rs-numFalse : ∀ {t} → NumericValue t → ¬ (t ⇒* false)
    ¬rs-numFalse zero      (() ◅ _)
    ¬rs-numFalse (suc nvₜ) (r-suc t⇒u ◅ _) = t⇒u ↯ nv→nf nvₜ

    ¬rs-sucTrue : ∀ {t} → ¬ (suc t ⇒* true)
    ¬rs-sucTrue = λ where (r-suc _ ◅ si⇒*t) → si⇒*t ↯ ¬rs-sucTrue

    ¬rs-sucFalse : ∀ {t} → ¬ (suc t ⇒* false)
    ¬rs-sucFalse = λ where (r-suc _ ◅ si⇒*f) → si⇒*f ↯ ¬rs-sucFalse

    ¬rs-sucZero : ∀ {t} → ¬ (suc t ⇒* zero)
    ¬rs-sucZero = λ where (r-suc _ ◅ si⇒*z) → si⇒*z ↯ ¬rs-sucZero

    ¬rs-predTrue : ∀ {t} → ¬ (pred t ⇒* true)
    ¬rs-predTrue = λ where (r-predZero ◅ z⇒*t)    → z⇒*t ↯ ¬rs-numTrue zero
                           (r-predSuc nvₓ ◅ i⇒*t) → i⇒*t ↯ ¬rs-numTrue nvₓ
                           (r-pred _ ◅ pi⇒*t)     → pi⇒*t ↯ ¬rs-predTrue

    ¬rs-predFalse : ∀ {t} → ¬ (pred t ⇒* false)
    ¬rs-predFalse = λ where (r-predZero ◅ z⇒*f)    → z⇒*f ↯ ¬rs-numFalse zero
                            (r-predSuc nvₓ ◅ i⇒*f) → i⇒*f ↯ ¬rs-numFalse nvₓ
                            (r-pred _ ◅ pi⇒*f)     → pi⇒*f ↯ ¬rs-predFalse

    lem-a8-suc : ∀ {t u} → suc t ⇒* suc u → t ⇒* u
    lem-a8-suc ε                      = ε
    lem-a8-suc (r-suc t⇒i ◅ si⇒*su) with lem-a8-suc si⇒*su
    ... | i⇒*u                       = t⇒i ◅ i⇒*u

    lem-a8-pred : ∀ {t u} → (nvᵤ : NumericValue u) → pred t ⇒* u →
                  (t ⇒* zero × u ≡ zero) ⊎ (t ⇒* suc u)
    lem-a8-pred ()      ε
    lem-a8-pred zero    (r-predZero ◅ z⇒*z)         = inj₁ (z⇒*z , refl)
    lem-a8-pred (suc _) (r-predZero ◅ () ◅ _)
    lem-a8-pred zero    (r-predSuc zero ◅ _)         = inj₂ ε
    lem-a8-pred zero    (r-predSuc (suc _) ◅ si⇒*z) = si⇒*z ↯ ¬rs-sucZero
    lem-a8-pred (suc _) (r-predSuc _ ◅ i⇒*su)       = inj₂ (rs-suc i⇒*su)
    lem-a8-pred nvᵤ     (r-pred t⇒i ◅ pi⇒*u)       with lem-a8-pred nvᵤ pi⇒*u
    ... | inj₁ (i⇒*z , refl)                        = inj₁ (t⇒i ◅ i⇒*z , refl)
    ... | inj₂ i⇒*su                                = inj₂ (t⇒i ◅ i⇒*su)

    lem-a8-iszero : ∀ {t u} → (vᵤ : Value u) → iszero t ⇒* u →
                    (t ⇒* zero × u ≡ true) ⊎ ((∃ λ i → NumericValue i × t ⇒* suc i) × u ≡ false)
    lem-a8-iszero vᵤ       (r-iszeroZero ◅ ε)         = inj₁ (ε , refl)
    lem-a8-iszero vᵤ       (r-iszeroZero ◅ () ◅ _)
    lem-a8-iszero vᵤ       (r-iszeroSuc nvₜ ◅ ε)      = inj₂ ((_ , nvₜ , ε) , refl)
    lem-a8-iszero vᵤ       (r-iszeroSuc nvₜ ◅ () ◅ _)
    lem-a8-iszero vᵤ       (r-iszero t⇒i ◅ izi⇒*u)  with lem-a8-iszero vᵤ izi⇒*u
    ... | inj₁ (i⇒*z , refl)                         = inj₁ (t⇒i ◅ i⇒*z , refl)
    ... | inj₂ ((y , nvy , i⇒*sy) , refl)            = inj₂ ((y , nvy , t⇒i ◅ i⇒*sy) , refl)
    lem-a8-iszero (num ()) ε

    lem-a8-if : ∀ {t₁ t₂ t₃ u} → (vᵤ : Value u) → if t₁ then t₂ else t₃ ⇒* u →
                (t₁ ⇒* true × t₂ ⇒* u) ⊎ (t₁ ⇒* false × t₃ ⇒* u)
    lem-a8-if vᵤ       (r-ifTrue ◅ ift₁⇒*u)     = inj₁ (ε , ift₁⇒*u)
    lem-a8-if vᵤ       (r-ifFalse ◅ ift₁⇒*u)    = inj₂ (ε , ift₁⇒*u)
    lem-a8-if vᵤ       (r-if t₁⇒i₁ ◅ itei₁⇒*u) with lem-a8-if vᵤ itei₁⇒*u
    ... | inj₁ (i₁⇒*t , t₂⇒*u)                 = inj₁ (t₁⇒i₁ ◅ i₁⇒*t , t₂⇒*u)
    ... | inj₂ (i₁⇒*f , t₃⇒*u)                 = inj₂ (t₁⇒i₁ ◅ i₁⇒*f , t₃⇒*u)
    lem-a8-if (num ()) ε


---------------------------------------------------------------------------------------------------------------
--
-- Proposition A.8.
-- “If `t ⇒* v` then `t ⇓ v`.”

    prop-a8 : ∀ {t u} → (vᵤ : Value u) → t ⇒* u → t ⇓ u
    prop-a8 vₜ              ε                         = e-val vₜ
    prop-a8 true            (r-suc _ ◅ si⇒*t)        = si⇒*t ↯ ¬rs-sucTrue
    prop-a8 false           (r-suc _ ◅ si⇒*f)        = si⇒*f ↯ ¬rs-sucFalse
    prop-a8 (num zero)      (r-suc t⇒i ◅ si⇒*z)     = si⇒*z ↯ ¬rs-sucZero
    prop-a8 (num (suc nvᵤ)) (r-suc t⇒i ◅ si⇒*su)    with lem-a8-suc si⇒*su
    ... | i⇒*u                                       = e-suc nvᵤ (prop-a8 (num nvᵤ) (t⇒i ◅ i⇒*u))
    prop-a8 vᵤ              (r-predZero ◅ ε)          = e-predZero (e-val (num zero))
    prop-a8 vᵤ              (r-predZero ◅ () ◅ _)
    prop-a8 true            (r-predSuc nvₜ ◅ t⇒*t)   = t⇒*t ↯ ¬rs-numTrue nvₜ
    prop-a8 false           (r-predSuc nvₜ ◅ t⇒*f)   = t⇒*f ↯ ¬rs-numFalse nvₜ
    prop-a8 (num nvᵤ)       (r-predSuc _ ◅ t⇒*u)     = e-predSuc nvᵤ (prop-a8 (num (suc nvᵤ))
                                                                               (rs-suc t⇒*u))
    prop-a8 true            (r-pred t⇒i ◅ pi⇒*t)    = pi⇒*t ↯ ¬rs-predTrue
    prop-a8 false           (r-pred t⇒i ◅ pi⇒*f)    = pi⇒*f ↯ ¬rs-predFalse
    prop-a8 (num nvᵤ)       (r-pred t⇒i ◅ pi⇒*u)    with lem-a8-pred nvᵤ pi⇒*u
    ... | inj₁ (i⇒*z , refl)                         = e-predZero (prop-a8 (num nvᵤ) (t⇒i ◅ i⇒*z))
    ... | inj₂ (i⇒*su)                               = e-predSuc nvᵤ (prop-a8 (num (suc nvᵤ)) (t⇒i ◅ i⇒*su))
    prop-a8 vᵤ              (r-iszeroZero ◅ ε)        = e-iszeroZero (e-val (num zero))
    prop-a8 vᵤ              (r-iszeroZero ◅ () ◅ _)
    prop-a8 vᵤ              (r-iszeroSuc nvₜ ◅ ε)     = e-iszeroSuc nvₜ (e-val (num (suc nvₜ)))
    prop-a8 vᵤ              (r-iszeroSuc _ ◅ () ◅ _)
    prop-a8 vᵤ              (r-iszero t⇒i ◅ izi⇒*u) with lem-a8-iszero vᵤ izi⇒*u
    ... | inj₁ (i⇒*z , refl)                         = e-iszeroZero (prop-a8 (num zero) (t⇒i ◅ i⇒*z))
    ... | inj₂ ((_ , nvy , i⇒*sy) , refl)            = e-iszeroSuc nvy (prop-a8 (num (suc nvy))
                                                                                 (t⇒i ◅ i⇒*sy))
    prop-a8 vᵤ              (r-ifTrue ◅ t₂⇒*u)       = e-ifTrue vᵤ (e-val true) (prop-a8 vᵤ t₂⇒*u)
    prop-a8 vᵤ              (r-ifFalse ◅ t₃⇒*u)      = e-ifFalse vᵤ (e-val false) (prop-a8 vᵤ t₃⇒*u)
    prop-a8 vᵤ              (r-if t₁⇒i₁ ◅ itei₁⇒*u) with lem-a8-if vᵤ itei₁⇒*u
    ... | inj₁ (i₁⇒*t , t₂⇒*u)                      = e-ifTrue vᵤ (prop-a8 true (t₁⇒i₁ ◅ i₁⇒*t))
                                                                    (prop-a8 vᵤ t₂⇒*u)
    ... | inj₂ (i₁⇒*f , t₃⇒*u)                      = e-ifFalse vᵤ (prop-a8 false (t₁⇒i₁ ◅ i₁⇒*f))
                                                                     (prop-a8 vᵤ t₃⇒*u)


-- This concludes Exercise 3.5.17.

    prop-a7-a8 : ∀ {t u} → (vᵤ : Value u) → (t ⇓ u) ↔ (t ⇒* u)
    prop-a7-a8 vᵤ = prop-a7 vᵤ , prop-a8 vᵤ


---------------------------------------------------------------------------------------------------------------
--
-- 3.5.18. Exercise [⋆⋆ ↛]
-- “Suppose we want to change the evaluation strategy of our language so that the `then` and `else` branches of
-- an `if` expression are evaluated (in that order) _before_ the guard is evaluated.  Show how the reduction
-- rules need to change to achieve this effect.”
-- (skipped)


---------------------------------------------------------------------------------------------------------------
--
-- 3.6. Notes


---------------------------------------------------------------------------------------------------------------
