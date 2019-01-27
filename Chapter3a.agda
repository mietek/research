module Chapter3a where

open import Chapter3 public


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
-- “Show that the small-step and big-step semantics for this language coincide, i.e. `t ⟹* v` iff `t ⇓ v`.”

private
  module Exercise-3-5-17 where
    open NumbersAndBooleansGetStuck

    {-# DISPLAY _* _⟹_ = _⟹*_ #-}

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
-- “If `t₁ ⟹* u₁` then `if t₁ then t₂ else t₃ ⟹* if u₁ then t₂ else t₃`.  (And similarly for the other term
-- constructors.)”
-- (shown inline below)


---------------------------------------------------------------------------------------------------------------
--
-- Proposition A.7.
-- “If `t ⇓ v` then `t ⟹* v`.”

    prop-a-7 : ∀ {t u} → (vᵤ : Value u) → t ⇓ u → t ⟹* u
    prop-a-7 vᵤ (e-val vₜ)                     = []
    prop-a-7 vᵤ (e-suc nvᵤ t⇓u)                = map r-suc (prop-a-7 (num nvᵤ) t⇓u)
    prop-a-7 vᵤ (e-predZero t⇓zero)            = map r-pred (prop-a-7 vᵤ t⇓zero) ∷ʳ r-predZero
    prop-a-7 vᵤ (e-predSuc nvᵤ t⇓sucu)         = map r-pred (prop-a-7 (num (suc nvᵤ)) t⇓sucu) ∷ʳ r-predSuc nvᵤ
    prop-a-7 vᵤ (e-iszeroZero t⇓zero)          = map r-iszero (prop-a-7 (num zero) t⇓zero) ∷ʳ r-iszeroZero
    prop-a-7 vᵤ (e-iszeroSuc nvᵤ t⇓sucu)       = map r-iszero (prop-a-7 (num (suc nvᵤ)) t⇓sucu) ∷ʳ r-iszeroSuc nvᵤ
    prop-a-7 vᵤ (e-ifTrue vᵤ₂ t₁⇓true t₂⇓u₂)   = map r-if (prop-a-7 true t₁⇓true) ++ r-ifTrue ∷ (prop-a-7 vᵤ₂ t₂⇓u₂)
    prop-a-7 vᵤ (e-ifFalse vᵤ₃ t₁⇓false t₃⇓u₃) = map r-if (prop-a-7 false t₁⇓false) ++ r-ifFalse ∷ (prop-a-7 vᵤ₃ t₃⇓u₃)


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Clean this up.

    help-1 : ∀ {t} → NumericValue t → ¬ (t ⟹* true)
    help-1 zero      (() ∷ _)
    help-1 (suc nvₜ) (r-suc t⟹u ∷ sucu⟹*true) = t⟹u ↯ nv→nf nvₜ

    help-2 : ∀ {t} → NumericValue t → ¬ (t ⟹* false)
    help-2 zero      (() ∷ _)
    help-2 (suc nvₜ) (r-suc t⟹u ∷ sucu⟹*false) = t⟹u ↯ nv→nf nvₜ

    help-3 : ∀ {t} → ¬ (suc t ⟹* true)
    help-3 = λ where (r-suc _ ∷ sucx⟹*true) → sucx⟹*true ↯ help-3

    help-4 : ∀ {t} → ¬ (suc t ⟹* false)
    help-4 = λ where (r-suc _ ∷ sucx⟹*false) → sucx⟹*false ↯ help-4

    help-5 : ∀ {t} → ¬ (suc t ⟹* zero)
    help-5 = λ where (r-suc _ ∷ sucx⟹*zero) → sucx⟹*zero ↯ help-5

    help-6a : ¬ (zero ⟹* true)
    help-6a = λ where (() ∷ _)

    help-6 : ∀ {t} → ¬ (pred t ⟹* true)
    help-6 = λ where (r-predZero ∷ zero⟹*true) → zero⟹*true ↯ help-6a
                     (r-predSuc nvₓ ∷ x⟹*true) → x⟹*true ↯ help-1 nvₓ
                     (r-pred _ ∷ predx⟹*true)  → predx⟹*true ↯ help-6

    help-7a : ¬ (zero ⟹* false)
    help-7a = λ where (() ∷ _)

    help-7 : ∀ {t} → ¬ (pred t ⟹* false)
    help-7 = λ where (r-predZero ∷ zero⟹*false) → zero⟹*false ↯ help-7a
                     (r-predSuc nvₓ ∷ x⟹*false) → x⟹*false ↯ help-2 nvₓ
                     (r-pred _ ∷ predx⟹*false)  → predx⟹*false ↯ help-7

    help-8 : ∀ {t u} → t ⟹* suc u → suc t ⟹* suc (suc u)
    help-8 []                  = []
    help-8 (t⟹x ∷ x⟹*sucu) = (r-suc t⟹x ∷ []) ++ help-8 x⟹*sucu


---------------------------------------------------------------------------------------------------------------
--
-- Lemma A.8.
-- “If `if t₁ then t₂ else t₃ ⟹* v`, then either `t₁ ⟹* true` and `t₂ ⟹* v` or `t₁ ⟹* false` and
-- `t₃ ⟹* v`.  Moreover, the evaluation sequences for `t₁` and `t₂` or `t₃` are strictly shorter than the
-- given evaluation sequence.  (And similarly for the other term constructors.)”

    lem-a-8-suc : ∀ {t u} → suc t ⟹* suc u → t ⟹* u
    lem-a-8-suc [] = []
    lem-a-8-suc (r-suc t⟹x ∷ sucx⟹*sucu) with lem-a-8-suc sucx⟹*sucu
    ... | x⟹*u                             = t⟹x ∷ x⟹*u

    lem-a-8-pred : ∀ {t u} → (nvᵤ : NumericValue u) → pred t ⟹* u →
                     (t ⟹* zero × u ≡ zero) ⊎ (t ⟹* suc u)
    lem-a-8-pred ()      []
    lem-a-8-pred zero    (r-predZero ∷ zero⟹*zero)         = inj₁ (zero⟹*zero , refl)
    lem-a-8-pred (suc _) (r-predZero ∷ () ∷ _)
    lem-a-8-pred zero    (r-predSuc zero ∷ _)                = inj₂ []
    lem-a-8-pred zero    (r-predSuc (suc _) ∷ sucx⟹*zero)  = sucx⟹*zero ↯ help-5
    lem-a-8-pred (suc _) (r-predSuc _ ∷ x⟹*sucu)           = inj₂ (help-8 x⟹*sucu)
    lem-a-8-pred nvᵤ     (r-pred t⟹x ∷ predx⟹*u)         with lem-a-8-pred nvᵤ predx⟹*u
    ... | inj₁ (x⟹*zero , refl)                            = inj₁ (t⟹x ∷ x⟹*zero , refl)
    ... | inj₂ x⟹*sucu                                     = inj₂ (t⟹x ∷ x⟹*sucu)

    lem-a-8-iszero : ∀ {t u} → (vᵤ : Value u) → iszero t ⟹* u →
                     (t ⟹* zero × u ≡ true) ⊎ ((∃ λ x → NumericValue x × t ⟹* suc x) × u ≡ false)
    lem-a-8-iszero vᵤ (r-iszeroZero ∷ [])             = inj₁ ([] , refl)
    lem-a-8-iszero vᵤ (r-iszeroZero ∷ () ∷ _)
    lem-a-8-iszero vᵤ (r-iszeroSuc nvₜ ∷ [])          = inj₂ ((_ , nvₜ , []) , refl)
    lem-a-8-iszero vᵤ (r-iszeroSuc nvₜ ∷ () ∷ _)
    lem-a-8-iszero vᵤ (r-iszero t⟹x ∷ iszerox⟹*u) with lem-a-8-iszero vᵤ iszerox⟹*u
    ... | inj₁ (x⟹*zero , refl)                     = inj₁ (t⟹x ∷ x⟹*zero , refl)
    ... | inj₂ ((_ , nvy , x⟹*sucy) , refl)         = inj₂ ((_ , nvy , t⟹x ∷ x⟹*sucy) , refl)
    lem-a-8-iszero (num ()) []

    lem-a-8-if : ∀ {t₁ t₂ t₃ u} → (vᵤ : Value u) → if t₁ then t₂ else t₃ ⟹* u →
                 (t₁ ⟹* true × t₂ ⟹* u) ⊎ (t₁ ⟹* false × t₃ ⟹* u)
    lem-a-8-if vᵤ       (r-ifTrue ∷ ift₁thent₂elset₃⟹*u)     = inj₁ ([] , ift₁thent₂elset₃⟹*u)
    lem-a-8-if vᵤ       (r-ifFalse ∷ ift₁thent₂elset₃⟹*u)    = inj₂ ([] , ift₁thent₂elset₃⟹*u)
    lem-a-8-if vᵤ       (r-if t₁⟹x₁ ∷ ifx₁thent₂elset₃⟹*u) with lem-a-8-if vᵤ ifx₁thent₂elset₃⟹*u
    ... | inj₁ (x₁⟹*true , t₂⟹*u)                          = inj₁ (t₁⟹x₁ ∷ x₁⟹*true , t₂⟹*u)
    ... | inj₂ (x₁⟹*false , t₃⟹*u)                         = inj₂ (t₁⟹x₁ ∷ x₁⟹*false , t₃⟹*u)
    lem-a-8-if (num ()) []


---------------------------------------------------------------------------------------------------------------
--
-- Proposition A.8.
-- “If `t ⟹* v` then `t ⇓ v`.”
--
-- This concludes Exercise 3.5.17.

    prop-a-8 : ∀ {t u} → (vᵤ : Value u) → t ⟹* u → t ⇓ u
    prop-a-8 vₜ              []                                     = e-val vₜ
    prop-a-8 true            (r-suc _ ∷ sucx⟹*true)               = sucx⟹*true ↯ help-3
    prop-a-8 false           (r-suc _ ∷ sucx⟹*false)              = sucx⟹*false ↯ help-4
    prop-a-8 (num zero)      (r-suc t⟹x ∷ sucx⟹*zero)           = sucx⟹*zero ↯ help-5
    prop-a-8 (num (suc nvᵤ)) (r-suc t⟹x ∷ sucx⟹*sucu)           with lem-a-8-suc sucx⟹*sucu
    ... | x⟹*u                                                    = e-suc nvᵤ (prop-a-8 (num nvᵤ) (t⟹x ∷ x⟹*u))
    prop-a-8 vᵤ              (r-predZero ∷ [])                      = e-predZero (e-val (num zero))
    prop-a-8 vᵤ              (r-predZero ∷ () ∷ _)
    prop-a-8 true            (r-predSuc nvₜ ∷ t⟹*true)            = t⟹*true ↯ help-1 nvₜ
    prop-a-8 false           (r-predSuc nvₜ ∷ t⟹*false)           = t⟹*false ↯ help-2 nvₜ
    prop-a-8 (num nvᵤ)       (r-predSuc _ ∷ t⟹*u)                 = e-predSuc nvᵤ (prop-a-8 (num (suc nvᵤ)) (map r-suc t⟹*u))
    prop-a-8 true            (r-pred t⟹x ∷ predx⟹*true)         = predx⟹*true ↯ help-6
    prop-a-8 false           (r-pred t⟹x ∷ predx⟹*false)        = predx⟹*false ↯ help-7
    prop-a-8 (num nvᵤ)       (r-pred t⟹x ∷ predx⟹*u)            with lem-a-8-pred nvᵤ predx⟹*u
    ... | inj₁ (x⟹*zero , refl)                                   = e-predZero (prop-a-8 (num nvᵤ) (t⟹x ∷ x⟹*zero))
    ... | inj₂ (x⟹*sucu)                                          = e-predSuc nvᵤ (prop-a-8 (num (suc nvᵤ)) (t⟹x ∷ x⟹*sucu))
    prop-a-8 vᵤ              (r-iszeroZero ∷ [])                    = e-iszeroZero (e-val (num zero))
    prop-a-8 vᵤ              (r-iszeroZero ∷ () ∷ _)
    prop-a-8 vᵤ              (r-iszeroSuc nvₜ ∷ [])                 = e-iszeroSuc nvₜ (e-val (num (suc nvₜ)))
    prop-a-8 vᵤ              (r-iszeroSuc _ ∷ () ∷ _)
    prop-a-8 vᵤ              (r-iszero t⟹x ∷ iszerox⟹*u)        with lem-a-8-iszero vᵤ iszerox⟹*u
    ... | inj₁ (x⟹*zero , refl)                                   = e-iszeroZero (prop-a-8 (num zero) (t⟹x ∷ x⟹*zero))
    ... | inj₂ ((_ , nvy , x⟹*sucy) , refl)                       = e-iszeroSuc nvy (prop-a-8 (num (suc nvy)) (t⟹x ∷ x⟹*sucy))
    prop-a-8 vᵤ              (r-ifTrue ∷ t₂⟹*u)                   = e-ifTrue vᵤ (e-val true) (prop-a-8 vᵤ t₂⟹*u)
    prop-a-8 vᵤ              (r-ifFalse ∷ t₃⟹*u)                  = e-ifFalse vᵤ (e-val false) (prop-a-8 vᵤ t₃⟹*u)
    prop-a-8 vᵤ              (r-if t₁⟹x₁ ∷ ifx₁thent₂elset₃⟹*u) with lem-a-8-if vᵤ ifx₁thent₂elset₃⟹*u
    ... | inj₁ (x₁⟹*true  , t₂⟹*u)                              = e-ifTrue vᵤ (prop-a-8 true (t₁⟹x₁ ∷ x₁⟹*true)) (prop-a-8 vᵤ t₂⟹*u)
    ... | inj₂ (x₁⟹*false , t₃⟹*u)                              = e-ifFalse vᵤ (prop-a-8 false (t₁⟹x₁ ∷ x₁⟹*false)) (prop-a-8 vᵤ t₃⟹*u)


---------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------
