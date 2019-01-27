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
-- Lemma A.8.
-- “If `if t₁ then t₂ else t₃ ⟹* v`, then either `t₁ ⟹* true` and `t₂ ⟹* v` or `t₁ ⟹* false` and
-- `t₃ ⟹* v`.  Moreover, the evaluation sequences for `t₁` and `t₂` or `t₃` are strictly shorter than the
-- given evaluation sequence.  (And similarly for the other term constructors.)”
-- (unknown)


---------------------------------------------------------------------------------------------------------------
--
-- Proposition A.8.
-- “If `t ⟹* v` then `t ⇓ v`.”

    prop-a-8 : ∀ {t u} → (vᵤ : Value u) → t ⟹* u → t ⇓ u
    prop-a-8 {t}                        vₜ []                                     = e-val vₜ
    prop-a-8 {suc t}                    vᵤ (r-suc t⟹x ∷ sucx⟹*u)              = {!!}
    prop-a-8 {pred zero}                vᵤ (r-predZero ∷ [])                      = e-predZero (e-val (num zero))
    prop-a-8 {pred zero}                vᵤ (r-predZero ∷ () ∷ _)
    prop-a-8 {pred (suc t)}             vᵤ (r-predSuc nvₜ ∷ t⟹*u)               = {!!}
    prop-a-8 {pred t}                   vᵤ (r-pred t⟹x ∷ predx⟹*u)            = {!!}
    prop-a-8 {iszero zero}              vᵤ (r-iszeroZero ∷ [])                    = e-iszeroZero (e-val (num zero))
    prop-a-8 {iszero zero}              vᵤ (r-iszeroZero ∷ () ∷ _)
    prop-a-8 {iszero (suc t)}           vᵤ (r-iszeroSuc nvₜ ∷ [])                 = e-iszeroSuc nvₜ (e-val (num (suc nvₜ)))
    prop-a-8 {iszero (suc t)}           vᵤ (r-iszeroSuc nvₜ ∷ () ∷ _)
    prop-a-8 {iszero t}                 vᵤ (r-iszero t⟹x ∷ iszerox⟹*u)        = {!!}
    prop-a-8 {if true then t₂ else t₃}  vᵤ (r-ifTrue ∷ t₂⟹*u)                   = {!!}
    prop-a-8 {if false then t₂ else t₃} vᵤ (r-ifFalse ∷ t₃⟹*u)                  = {!!}
    prop-a-8 {if t₁ then t₂ else t₃}    vᵤ (r-if t₁⟹x₁ ∷ ifx₁thent₂elset₃⟹*u) = {!!}


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
