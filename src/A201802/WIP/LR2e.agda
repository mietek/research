{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module A201802.WIP.LR2e where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.FinLemmas
open import A201801.Vec
open import A201801.VecLemmas
open import A201801.AllVec

open import A201802.LR0
open import A201802.LR0Lemmas
open import A201802.LR1


--------------------------------------------------------------------------------


-- `iv : IsVal M` says that the term `M` is a value
data IsVal {g} : Term g → Set
  where
    instance
      val-LAM   : ∀ {M} → IsVal (LAM M)
      val-TRUE  : IsVal TRUE
      val-FALSE : IsVal FALSE


-- -- `val M {{iv}} : Val g` keeps the term `M` together with the evidence `iv` that `M` is a value
-- record Val (g : Nat) : Set
--   where
--     constructor val
--     field
--       term   : Term g
--       {{iv}} : IsVal term


-- `E : EvCx g` is a well-scoped call-by-value evaluation context
data EvCx (g : Nat) : Set
  where
    ec-[]      : EvCx g
    ec-fun-APP : EvCx g → Term g → EvCx g
    ec-arg-APP : (M : Term g) → {{_ : IsVal M}} → EvCx g → EvCx g
    ec-IF      : EvCx g → Term g → Term g → EvCx g


-- `E [ M ] : Term g` plugs the term `M` into the evaluation context `E`
_[_] : ∀ {g} → EvCx g → Term g → Term g
ec-[]            [ M ] = M
ec-fun-APP E N   [ M ] = APP (E [ M ]) N
ec-arg-APP N E   [ M ] = APP N (E [ M ])
ec-IF      E N O [ M ] = IF (E [ M ]) N O


-- `_ : M ↦ M′` says that the term `M` reduces in one step to the term `M′`
infix 3 _↦_
data _↦_ {g} : Term g → Term g → Set
  where
    step-APP-LAM  : ∀ {M N} → APP (LAM M) N ↦ CUT N M
    step-IF-TRUE  : ∀ {N O} → IF TRUE N O ↦ N
    step-IF-FALSE : ∀ {N O} → IF FALSE N O ↦ O
    step-cong     : ∀ {M M′} → (E : EvCx g) → M ↦ M′
                             → E [ M ] ↦ E [ M′ ]


-- `_ : M ⤅ M′` says that the term `M` reduces in some number of steps to the term `M′`
infix 3 _⤅_
data _⤅_ {g} : Term g → Term g → Set
  where
    done : ∀ {M} → M ⤅ M
    _⨾₁_ : ∀ {M M″ M′} → M ↦ M″ → M″ ⤅ M′
                       → M ⤅ M′


-- `_⤅_` is the reflexive and transitive closure of `_↦_`
_⨾ₙ_ : ∀ {g} → {M M″ M′ : Term g}
             → M ⤅ M″ → M″ ⤅ M′
             → M ⤅ M′
done              ⨾ₙ M⤅M′  = M⤅M′
(M↦M‴ ⨾₁ M‴⤅M″) ⨾ₙ M″⤅M′ = M↦M‴ ⨾₁ (M‴⤅M″ ⨾ₙ M″⤅M′)


-- `_ : M ⇓ M′` says that the term `M` evaluates to the value `M′
infix 3 _⇓_
_⇓_ : ∀ {g} → Term g → (M′ : Term g) → {{_ : IsVal M′}} → Set
M ⇓ M′ = M ⤅ M′


-- `_ : M ⇓` says that the evaluation of the term `M` terminates

-- _⇓ : ∀ {g} → Term g → Set
-- M ⇓ = Σ (Term _) (\ M′ → Σ (IsVal M′) (\ iv → (M ⇓ M′) {{iv}}))

_⇓ : ∀ {g} → Term g → Set
M ⇓ = Σ (Term _) (\ M′ → {!Σ″ (IsVal M′) (\ {{iv}} → (M ⇓ M′) {{iv}})!})

-- infix 4 _/_/_
-- record _⇓ {g} (M : Term g) : Set
--   where
--     constructor _/_/_
--     field
--       M′   : Term g
--       ivM′ : IsVal M′
--       M⇓M′ : (M ⇓ M′) {{ivM′}}


--------------------------------------------------------------------------------


-- `_↦_` is type-preserving
mutual
  tp↦ : ∀ {g M M′ A} → {Γ : Types g}
                       → M ↦ M′ → Γ ⊢ M ⦂ A
                       → Γ ⊢ M′ ⦂ A
  tp↦ step-APP-LAM        (app (lam 𝒟) ℰ) = cut ℰ 𝒟
  tp↦ step-IF-TRUE        (if 𝒟 ℰ ℱ)      = ℰ
  tp↦ step-IF-FALSE       (if 𝒟 ℰ ℱ)      = ℱ
  tp↦ (step-cong E M↦M′) 𝒟               = cong-tp↦ E M↦M′ 𝒟

  cong-tp↦ : ∀ {g M M′ A} → {Γ : Types g}
                           → (E : EvCx g) → M ↦ M′ → Γ ⊢ E [ M ] ⦂ A
                           → Γ ⊢ E [ M′ ] ⦂ A
  cong-tp↦ ec-[]            M↦M′ 𝒟          = tp↦ M↦M′ 𝒟
  cong-tp↦ (ec-fun-APP E N) M↦M′ (app 𝒟 ℰ)  = app (cong-tp↦ E M↦M′ 𝒟) ℰ
  cong-tp↦ (ec-arg-APP N E) M↦M′ (app 𝒟 ℰ)  = app 𝒟 (cong-tp↦ E M↦M′ ℰ)
  cong-tp↦ (ec-IF E N O)    M↦M′ (if 𝒟 ℰ ℱ) = if (cong-tp↦ E M↦M′ 𝒟) ℰ ℱ


-- `_⤅_` is type-preserving
tp⤅ : ∀ {g M M′ A} → {Γ : Types g}
                    → M ⤅ M′ → Γ ⊢ M ⦂ A
                    → Γ ⊢ M′ ⦂ A
tp⤅ done              𝒟 = 𝒟
tp⤅ (M↦M″ ⨾₁ M″⤅M′) 𝒟 = tp⤅ (M″⤅M′) (tp↦ M↦M″ 𝒟)


--------------------------------------------------------------------------------


eval-IF : ∀ {g} → {M M′ N O : Term g}
                → M ⤅ M′
                → IF M N O ⤅ IF M′ N O
eval-IF {N = N} {O} done              = done
eval-IF {N = N} {O} (M↦M″ ⨾₁ M″⤅M′) = step-cong (ec-IF ec-[] N O) M↦M″ ⨾₁ eval-IF M″⤅M′


eval-IF-TRUE : ∀ {g} → {M N O : Term g}
                     → M ⤅ TRUE
                     → IF M N O ⤅ N
eval-IF-TRUE M⤅TRUE = eval-IF M⤅TRUE ⨾ₙ (step-IF-TRUE ⨾₁ done)


eval-IF-FALSE : ∀ {g} → {M N O : Term g}
                      → M ⤅ FALSE
                      → IF M N O ⤅ O
eval-IF-FALSE M⤅FALSE = eval-IF M⤅FALSE ⨾ₙ (step-IF-FALSE ⨾₁ done)


-- term-IF-TRUE : ∀ {g} → {M N O : Term g}
--                      → M ⤅ TRUE → N ⇓
--                      → IF M N O ⇓
-- term-IF-TRUE M⤅TRUE (N′ , ⟪ N⤅N′ ⟫) = N′ , ⟪ eval-IF-TRUE M⤅TRUE ⨾ₙ N⤅N′ ⟫


-- term-IF-FALSE : ∀ {g} → {M N O : Term g}
--                       → M ⤅ FALSE → O ⇓
--                       → IF M N O ⇓
-- term-IF-FALSE M⤅FALSE (O′ , ⟪ O⤅O′ ⟫) = O′ , ⟪ eval-IF-FALSE M⤅FALSE ⨾ₙ O⤅O′ ⟫


private
  module Impossible
    where
      sn : ∀ {M A} → ∙ ⊢ M ⦂ A
                   → M ⇓
      sn (var ())
      sn (lam 𝒟)    = {!LAM _ , ⟪ done ⟫!}
      sn (app 𝒟 ℰ)  = {!!}
      sn true       = {!TRUE , ⟪ done ⟫!}
      sn false      = {!FALSE , ⟪ done ⟫!}
      sn _          = {!!}
      -- sn (if 𝒟 ℰ ℱ) with sn 𝒟
      -- sn (if 𝒟 ℰ ℱ) | M′     , ⟪ M⤅M′ ⟫ with tp⤅ M⤅M′ 𝒟
      -- sn (if 𝒟 ℰ ℱ) | LAM M″ , ⟪_⟫ {{val-LAM}}   M⤅LAM-M″ | ()
      -- sn (if 𝒟 ℰ ℱ) | TRUE   , ⟪_⟫ {{val-TRUE}}  M⤅TRUE   | true  = term-IF-TRUE M⤅TRUE (sn ℰ)
      -- sn (if 𝒟 ℰ ℱ) | FALSE  , ⟪_⟫ {{val-FALSE}} M⤅FALSE  | false = term-IF-FALSE M⤅FALSE (sn ℱ)


--------------------------------------------------------------------------------
