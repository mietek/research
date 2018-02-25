{-# OPTIONS --allow-unsolved-metas #-}

module LR2 where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec
open import VecLemmas
open import AllVec
open import LR1


--------------------------------------------------------------------------------


data IsVal {g} : Term g → Set
  where
    instance
      val-LAM   : ∀ {M} → IsVal (LAM M)
      val-TRUE  : IsVal TRUE
      val-FALSE : IsVal FALSE


record Val (g : Nat) : Set
  where
    constructor val
    field
      term   : Term g
      {{iv}} : IsVal term


data EvalCx (g : Nat) : Set
  where
    ec-[]   : EvalCx g
    ec-APP₁ : EvalCx g → Term g → EvalCx g
    ec-APP₂ : Val g → EvalCx g → EvalCx g
    ec-IF   : EvalCx g → Term g → Term g → EvalCx g


_[_] : ∀ {g} → EvalCx g → Term g → Term g
ec-[]         [ M ] = M
ec-APP₁ E N   [ M ] = APP (E [ M ]) N
ec-APP₂ N E   [ M ] = APP (Val.term N) (E [ M ])
ec-IF   E N O [ M ] = IF (E [ M ]) N O


infix 3 _↦_
data _↦_ {g} : Term g → Term g → Set
  where
    red-APP-LAM  : ∀ {M N} → APP (LAM M) N ↦ CUT N M
    red-IF-TRUE  : ∀ {M N} → IF TRUE M N ↦ M
    red-IF-FALSE : ∀ {M N} → IF FALSE M N ↦ N
    cong-ec      : ∀ {M M′} → (E : EvalCx g) → M ↦ M′
                            → E [ M ] ↦ E [ M′ ]


infix 3 _⤅_
data _⤅_ {g} : Term g → Term g → Set
  where
    done : ∀ {M} → M ⤅ M
    step : ∀ {M M″ M′} → M ↦ M″ → M″ ⤅ M′ → M ⤅ M′


steps : ∀ {g} → {M M″ M′ : Term g} → M ⤅ M″ → M″ ⤅ M′ → M ⤅ M′
steps done                M⤅M′  = M⤅M′
steps (step M↦M‴ M‴⤅M″) M″⤅M′ = step M↦M‴ (steps M‴⤅M″ M″⤅M′)


infix 3 _⇓_
_⇓_ : ∀ {g} → Term g → Val g → Set
M ⇓ M′ = M ⤅ Val.term M′


_⇓ : ∀ {g} → Term g → Set
M ⇓ = Σ (Val _) (\ M′ → M ⇓ M′)


--------------------------------------------------------------------------------


mutual
  tp↦ : ∀ {g M M′ A} → {Γ : Types g}
                      → M ↦ M′ → Γ ⊢ M ⦂ A
                      → Γ ⊢ M′ ⦂ A
  tp↦ red-APP-LAM       (app (lam 𝒟) ℰ) = cut ℰ 𝒟
  tp↦ red-IF-TRUE       (if 𝒟 ℰ ℱ)      = ℰ
  tp↦ red-IF-FALSE      (if 𝒟 ℰ ℱ)      = ℱ
  tp↦ (cong-ec E M↦M′) 𝒟               = plug E M↦M′ 𝒟

  plug : ∀ {g M M′ A} → {Γ : Types g}
                      → (E : EvalCx g) → M ↦ M′ → Γ ⊢ E [ M ] ⦂ A
                      → Γ ⊢ E [ M′ ] ⦂ A
  plug ec-[]         M↦M′ 𝒟          = tp↦ M↦M′ 𝒟
  plug (ec-APP₁ E N) M↦M′ (app 𝒟 ℰ)  = app (plug E M↦M′ 𝒟) ℰ
  plug (ec-APP₂ N E) M↦M′ (app 𝒟 ℰ)  = app 𝒟 (plug E M↦M′ ℰ)
  plug (ec-IF E N O) M↦M′ (if 𝒟 ℰ ℱ) = if (plug E M↦M′ 𝒟) ℰ ℱ


tp⤅ : ∀ {g M M′ A} → {Γ : Types g}
                    → M ⤅ M′ → Γ ⊢ M ⦂ A
                    → Γ ⊢ M′ ⦂ A
tp⤅ done                𝒟 = 𝒟
tp⤅ (step M↦M″ M″⤅M′) 𝒟 = tp⤅ (M″⤅M′) (tp↦ M↦M″ 𝒟)


--------------------------------------------------------------------------------


lem-IF-TRUE : ∀ {g} → {M N N′ O : Term g}
                    → M ⤅ TRUE → N ⤅ N′
                    → IF M N O ⤅ N′
lem-IF-TRUE done                  N⤅N′ = step red-IF-TRUE N⤅N′
lem-IF-TRUE (step M↦M″ M″⤅TRUE) N⤅N′ = step (cong-ec (ec-IF ec-[] _ _) M↦M″) (lem-IF-TRUE M″⤅TRUE N⤅N′)


lem-IF-FALSE : ∀ {g} → {M N O O′ : Term g}
                     → M ⤅ FALSE → O ⤅ O′
                     → IF M N O ⤅ O′
lem-IF-FALSE done                   O⤅O′ = step red-IF-FALSE O⤅O′
lem-IF-FALSE (step M↦M′ M′⤅FALSE) O⤅O′ = step (cong-ec (ec-IF ec-[] _ _) M↦M′) (lem-IF-FALSE M′⤅FALSE O⤅O′)


private
  module Impossible
    where
      sn : ∀ {M A} → ∙ ⊢ M ⦂ A → M ⇓
      sn (var ())
      sn (lam 𝒟)   = val (LAM _) , done
      sn (app 𝒟 ℰ) = {!!}
      sn true      = val TRUE , done
      sn false     = val FALSE , done
      sn (if 𝒟 ℰ ℱ) with sn 𝒟 | sn ℰ | sn ℱ
      sn (if 𝒟 ℰ ℱ) | M′ , M⤅M′ | N⇓ | O⇓ with tp⤅ M⤅M′ 𝒟
      sn (if 𝒟 ℰ ℱ) | val (LAM M″) {{val-LAM}}   , M⤅LAM-M″ | N⇓         | O⇓         | ()
      sn (if 𝒟 ℰ ℱ) | val TRUE     {{val-TRUE}}  , M⤅TRUE   | N′ , N⤅N′ | O⇓         | true  = N′ , lem-IF-TRUE M⤅TRUE N⤅N′
      sn (if 𝒟 ℰ ℱ) | val FALSE    {{val-FALSE}} , M⤅FALSE  | N⇓         | O′ , O⤅O′ | false = O′ , lem-IF-FALSE M⤅FALSE O⤅O′


--------------------------------------------------------------------------------
