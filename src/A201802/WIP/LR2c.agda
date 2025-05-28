{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module A201802.WIP.LR2c where

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


data Val {g} : Term g → Set
  where
    instance
      val-LAM   : ∀ {M} → Val (LAM M)
      val-TRUE  : Val TRUE
      val-FALSE : Val FALSE


data EC (g : Nat) : Set
  where
    ec-[]   : EC g
    ec-APP₁ : EC g → Term g → EC g
    ec-APP₂ : (M : Term g) → EC g → {{_ : Val M}} → EC g
    ec-IF   : EC g → Term g → Term g → EC g


_[_] : ∀ {g} → EC g → Term g → Term g
ec-[]         [ M ] = M
ec-APP₁ E N   [ M ] = APP (E [ M ]) N
ec-APP₂ N E   [ M ] = APP N (E [ M ])
ec-IF   E N O [ M ] = IF (E [ M ]) N O


infix 3 _↦_
data _↦_ {g} : Term g → Term g → Set
  where
    red-APP-LAM  : ∀ {M N} → APP (LAM M) N ↦ CUT N M
    red-IF-TRUE  : ∀ {M N} → IF TRUE M N ↦ M
    red-IF-FALSE : ∀ {M N} → IF FALSE M N ↦ N
    cong-ec      : ∀ {M M′} → (E : EC g) → M ↦ M′
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
_⇓_ : ∀ {g} → Term g → (M′ : Term g) → {{_ : Val M′}} → Set
M ⇓ M′ = M ⤅ M′


_⇓ : ∀ {g} → Term g → Set
M ⇓ = Σ (Term _) (\ M′ → Σ (Val M′) (\ vM′ → (M ⇓ M′) {{vM′}}))


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
                      → (E : EC g) → M ↦ M′ → Γ ⊢ E [ M ] ⦂ A
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


tp⇓ : ∀ {g M M′ A} → {Γ : Types g} {{_ : Val M′}}
                   → M ⇓ M′ → Γ ⊢ M ⦂ A
                   → Γ ⊢ M′ ⦂ A
tp⇓ M⇓M′ 𝒟 = tp⤅ M⇓M′ 𝒟


--------------------------------------------------------------------------------


lem-IF-TRUE : ∀ {g} → {M N N′ O : Term g} → {{_ : Val N′}}
                    → M ⇓ TRUE → N ⇓ N′
                    → IF M N O ⇓ N′
lem-IF-TRUE done                 N⇓N′ = step red-IF-TRUE N⇓N′
lem-IF-TRUE (step M↦M″ M″⇓TRUE) N⇓N′ = step (cong-ec (ec-IF ec-[] _ _) M↦M″) (lem-IF-TRUE M″⇓TRUE N⇓N′)


lem-IF-FALSE : ∀ {g} → {M N O O′ : Term g} → {{_ : Val O′}}
                     → M ⇓ FALSE → O ⇓ O′
                     → IF M N O ⇓ O′
lem-IF-FALSE done                  O⇓O′ = step red-IF-FALSE O⇓O′
lem-IF-FALSE (step M↦M′ M′⇓FALSE) O⇓O′ = step (cong-ec (ec-IF ec-[] _ _) M↦M′) (lem-IF-FALSE M′⇓FALSE O⇓O′)


private
  module Impossible
    where
      sn : ∀ {M A} → ∙ ⊢ M ⦂ A → M ⇓
      sn (var ())
      sn (lam 𝒟)    = LAM _ , (val-LAM , done)
      sn (app 𝒟 ℰ)  = {!!}
      sn true       = TRUE , (val-TRUE , done)
      sn false      = FALSE , (val-FALSE , done)
      sn (if 𝒟 ℰ ℱ) with sn 𝒟 | sn ℰ | sn ℱ
      sn (if 𝒟 ℰ ℱ) | M′ , (vM′ , M⇓M′) | N⇓ | O⇓ with tp⇓ {{vM′}} M⇓M′ 𝒟
      sn (if 𝒟 ℰ ℱ) | LAM M″ , (val-LAM   , M⇓LAM-M″) | N⇓                | O⇓                | ()
      sn (if 𝒟 ℰ ℱ) | TRUE   , (val-TRUE  , M⇓TRUE)   | N′ , (vN′ , N⇓N′) | O⇓                | true  = N′ , (vN′ , lem-IF-TRUE {{vN′}} M⇓TRUE N⇓N′)
      sn (if 𝒟 ℰ ℱ) | FALSE  , (val-FALSE , M⇓FALSE)  | N⇓                | O′ , (vO′ , O⇓O′) | false = O′ , (vO′ , lem-IF-FALSE {{vO′}} M⇓FALSE O⇓O′)
      sn _          = {!!}


--------------------------------------------------------------------------------
