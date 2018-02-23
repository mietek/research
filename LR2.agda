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


data Val {g} : Term g → Set
  where
    val-LAM   : ∀ {M} → Val (LAM M)
    val-TRUE  : Val TRUE
    val-FALSE : Val FALSE


data EC (g : Nat) : Set
  where
    ec-[]   : EC g
    ec-APP₁ : EC g → Term g → EC g
    ec-APP₂ : Term g → EC g → EC g
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
    red-ec       : ∀ {M M′} → (E : EC g) → M ↦ M′
                            → E [ M ] ↦ E [ M′ ]


infix 3 _⇓_
data _⇓_ {g} : Term g → (M′ : Term g) → Set
  where
    eval-LAM   : ∀ {M} → LAM M ⇓ LAM M
    eval-TRUE  : TRUE ⇓ TRUE
    eval-FALSE : FALSE ⇓ FALSE
    eval-red   : ∀ {M M′ M″} → M ↦ M′ → M′ ⇓ M″ → M ⇓ M″


_⇓ : ∀ {g} → (M : Term g) → Set
M ⇓ = Σ (Term _) (\ M′ → M ⇓ M′)


--------------------------------------------------------------------------------


val : ∀ {g} → {M M′ : Term g}
            → M ⇓ M′
            → Val M′
val eval-LAM               = val-LAM
val eval-TRUE              = val-TRUE
val eval-FALSE             = val-FALSE
val (eval-red M↦M′ M′⇓M″) = val M′⇓M″


mutual
  tp↦ : ∀ {g M M′ A} → {Γ : Types g}
                      → M ↦ M′ → Γ ⊢ M ⦂ A
                      → Γ ⊢ M′ ⦂ A
  tp↦ red-APP-LAM      (app (lam 𝒟) ℰ) = cut ℰ 𝒟
  tp↦ red-IF-TRUE      (if 𝒟 ℰ ℱ)      = ℰ
  tp↦ red-IF-FALSE     (if 𝒟 ℰ ℱ)      = ℱ
  tp↦ (red-ec E M↦M′) 𝒟               = plug E M↦M′ 𝒟

  plug : ∀ {g M M′ A} → {Γ : Types g}
                      → (E : EC g) → M ↦ M′ → Γ ⊢ E [ M ] ⦂ A
                      → Γ ⊢ E [ M′ ] ⦂ A
  plug ec-[]         M↦M′ 𝒟          = tp↦ M↦M′ 𝒟
  plug (ec-APP₁ E N) M↦M′ (app 𝒟 ℰ)  = app (plug E M↦M′ 𝒟) ℰ
  plug (ec-APP₂ N E) M↦M′ (app 𝒟 ℰ)  = app 𝒟 (plug E M↦M′ ℰ)
  plug (ec-IF E N O) M↦M′ (if 𝒟 ℰ ℱ) = if (plug E M↦M′ 𝒟) ℰ ℱ


tp⇓ : ∀ {g M M′ A} → {Γ : Types g}
                   → M ⇓ M′ → Γ ⊢ M ⦂ A
                   → Γ ⊢ M′ ⦂ A
tp⇓ eval-LAM               𝒟 = 𝒟
tp⇓ eval-TRUE              𝒟 = 𝒟
tp⇓ eval-FALSE             𝒟 = 𝒟
tp⇓ (eval-red M↦M′ M′⇓M″) 𝒟 = tp⇓ M′⇓M″ (tp↦ M↦M′ 𝒟)


--------------------------------------------------------------------------------


lem-CUT : ∀ {g} → {M M′ : Term g} {N : Term (suc g)}
                → M ⇓ M′
                → CUT M N ⇓ CUT M′ N
lem-CUT M⇓M′ = {!!}


lem-APP-LAM : ∀ {g} → {M : Term g} {M′ : Term (suc g)} {N N′ : Term g}
                    → M ⇓ LAM M′ → N ⇓ N′
                    → APP M N ⇓ CUT N′ M′
lem-APP-LAM {M = M} {M′} {N} {N′} eval-LAM                   N⇓N′
  = eval-red {M = APP (LAM M′) N} {CUT N M′} {CUT N′ M′} red-APP-LAM (lem-CUT {M = N} {N′} {M′} N⇓N′)
lem-APP-LAM {M = M} {M″} {N} {N′} (eval-red {M′ = M′} M↦M′ M′⇓LAM-M″) N⇓N′
  = eval-red {M = APP M N} {ec-APP₁ ec-[] N [ M′ ]} {CUT N′ M″} (red-ec (ec-APP₁ ec-[] _) M↦M′) (lem-APP-LAM M′⇓LAM-M″ N⇓N′)


lem-IF-TRUE : ∀ {g} → {M N N′ O : Term g}
                    → M ⇓ TRUE → N ⇓ N′
                    → IF M N O ⇓ N′
lem-IF-TRUE eval-TRUE                N⇓N′ = eval-red red-IF-TRUE N⇓N′
lem-IF-TRUE (eval-red M↦M′ M′⇓TRUE) N⇓N′ = eval-red (red-ec (ec-IF ec-[] _ _) M↦M′) (lem-IF-TRUE M′⇓TRUE N⇓N′)


lem-IF-FALSE : ∀ {g} → {M N O O′ : Term g}
                     → M ⇓ FALSE → O ⇓ O′
                     → IF M N O ⇓ O′
lem-IF-FALSE eval-FALSE                O⇓O′ = eval-red red-IF-FALSE O⇓O′
lem-IF-FALSE (eval-red M↦M′ M′⇓FALSE) O⇓O′ = eval-red (red-ec (ec-IF ec-[] _ _) M↦M′) (lem-IF-FALSE M′⇓FALSE O⇓O′)


sn : ∀ {M A} → ∙ ⊢ M ⦂ A → M ⇓
sn (var ())
sn (lam 𝒟)    = LAM _ , eval-LAM
sn (app 𝒟 ℰ)  with sn 𝒟 | sn ℰ
sn (app 𝒟 ℰ)  | M′ , M⇓M′ | N′ , N⇓N′ with val M⇓M′ | tp⇓ M⇓M′ 𝒟
sn (app 𝒟 ℰ)  | LAM M′ , M⇓LAM-M′ | N′ , N⇓N′ | val-LAM   | lam 𝒟′ = CUT N′ M′ , lem-APP-LAM M⇓LAM-M′ N⇓N′
sn (app 𝒟 ℰ)  | TRUE   , M⇓M′     | N′ , N⇓N′ | val-TRUE  | ()
sn (app 𝒟 ℰ)  | FALSE  , M⇓M′     | N′ , N⇓N′ | val-FALSE | ()
sn true       = TRUE , eval-TRUE
sn false      = FALSE , eval-FALSE
sn (if 𝒟 ℰ ℱ) with sn 𝒟 | sn ℰ | sn ℱ
sn (if 𝒟 ℰ ℱ) | M′ , M⇓M′ | N′ , N⇓N′ | O′ , O⇓O′ with val M⇓M′ | tp⇓ M⇓M′ 𝒟
sn (if 𝒟 ℰ ℱ) | LAM M′ , M⇓M′    | N′ , N⇓N′ | O′ , O⇓O′ | val-LAM   | ()
sn (if 𝒟 ℰ ℱ) | TRUE   , M⇓TRUE  | N′ , N⇓N′ | O′ , O⇓O′ | val-TRUE  | true  = N′ , lem-IF-TRUE M⇓TRUE N⇓N′
sn (if 𝒟 ℰ ℱ) | FALSE  , M⇓FALSE | N′ , N⇓N′ | O′ , O⇓O′ | val-FALSE | false = O′ , lem-IF-FALSE M⇓FALSE O⇓O′


--------------------------------------------------------------------------------
