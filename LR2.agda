module LR2 where

open import Prelude
open import Category
open import Fin
open import FinLemmas
-- open import List
-- open import ListLemmas
open import Vec
open import VecLemmas
open import AllVec
open import LR1


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
    ec-IF   : EC g → Term g → Term g → EC g
    ec-APP₁ : EC g → Term g → EC g
    ec-APP₂ : (N : Term g) → EC g → {{_ : Val N}} → EC g

_[_] : ∀ {g} → EC g → Term g → Term g
ec-[]         [ M ] = M
ec-IF   E N O [ M ] = IF (E [ M ]) N O
ec-APP₁ E N   [ M ] = APP (E [ M ]) N
ec-APP₂ N E   [ M ] = APP N (E [ M ])

infix 3 _↦_
data _↦_ {g} : Term g → Term g → Set
  where
    red-IF-TRUE  : ∀ {M N} → IF TRUE M N ↦ M
    red-IF-FALSE : ∀ {M N} → IF FALSE M N ↦ N
    red-APP-LAM  : ∀ {M N} → APP (LAM M) N ↦ CUT N M
    red-ec       : ∀ {M M′} → (E : EC g) → M ↦ M′ → E [ M ] ↦ E [ M′ ]

infix 3 _⤅_
data _⤅_ {g} : Term g → (M′ : Term g) → Set
  where
    eval-TRUE  : TRUE ⤅ TRUE
    eval-FALSE : FALSE ⤅ FALSE
    eval-LAM   : ∀ {M} → LAM M ⤅ LAM M
    eval-red   : ∀ {M M′ M″} → M ↦ M′ → M′ ⤅ M″ → M ⤅ M″

val : ∀ {g} → {M M′ : Term g} → M ⤅ M′ → Val M′
val eval-TRUE               = val-TRUE
val eval-FALSE              = val-FALSE
val eval-LAM                = val-LAM
val (eval-red M⤅M′ M′⤅M″) = val M′⤅M″

infix 3 _⇓_
_⇓_ : ∀ {g} → Term g → Term g → Set
M ⇓ M′ = M ⤅ M′

_⇓ : ∀ {g} → (M : Term g) → Set
M ⇓ = Σ (Term _) (\ M′ → M ⇓ M′)

mutual
  tp↦ : ∀ {g M M′ A} → {Γ : Types g}
                      → M ↦ M′ → Γ ⊢ M ⦂ A
                      → Γ ⊢ M′ ⦂ A
  tp↦ red-IF-TRUE      (if 𝒟 ℰ ℱ)      = ℰ
  tp↦ red-IF-FALSE     (if 𝒟 ℰ ℱ)      = ℱ
  tp↦ red-APP-LAM      (app (lam 𝒟) ℰ) = cut ℰ 𝒟
  tp↦ (red-ec E M↦M′) 𝒟               = plug E M↦M′ 𝒟

  plug : ∀ {g M M′ A} → {Γ : Types g}
                      → (E : EC g) → M ↦ M′ → Γ ⊢ E [ M ] ⦂ A
                      → Γ ⊢ E [ M′ ] ⦂ A
  plug ec-[]         M↦M′ 𝒟          = tp↦ M↦M′ 𝒟
  plug (ec-IF E N O) M↦M′ (if 𝒟 ℰ ℱ) = if (plug E M↦M′ 𝒟) ℰ ℱ
  plug (ec-APP₁ E N) M↦M′ (app 𝒟 ℰ)  = app (plug E M↦M′ 𝒟) ℰ
  plug (ec-APP₂ N E) M↦M′ (app 𝒟 ℰ)  = app 𝒟 (plug E M↦M′ ℰ)

tp⇓ : ∀ {g M M′ A} → {Γ : Types g}
                   → M ⇓ M′ → Γ ⊢ M ⦂ A
                   → Γ ⊢ M′ ⦂ A
tp⇓ eval-TRUE              𝒟 = 𝒟
tp⇓ eval-FALSE             𝒟 = 𝒟
tp⇓ eval-LAM               𝒟 = 𝒟
tp⇓ (eval-red M↦M′ M′⇓M″) 𝒟 = tp⇓ M′⇓M″ (tp↦ M↦M′ 𝒟)

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
sn (lam 𝒟)    = {!!}
sn (app 𝒟 ℰ)  = {!!}
sn true       = TRUE , eval-TRUE
sn false      = FALSE , eval-FALSE
sn (if 𝒟 ℰ ℱ) with sn 𝒟 | sn ℰ | sn ℱ
sn (if 𝒟 ℰ ℱ) | M′ , M⇓M′ | N′ , N⇓N′ | O′ , O⇓O′ with val M⇓M′ | tp⇓ M⇓M′ 𝒟
sn (if 𝒟 ℰ ℱ) | LAM M′ , M⇓M′    | N′ , N⇓N′ | O′ , O⇓O′ | val-LAM   | ()
sn (if 𝒟 ℰ ℱ) | TRUE   , M⇓TRUE  | N′ , N⇓N′ | O′ , O⇓O′ | val-TRUE  | true  = N′ , lem-IF-TRUE M⇓TRUE N⇓N′
sn (if 𝒟 ℰ ℱ) | FALSE  , M⇓FALSE | N′ , N⇓N′ | O′ , O⇓O′ | val-FALSE | false = O′ , lem-IF-FALSE M⇓FALSE O⇓O′
