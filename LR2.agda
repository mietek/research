{-# OPTIONS --allow-unsolved-metas #-}

module LR2 where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec
open import VecLemmas
open import AllVec
open import LR0
open import LR1


--------------------------------------------------------------------------------


-- `IsVal M` says that the term `M` is a value.
data IsVal {g} : Term g → Set
  where
    instance
      iv-LAM   : ∀ {M} → IsVal (LAM M)
      iv-TRUE  : IsVal TRUE
      iv-FALSE : IsVal FALSE


-- `Val g` is a well-scoped term together with the evidence that this term is a value.
-- record Val (g : Nat) : Set
--   where
--     constructor val
--     field
--       term   : Term g
--       {{iv}} : IsVal term


-- TODO
data AreVals {g} : ∀ {n} → Terms g n → Set
  where
    instance
      ∙   : AreVals ∙
      _,_ : ∀ {n M} → {τ : Terms g n}
                    → AreVals τ → IsVal M
                    → AreVals (τ , M)


-- TODO
-- record Vals (g n : Nat) : Set
--   where
--     constructor vals
--     field
--       terms  : Terms g n
--       {{av}} : AreVals terms


--------------------------------------------------------------------------------


-- `EvCx g` is a well-scoped call-by-value (CBV) evaluation context.
data EvCx (g : Nat) : Set
  where
    ec-hole    : EvCx g
    ec-fun-APP : EvCx g → Term g → EvCx g
    ec-APP-arg : (M : Term g) → EvCx g → {{_ : IsVal M}} → EvCx g
    ec-IF      : EvCx g → Term g → Term g → EvCx g


-- `E [ M ]` plugs the term `M` into the evaluation context `E`.
_[_] : ∀ {g} → EvCx g → Term g → Term g
ec-hole          [ M ] = M
ec-fun-APP E N   [ M ] = APP (E [ M ]) N
ec-APP-arg M E   [ N ] = APP M (E [ N ])
ec-IF      E N O [ M ] = IF (E [ M ]) N O


-- Values do not have evaluation contexts.
no-ec-val : ∀ {g} → {M M′ : Term g} → (E : EvCx g) → M ≡ E [ M′ ] → {{_ : IsVal M}}
                  → M ≡ M′
no-ec-val ec-hole          refl        = refl
no-ec-val (ec-fun-APP E N) refl {{()}}
no-ec-val (ec-APP-arg M E) refl {{()}}
no-ec-val (ec-IF E N O)    refl {{()}}


--------------------------------------------------------------------------------


-- `_↦_` is the CBV small-step reduction relation.
-- `M ↦ M′` says that the term `M` reduces in one step to the term `M′`.
infix 3 _↦_
data _↦_ {g} : Term g → Term g → Set
  where
    red-APP-LAM  : ∀ {M N} → {{_ : IsVal N}}
                           → APP (LAM M) N ↦ CUT N M
    red-IF-TRUE  : ∀ {N O} → IF TRUE N O ↦ N
    red-IF-FALSE : ∀ {N O} → IF FALSE N O ↦ O
    red-cong     : ∀ {M M′ E[M]} → (E : EvCx g) → M ↦ M′ → {{_ : E[M] ≡ E [ M ]}}
                                 → E[M] ↦ E [ M′ ]


-- If `M` reduces in one step to `M′`, then `APP M N` reduces in one step to `APP M′ N`.
red-fun-APP : ∀ {g} → {M M′ N : Term g}
                    → M ↦ M′
                    → APP M N ↦ APP M′ N
red-fun-APP M↦M′ = red-cong (ec-fun-APP ec-hole _) M↦M′


-- If `N` reduces in one step to `N′`, then `APP M N` reduces in one step to `APP M N′`.
red-APP-arg : ∀ {g} → {M N N′ : Term g}
                    → N ↦ N′ → {{_ : IsVal M}}
                    → APP M N ↦ APP M N′
red-APP-arg N↦N′ = red-cong (ec-APP-arg _ ec-hole) N↦N′


-- If `M` reduces in one step to `M′`, then `IF M N O` reduces in one step to `IF M′ N O`.
red-IF : ∀ {g} → {M M′ N O : Term g}
               → M ↦ M′
               → IF M N O ↦ IF M′ N O
red-IF M↦M′ = red-cong (ec-IF ec-hole _ _) M↦M′


-- Values do not reduce.
no-red-val : ∀ {g M′} → (M : Term g) → {{_ : IsVal M}}
                      → ¬ (M ↦ M′)
no-red-val (LAM M) {{iv-LAM}}   (red-cong E _         {{p}}) with no-ec-val E p
no-red-val (LAM M) {{iv-LAM}}   (red-cong E LAM-M↦M′ {{p}}) | refl = no-red-val (LAM M) LAM-M↦M′
no-red-val TRUE    {{iv-TRUE}}  (red-cong E _         {{p}}) with no-ec-val E p
no-red-val TRUE    {{iv-TRUE}}  (red-cong E TRUE↦M′  {{p}}) | refl = no-red-val TRUE TRUE↦M′
no-red-val FALSE   {{iv-FALSE}} (red-cong E _         {{p}}) with no-ec-val E p
no-red-val FALSE   {{iv-FALSE}} (red-cong E FALSE↦M′ {{p}}) | refl = no-red-val FALSE FALSE↦M′


-- `_↦_` is type-preserving.
mutual
  tp↦ : ∀ {g M M′ A} → {Γ : Types g}
                      → M ↦ M′ → Γ ⊢ M ⦂ A
                      → Γ ⊢ M′ ⦂ A
  tp↦ red-APP-LAM                 (app (lam 𝒟) ℰ) = cut ℰ 𝒟
  tp↦ red-IF-TRUE                 (if 𝒟 ℰ ℱ)      = ℰ
  tp↦ red-IF-FALSE                (if 𝒟 ℰ ℱ)      = ℱ
  tp↦ (red-cong E M↦M′ {{refl}}) 𝒟               = tp[↦] E M↦M′ 𝒟

  tp[↦] : ∀ {g M M′ A} → {Γ : Types g}
                        → (E : EvCx g) → M ↦ M′ → Γ ⊢ E [ M ] ⦂ A
                        → Γ ⊢ E [ M′ ] ⦂ A
  tp[↦] ec-hole          M↦M′ 𝒟          = tp↦ M↦M′ 𝒟
  tp[↦] (ec-fun-APP E N) M↦M′ (app 𝒟 ℰ)  = app (tp[↦] E M↦M′ 𝒟) ℰ
  tp[↦] (ec-APP-arg N E) M↦M′ (app 𝒟 ℰ)  = app 𝒟 (tp[↦] E M↦M′ ℰ)
  tp[↦] (ec-IF E N O)    M↦M′ (if 𝒟 ℰ ℱ) = if (tp[↦] E M↦M′ 𝒟) ℰ ℱ


--------------------------------------------------------------------------------


-- `_⤅_` is the CBV big-step reduction relation.
-- `_⤅_` is also the reflexive and transitive closure of `_↦_`.
-- `M ⤅ M′` says that the term `M` reduces to the term `M′`, in zero or more steps.
infix 3 _⤅_
data _⤅_ {g} : Term g → Term g → Set
  where
    done : ∀ {M} → M ⤅ M
    step : ∀ {M M″ M′} → M ↦ M″ → M″ ⤅ M′
                       → M ⤅ M′


-- If `M` reduces to `M′`, then `APP M N` reduces to `APP M′ N`.
step-fun-APP : ∀ {g} → {M M′ N : Term g}
                     → M ⤅ M′
                     → APP M N ⤅ APP M′ N
step-fun-APP done               = done
step-fun-APP (step M↦M″ M⤅M′) = step (red-fun-APP M↦M″) (step-fun-APP M⤅M′)


-- If `N` reduces to `N′`, then `APP M N` reduces to `APP M N′`.
step-APP-arg : ∀ {g} → {M N N′ : Term g}
                     → N ⤅ N′ → {{_ : IsVal M}}
                     → APP M N ⤅ APP M N′
step-APP-arg done               = done
step-APP-arg (step N↦N″ N⤅N′) = step (red-APP-arg N↦N″) (step-APP-arg N⤅N′)


-- If `M` reduces to `M′`, then `IF M N O` reduces to `IF M′ N O`.
step-IF : ∀ {g} → {M M′ N O : Term g}
                → M ⤅ M′
                → IF M N O ⤅ IF M′ N O
step-IF done                = done
step-IF (step M↦M″ M″⤅M′) = step (red-IF M↦M″) (step-IF M″⤅M′)


-- `_⤅_` is transitive.
steps : ∀ {g} → {M M″ M′ : Term g}
              → M ⤅ M″ → M″ ⤅ M′
              → M ⤅ M′
steps done                M⤅M′  = M⤅M′
steps (step M↦M‴ M‴⤅M″) M″⤅M′ = step M↦M‴ (steps M‴⤅M″ M″⤅M′)


-- If `M` reduces to `TRUE`, and `N` reduces to `N′`, then `IF M N O` reduces to `N′`.
step-IF-TRUE : ∀ {g} → {M N N′ O : Term g}
                     → M ⤅ TRUE → N ⤅ N′
                     → IF M N O ⤅ N′
step-IF-TRUE M⤅TRUE N⤅N′ = steps (step-IF M⤅TRUE) (step red-IF-TRUE N⤅N′)


-- If `M` reduces to `FALSE`, and `O` reduces to `O′`, then `IF M N O` reduces to `O′`.
step-IF-FALSE : ∀ {g} → {M N O O′ : Term g}
                      → M ⤅ FALSE → O ⤅ O′
                      → IF M N O ⤅ O′
step-IF-FALSE M⤅FALSE O⤅O′ = steps (step-IF M⤅FALSE) (step red-IF-FALSE O⤅O′)


-- `_⤅_` is type-preserving.
tp⤅ : ∀ {g M M′ A} → {Γ : Types g}
                    → M ⤅ M′ → Γ ⊢ M ⦂ A
                    → Γ ⊢ M′ ⦂ A
tp⤅ done                𝒟 = 𝒟
tp⤅ (step M↦M″ M″⤅M′) 𝒟 = tp⤅ (M″⤅M′) (tp↦ M↦M″ 𝒟)


--------------------------------------------------------------------------------


-- `_⇓_` is the CBV evaluation relation.
-- `M ⇓ M′` says that the term `M` evaluates to the value `M′`.
infix 3 _⇓_
_⇓_ : ∀ {g} → Term g → Term g → Set
M ⇓ M′ = IsVal M′ × M ⤅ M′


-- `M ⇓` says that the evaluation of the term `M` terminates.
_⇓ : ∀ {g} → Term g → Set
M ⇓ = Σ (Term _) (\ M′ → M ⇓ M′)


-- If `N` terminates, then `APP M N` terminates.
halt-APP-arg : ∀ {g} → {M N : Term g}
                     → N ⇓ → {{_ : IsVal M}}
                     → APP M N ⇓
halt-APP-arg {M = M} (N′ , (iv-N′ , N⤅N′)) = APP M N′ , ({!!} , step-APP-arg N⤅N′)


-- If `M` reduces to `TRUE`, and `N` terminates, then `IF M N O` terminates.
halt-IF-TRUE : ∀ {g} → {M N O : Term g}
                     → M ⤅ TRUE → N ⇓
                     → IF M N O ⇓
halt-IF-TRUE M⤅TRUE (N′ , (iv-N′ , N⤅N′)) = N′ , (iv-N′ , step-IF-TRUE M⤅TRUE N⤅N′)


-- If `M` reduces to `FALSE`, and `O` terminates, then `IF M N O` terminates.
halt-IF-FALSE : ∀ {g} → {M N O : Term g}
                      → M ⤅ FALSE → O ⇓
                      → IF M N O ⇓
halt-IF-FALSE M⤅FALSE (O′ , (iv-O′ , O⤅O′)) = O′ , (iv-O′ , step-IF-FALSE M⤅FALSE O⤅O′)


--------------------------------------------------------------------------------


private
  module Impossible
    where
      -- TODO
      halt : ∀ {M A} → ∙ ⊢ M ⦂ A
                     → M ⇓
      halt (var ())
      halt (lam 𝒟)    = LAM _ , (iv-LAM , done)
      halt (app 𝒟 ℰ)  = {!!}
      halt true       = TRUE , (iv-TRUE , done)
      halt false      = FALSE , (iv-FALSE , done)
      halt (if 𝒟 ℰ ℱ) with halt 𝒟
      halt (if 𝒟 ℰ ℱ) | M′      , (iv-M′    , M⤅M′)     with tp⤅ M⤅M′ 𝒟
      halt (if 𝒟 ℰ ℱ) | LAM M″  , (iv-LAM   , M⤅LAM-M″) | ()
      halt (if 𝒟 ℰ ℱ) | TRUE    , (iv-TRUE  , M⤅TRUE)   | true  = halt-IF-TRUE M⤅TRUE (halt ℰ)
      halt (if 𝒟 ℰ ℱ) | FALSE   , (iv-FALSE , M⤅FALSE)  | false = halt-IF-FALSE M⤅FALSE (halt ℱ)


--------------------------------------------------------------------------------
