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


-- `Val M` says that the term `M` is a value.
data Val {g} : Term g → Set
  where
    instance
      VLAM   : ∀ {M} → Val (LAM M)
      VTRUE  : Val TRUE
      VFALSE : Val FALSE


-- `Vals τ` says that all terms `τ` are values.
data Vals {g} : ∀ {n} → Terms g n → Set
  where
    instance
      ∙   : Vals ∙
      _,_ : ∀ {n M} → {τ : Terms g n}
                    → Vals τ → Val M
                    → Vals (τ , M)


--------------------------------------------------------------------------------


-- `_↦_` is the CBV computation relation.
infix 3 _↦_
data _↦_ {g} : Term g → Term g → Set
  where
    red-APP-LAM  : ∀ {M N} → {{_ : Val N}} → APP (LAM M) N ↦ CUT N M
    red-IF-TRUE  : ∀ {N O} → IF TRUE N O ↦ N
    red-IF-FALSE : ∀ {N O} → IF FALSE N O ↦ O


-- Computation is deterministic.
det↦ : ∀ {g} → {M M′₁ M′₂ : Term g}
              → M ↦ M′₁ → M ↦ M′₂
              → M′₁ ≡ M′₂
det↦ red-APP-LAM  red-APP-LAM  = refl
det↦ red-IF-TRUE  red-IF-TRUE  = refl
det↦ red-IF-FALSE red-IF-FALSE = refl


-- Computation is type-preserving.
tp↦ : ∀ {g M M′ A} → {Γ : Types g}
                    → M ↦ M′ → Γ ⊢ M ⦂ A
                    → Γ ⊢ M′ ⦂ A
tp↦ red-APP-LAM  (app (lam 𝒟) ℰ) = cut ℰ 𝒟
tp↦ red-IF-TRUE  (if 𝒟 ℰ ℱ)      = ℰ
tp↦ red-IF-FALSE (if 𝒟 ℰ ℱ)      = ℱ


--------------------------------------------------------------------------------


-- `_⤇_` is the CBV small-step reduction relation.
infix 3 _⤇_
data _⤇_ {g} : Term g → Term g → Set
  where
    do : ∀ {M M′} → M ↦ M′
                  → M ⤇ M′

    cong-APP : ∀ {M M′ N} → M ⤇ M′
                           → APP M N ⤇ APP M′ N

    cong-APP-LAM : ∀ {M N N′} → N ⤇ N′
                              → APP (LAM M) N ⤇ APP (LAM M) N′

    cong-IF : ∀ {M M′ N O} → M ⤇ M′
                           → IF M N O ⤇ IF M′ N O


-- Computation determines small-step reduction.
do-det⤇ : ∀ {g} → {M M′₁ M′₂ : Term g}
                 → M ↦ M′₁ → M ⤇ M′₂
                 → M′₁ ≡ M′₂
do-det⤇ M↦M′₁                   (do M↦M′₂) = det↦ M↦M′₁ M↦M′₂
do-det⤇ red-APP-LAM              (cong-APP (do ()))
do-det⤇ (red-APP-LAM {{VLAM}})   (cong-APP-LAM (do ()))
do-det⤇ (red-APP-LAM {{VTRUE}})  (cong-APP-LAM (do ()))
do-det⤇ (red-APP-LAM {{VFALSE}}) (cong-APP-LAM (do ()))
do-det⤇ red-IF-TRUE              (cong-IF (do ()))
do-det⤇ red-IF-FALSE             (cong-IF (do ()))


-- Small-step reduction is deterministic.
det⤇ : ∀ {g} → {M M′₁ M′₂ : Term g}
              → M ⤇ M′₁ → M ⤇ M′₂
              → M′₁ ≡ M′₂
det⤇ (do M↦M′₁)           M⤇M′₂                = do-det⤇ M↦M′₁ M⤇M′₂
det⤇ (cong-APP M⤇M′₁)     (do M↦M′₂)           = do-det⤇ M↦M′₂ (cong-APP M⤇M′₁) ⁻¹
det⤇ (cong-APP-LAM N⤇N′₁) (do M↦M′₂)           = do-det⤇ M↦M′₂ (cong-APP-LAM N⤇N′₁) ⁻¹
det⤇ (cong-IF M⤇M′₁)      (do M↦M′₂)           = do-det⤇ M↦M′₂ (cong-IF M⤇M′₁) ⁻¹
det⤇ (cong-APP M⤇M′₁)     (cong-APP M⤇M′₂)     = (\ M′ → APP M′ _) & det⤇ M⤇M′₁ M⤇M′₂
det⤇ (cong-APP (do ()))    (cong-APP-LAM _)
det⤇ (cong-APP-LAM _)      (cong-APP (do ()))
det⤇ (cong-APP-LAM N⤇N′₁) (cong-APP-LAM N⤇N′₂) = (\ N′ → APP _ N′) & det⤇ N⤇N′₁ N⤇N′₂
det⤇ (cong-IF M⤇M′₁)      (cong-IF M⤇M′₂)      = (\ M′ → IF M′ _ _) & det⤇ M⤇M′₁ M⤇M′₂


-- Small-step reduction is type-preserving.
tp⤇ : ∀ {g M M′ A} → {Γ : Types g}
                    → M ⤇ M′ → Γ ⊢ M ⦂ A
                    → Γ ⊢ M′ ⦂ A
tp⤇ (do M↦M′)           𝒟          = tp↦ M↦M′ 𝒟
tp⤇ (cong-APP M⤇M′)     (app 𝒟 ℰ)  = app (tp⤇ M⤇M′ 𝒟) ℰ
tp⤇ (cong-APP-LAM M⤇M′) (app 𝒟 ℰ)  = app 𝒟 (tp⤇ M⤇M′ ℰ)
tp⤇ (cong-IF M⤇M′)      (if 𝒟 ℰ ℱ) = if (tp⤇ M⤇M′ 𝒟) ℰ ℱ


--------------------------------------------------------------------------------


-- `_⤇*_` is the iterated small-step reduction relation.
infix 3 _⤇*_
data _⤇*_ {g} : Term g → Term g → Set
  where
    -- Iterated small-step reduction is reflexive.
    done : ∀ {M} → M ⤇* M

    -- Small-step reduction IN REVERSE preserves iterated small-step reduction.
    step : ∀ {M M′ M″} → M ⤇ M′ → M′ ⤇* M″
                       → M ⤇* M″


-- Iterated small-step reduction is transitive.
-- Iterated small-step reduction IN REVERSE preserves iterated small-step reduction.
steps : ∀ {g} → {M M′ M″ : Term g}
              → M ⤇* M′ → M′ ⤇* M″
              → M ⤇* M″
steps done                 M⤇*M″  = M⤇*M″
steps (step M⤇M‴ M‴⤇*M′) M′⤇*M″ = step M⤇M‴ (steps M‴⤇*M′ M′⤇*M″)


-- When reducing down to a value, the initial small step determines the subsequent small steps.
-- Small-step reduction preserves iterated small-step reduction down to a value.
unstep : ∀ {g} → {M M′ M″ : Term g}
               → M ⤇ M′ → M ⤇* M″ → {{_ : Val M″}}
               → M′ ⤇* M″
unstep M⤇M′₁  (step M⤇M′₂ M′₂⤇*M″) with det⤇ M⤇M′₁ M⤇M′₂
unstep M⤇M′   (step _      M′⤇*M″)  | refl = M′⤇*M″
unstep (do ()) done {{VLAM}}
unstep (do ()) done {{VTRUE}}
unstep (do ()) done {{VFALSE}}


-- When reducing down to a value, iterated small-step reduction is deterministic.
det⤇* : ∀ {g} → {M M′₁ M′₂ : Term g}
               → M ⤇* M′₁ → {{_ : Val M′₁}} → M ⤇* M′₂ → {{_ : Val M′₂}}
               → M′₁ ≡ M′₂
det⤇* done                    done    = refl
det⤇* (step M⤇M″₁ M″₁⤇*M′₁) M⤇*M′₂ = det⤇* M″₁⤇*M′₁ (unstep M⤇M″₁ M⤇*M′₂)
det⤇* done {{VLAM}}           (step (do ()) _)
det⤇* done {{VTRUE}}          (step (do ()) _)
det⤇* done {{VFALSE}}         (step (do ()) _)


-- Iterated small-step reduction is type-preserving.
tp⤇* : ∀ {g M M′ A} → {Γ : Types g}
                     → M ⤇* M′ → Γ ⊢ M ⦂ A
                     → Γ ⊢ M′ ⦂ A
tp⤇* done                 𝒟 = 𝒟
tp⤇* (step M⤇M″ M″⤇*M′) 𝒟 = tp⤇* M″⤇*M′ (tp⤇ M⤇M″ 𝒟)


-- If `M` reduces to `M′`, then `APP M N` reduces to `APP M′ N`.
congs-APP : ∀ {g} → {M M′ N : Term g}
                  → M ⤇* M′
                  → APP M N ⤇* APP M′ N
congs-APP done                 = done
congs-APP (step M⤇M″ M″⤇*M′) = step (cong-APP M⤇M″) (congs-APP M″⤇*M′)


-- If `N` reduces to `N′`, then `APP (LAM M) N` reduces to `APP (LAM M) N′`.
congs-APP-LAM : ∀ {g} → {M : Term (suc g)} {N N′ : Term g}
                      → N ⤇* N′
                      → APP (LAM M) N ⤇* APP (LAM M) N′
congs-APP-LAM done                 = done
congs-APP-LAM (step M⤇M″ M″⤇*M′) = step (cong-APP-LAM M⤇M″) (congs-APP-LAM M″⤇*M′)


-- If `M` reduces to `M′`, then `IF M N O` reduces to `IF M′ N O`.
congs-IF : ∀ {g} → {M M′ N O : Term g}
                 → M ⤇* M′
                 → IF M N O ⤇* IF M′ N O
congs-IF done                 = done
congs-IF (step M⤇M″ M″⤇*M′) = step (cong-IF M⤇M″) (congs-IF M″⤇*M′)


-- If `M` reduces to `TRUE` and `N` reduces to `N′`, then `IF M N O` reduces to `N′`.
congs-IF-TRUE : ∀ {g} → {M N N′ O : Term g}
                      → M ⤇* TRUE → N ⤇* N′
                      → IF M N O ⤇* N′
congs-IF-TRUE M⤇*TRUE N⤇*N′ = steps (congs-IF M⤇*TRUE) (step (do red-IF-TRUE) N⤇*N′)


-- If `M` reduces to `FALSE` and `O` reduces to `O′`, then `IF M N O` reduces to `O′`.
congs-IF-FALSE : ∀ {g} → {M N O O′ : Term g}
                       → M ⤇* FALSE → O ⤇* O′
                       → IF M N O ⤇* O′
congs-IF-FALSE M⤇*FALSE N⤇*N′ = steps (congs-IF M⤇*FALSE) (step (do red-IF-FALSE) N⤇*N′)


--------------------------------------------------------------------------------


-- `_⇓_` is the big-step reduction relation.
infix 3 _⇓_
_⇓_ : ∀ {g} → Term g → Term g → Set
M ⇓ M′ = M ⤇* M′ × Val M′


-- A big step can be extended with an initial small step.
-- Small-step reduction IN REVERSE preserves big-step reduction.
big-step : ∀ {g} → {M M′ M″ : Term g}
                 → M ⤇ M′ → M′ ⇓ M″
                 → M ⇓ M″
big-step M⤇M′ (M′⤇*M″ , VM″) = step M⤇M′ M′⤇*M″ , VM″


-- The initial small step determines the subsequent big step.
-- Small-step reduction preserves big-step reduction.
big-unstep : ∀ {g} → {M M′ M″ : Term g}
                   → M ⤇ M′ → M ⇓ M″
                   → M′ ⇓ M″
big-unstep M⤇M′ (M′⤇*M″ , VM″) = unstep M⤇M′ M′⤇*M″ {{VM″}} , VM″


-- Big-step reduction is deterministic.
det⇓ : ∀ {g} → {M M′₁ M′₂ : Term g}
             → M ⇓ M′₁ → M ⇓ M′₂
             → M′₁ ≡ M′₂
det⇓ (M⤇*M′₁ , VM′₁) (M⤇*M′₂ , VM′₂) = det⤇* M⤇*M′₁ {{VM′₁}} M⤇*M′₂ {{VM′₂}}


-- If `M` reduces to `TRUE` and `N` reduces to `N′`, then `IF M N O` reduces to `N′`.
big-cong-IF-TRUE : ∀ {g} → {M N N′ O : Term g}
                         → M ⤇* TRUE → N ⇓ N′
                         → IF M N O ⇓ N′
big-cong-IF-TRUE M⤇*TRUE (N⤇*N′ , VN′) = congs-IF-TRUE M⤇*TRUE N⤇*N′ , VN′


-- If `M` reduces to `FALSE` and `O` reduces to `O′`, then `IF M N O` reduces to `O′`.
big-cong-IF-FALSE : ∀ {g} → {M N O O′ : Term g}
                          → M ⤇* FALSE → O ⇓ O′
                          → IF M N O ⇓ O′
big-cong-IF-FALSE M⤇*FALSE (O⤇*O′ , VO′) = congs-IF-FALSE M⤇*FALSE O⤇*O′ , VO′


--------------------------------------------------------------------------------


-- `_⇓` is the CBV termination relation.
_⇓ : ∀ {g} → Term g → Set
M ⇓ = Σ (Term _) (\ M′ → M ⇓ M′)


-- Small-step reduction IN REVERSE preserves termination.
-- Reversed small-step reduction is halt-preserving.
hpr⤇ : ∀ {g} → {M M′ : Term g}
              → M ⤇ M′ → M′ ⇓
              → M ⇓
hpr⤇ M⤇M′ (M″ , M′⇓M″) = M″ , big-step M⤇M′ M′⇓M″


-- Small-step reduction preserves termination.
-- Small-step reduction is halt-preserving.
hp⤇ : ∀ {g} → {M M′ : Term g}
             → M ⤇ M′ → M ⇓
             → M′ ⇓
hp⤇ M⤇M′ (M″ , M′⇓M″) = M″ , big-unstep M⤇M′ M′⇓M″


-- If `M` reduces to `TRUE` and `N` terminates, then `IF M N O` terminates.
halt-IF-TRUE : ∀ {g} → {M N O : Term g}
                     → M ⤇* TRUE → N ⇓
                     → IF M N O ⇓
halt-IF-TRUE M⤇*TRUE (N′ , N⇓N′) = N′ , big-cong-IF-TRUE M⤇*TRUE N⇓N′


-- If `M` reduces to `FALSE` and `O` terminates, then `IF M N O` terminates.
halt-IF-FALSE : ∀ {g} → {M N O : Term g}
                      → M ⤇* FALSE → O ⇓
                      → IF M N O ⇓
halt-IF-FALSE M⤇*FALSE (O′ , O⇓O′) = O′ , big-cong-IF-FALSE M⤇*FALSE O⇓O′


-- Every well-typed term terminates.
-- Impossible without a stronger induction hypothesis.
{-
halt : ∀ {M A} → ∙ ⊢ M ⦂ A
               → M ⇓
halt (var ())
halt (lam 𝒟)    = LAM _ , done , VLAM
halt (app 𝒟 ℰ)  = {!!}
halt true       = TRUE  , done , VTRUE
halt false      = FALSE , done , VFALSE
halt (if 𝒟 ℰ ℱ) with halt 𝒟
halt (if 𝒟 ℰ ℱ) | M′    , M⤇*M′    , VM′    with tp⤇* M⤇*M′ 𝒟
halt (if 𝒟 ℰ ℱ) | LAM _ , _         , VLAM   | ()
halt (if 𝒟 ℰ ℱ) | TRUE  , M⤇*TRUE  , VTRUE  | true  = halt-IF-TRUE M⤇*TRUE (halt ℰ)
halt (if 𝒟 ℰ ℱ) | FALSE , M⤇*FALSE , VFALSE | false = halt-IF-FALSE M⤇*FALSE (halt ℱ)
-}


--------------------------------------------------------------------------------
