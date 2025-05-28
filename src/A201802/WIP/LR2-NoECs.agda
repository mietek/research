{-# OPTIONS --rewriting #-}

module A201802.WIP.LR2-NoECs where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.FinLemmas
open import A201801.Vec
open import A201801.VecLemmas
open import A201801.AllVec

open import A201802.LR0
open import A201802.LR1


--------------------------------------------------------------------------------


-- `Val M` says that the term `M` is a value.
data Val {g} : Term g → Set
  where
    instance
      VLAM   : ∀ {M} → Val (LAM M)
      VTRUE  : Val TRUE
      VFALSE : Val FALSE


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
    red       : ∀ {M M′} → M ↦ M′
                         → M ⤇ M′
    cong-APP₁ : ∀ {M M′ N} → M ⤇ M′
                           → APP M N ⤇ APP M′ N
    cong-APP₂ : ∀ {M N N′} → N ⤇ N′
                           → APP (LAM M) N ⤇ APP (LAM M) N′
    cong-IF   : ∀ {M M′ N O} → M ⤇ M′
                             → IF M N O ⤇ IF M′ N O


-- Computation determines small-step reduction.
red-det⤇ : ∀ {g} → {M M′₁ M′₂ : Term g}
                  → M ↦ M′₁ → M ⤇ M′₂
                  → M′₁ ≡ M′₂
red-det⤇ M↦M′₁                   (red M↦M′₂) = det↦ M↦M′₁ M↦M′₂
red-det⤇ red-APP-LAM              (cong-APP₁ (red ()))
red-det⤇ (red-APP-LAM {{VLAM}})   (cong-APP₂ (red ()))
red-det⤇ (red-APP-LAM {{VTRUE}})  (cong-APP₂ (red ()))
red-det⤇ (red-APP-LAM {{VFALSE}}) (cong-APP₂ (red ()))
red-det⤇ red-IF-TRUE              (cong-IF (red ()))
red-det⤇ red-IF-FALSE             (cong-IF (red ()))


-- Small-step reduction is deterministic.
det⤇ : ∀ {g} → {M M′₁ M′₂ : Term g}
              → M ⤇ M′₁ → M ⤇ M′₂
              → M′₁ ≡ M′₂
det⤇ (red M↦M′₁)         M⤇M′₂               = red-det⤇ M↦M′₁ M⤇M′₂
det⤇ (cong-APP₁ M⤇M′₁)   (red M↦M′₂)         = red-det⤇ M↦M′₂ (cong-APP₁ M⤇M′₁) ⁻¹
det⤇ (cong-APP₂ N⤇N′₁)   (red M↦M′₂)         = red-det⤇ M↦M′₂ (cong-APP₂ N⤇N′₁) ⁻¹
det⤇ (cong-IF M⤇M′₁)     (red M↦M′₂)         = red-det⤇ M↦M′₂ (cong-IF M⤇M′₁) ⁻¹
det⤇ (cong-APP₁ M⤇M′₁)   (cong-APP₁ M⤇M′₂)   = (\ M′ → APP M′ _) & det⤇ M⤇M′₁ M⤇M′₂
det⤇ (cong-APP₁ (red ())) (cong-APP₂ _)
det⤇ (cong-APP₂ _)        (cong-APP₁ (red ()))
det⤇ (cong-APP₂ N⤇N′₁)   (cong-APP₂ N⤇N′₂)   = (\ N′ → APP _ N′) & det⤇ N⤇N′₁ N⤇N′₂
det⤇ (cong-IF M⤇M′₁)     (cong-IF M⤇M′₂)     = (\ M′ → IF M′ _ _) & det⤇ M⤇M′₁ M⤇M′₂


-- Small-step reduction is type-preserving.
tp⤇ : ∀ {g M M′ A} → {Γ : Types g}
                    → M ⤇ M′ → Γ ⊢ M ⦂ A
                    → Γ ⊢ M′ ⦂ A
tp⤇ (red M↦M′)       𝒟          = tp↦ M↦M′ 𝒟
tp⤇ (cong-APP₁ M⤇M′) (app 𝒟 ℰ)  = app (tp⤇ M⤇M′ 𝒟) ℰ
tp⤇ (cong-APP₂ M⤇M′) (app 𝒟 ℰ)  = app 𝒟 (tp⤇ M⤇M′ ℰ)
tp⤇ (cong-IF M⤇M′)   (if 𝒟 ℰ ℱ) = if (tp⤇ M⤇M′ 𝒟) ℰ ℱ


--------------------------------------------------------------------------------


-- `_⤇*_` is the iterated small-step reduction relation.
infix 3 _⤇*_
data _⤇*_ {g} : Term g → Term g → Set
  where
    done : ∀ {M} → M ⤇* M
    step : ∀ {M M′ M″} → M ⤇ M″ → M″ ⤇* M′
                       → M ⤇* M′


-- Iterated small-step reduction is transitive.
steps : ∀ {g} → {M M′ M″ : Term g}
              → M ⤇* M″ → M″ ⤇* M′
              → M ⤇* M′
steps done                 M⤇*M′  = M⤇*M′
steps (step M⤇M‴ M‴⤇*M″) M″⤇*M′ = step M⤇M‴ (steps M‴⤇*M″ M″⤇*M′)


-- When reducing down to a value, the initial small step determines the subsequent small steps.
rev-step : ∀ {g} → {M M′ M″ : Term g}
                 → M ⤇ M″ → M ⤇* M′ → {{_ : Val M′}}
                 → M″ ⤇* M′
rev-step M⤇M″₁   (step M⤇M″₂ M″₂⤇*M′) with det⤇ M⤇M″₁ M⤇M″₂
rev-step M⤇M″    (step _      M″⤇*M′)  | refl = M″⤇*M′
rev-step (red ()) done {{VLAM}}
rev-step (red ()) done {{VTRUE}}
rev-step (red ()) done {{VFALSE}}


-- When reducing down to a value, iterated small-step reduction is deterministic.
det⤇* : ∀ {g} → {M M′₁ M′₂ : Term g}
               → M ⤇* M′₁ → {{_ : Val M′₁}} → M ⤇* M′₂ → {{_ : Val M′₂}}
               → M′₁ ≡ M′₂
det⤇* done                    done    = refl
det⤇* (step M⤇M″₁ M″₁⤇*M′₁) M⤇*M′₂ = det⤇* M″₁⤇*M′₁ (rev-step M⤇M″₁ M⤇*M′₂)
det⤇* done {{VLAM}}           (step (red ()) _)
det⤇* done {{VTRUE}}          (step (red ()) _)
det⤇* done {{VFALSE}}         (step (red ()) _)


-- Iterated small-step reduction is type-preserving.
tp⤇* : ∀ {g M M′ A} → {Γ : Types g}
                     → M ⤇* M′ → Γ ⊢ M ⦂ A
                     → Γ ⊢ M′ ⦂ A
tp⤇* done                 𝒟 = 𝒟
tp⤇* (step M⤇M″ M″⤇*M′) 𝒟 = tp⤇* M″⤇*M′ (tp⤇ M⤇M″ 𝒟)


-- If `M` reduces to `M′`, then `APP M N` reduces to `APP M′ N`.
step-APP₁ : ∀ {g} → {M M′ N : Term g}
                  → M ⤇* M′
                  → APP M N ⤇* APP M′ N
step-APP₁ done                 = done
step-APP₁ (step M⤇M″ M″⤇*M′) = step (cong-APP₁ M⤇M″) (step-APP₁ M″⤇*M′)


-- If `N` reduces to `N′`, then `APP (LAM M) N` reduces to `APP (LAM M) N′`.
step-APP₂ : ∀ {g} → {M : Term (suc g)} {N N′ : Term g}
                  → N ⤇* N′
                  → APP (LAM M) N ⤇* APP (LAM M) N′
step-APP₂ done                 = done
step-APP₂ (step M⤇M″ M″⤇*M′) = step (cong-APP₂ M⤇M″) (step-APP₂ M″⤇*M′)


-- If `M` reduces to `M′`, then `IF M N O` reduces to `IF M′ N O`.
step-IF : ∀ {g} → {M M′ N O : Term g}
                → M ⤇* M′
                → IF M N O ⤇* IF M′ N O
step-IF done                 = done
step-IF (step M⤇M″ M″⤇*M′) = step (cong-IF M⤇M″) (step-IF M″⤇*M′)


-- If `M` reduces to `TRUE` and `N` reduces to `N′`, then `IF M N O` reduces to `N′`.
step-IF-TRUE : ∀ {g} → {M N N′ O : Term g}
                     → M ⤇* TRUE → N ⤇* N′
                     → IF M N O ⤇* N′
step-IF-TRUE M⤇*TRUE N⤇*N′ = steps (step-IF M⤇*TRUE) (step (red red-IF-TRUE) N⤇*N′)


-- If `M` reduces to `FALSE` and `O` reduces to `O′`, then `IF M N O` reduces to `O′`.
step-IF-FALSE : ∀ {g} → {M N O O′ : Term g}
                      → M ⤇* FALSE → O ⤇* O′
                      → IF M N O ⤇* O′
step-IF-FALSE M⤇*FALSE N⤇*N′ = steps (step-IF M⤇*FALSE) (step (red red-IF-FALSE) N⤇*N′)


--------------------------------------------------------------------------------


-- `_⇓_` is the big-step reduction relation.
infix 3 _⇓_
_⇓_ : ∀ {g} → Term g → Term g → Set
M ⇓ M′ = M ⤇* M′ × Val M′


-- A big step can be extended with an initial small step.
step⇓ : ∀ {g} → {M M′ M″ : Term g}
              → M ⤇ M′ → M′ ⇓ M″
              → M ⇓ M″
step⇓ M⤇M″ (M″⤇*M′ , VM′) = step M⤇M″ M″⤇*M′ , VM′


-- The initial small step determines the subsequent big step.
rev-step⇓ : ∀ {g} → {M M′ M″ : Term g}
                  → M ⤇ M′ → M ⇓ M″
                  → M′ ⇓ M″
rev-step⇓ M⤇M″ (M″⤇*M′ , VM′) = rev-step M⤇M″ M″⤇*M′ {{VM′}} , VM′


-- Big-step reduction is deterministic.
det⇓ : ∀ {g} → {M M′₁ M′₂ : Term g}
             → M ⇓ M′₁ → M ⇓ M′₂
             → M′₁ ≡ M′₂
det⇓ (M⤇*M′₁ , VM′₁) (M⤇*M′₂ , VM′₂) = det⤇* M⤇*M′₁ {{VM′₁}} M⤇*M′₂ {{VM′₂}}


-- If `M` reduces to `TRUE` and `N` reduces to `N′` then `IF M N O` reduces to `N′`.
leap-IF-TRUE : ∀ {g} → {M N N′ O : Term g}
                     → M ⤇* TRUE → N ⇓ N′
                     → IF M N O ⇓ N′
leap-IF-TRUE M⤇*TRUE (N⤇*N′ , VN′) = step-IF-TRUE M⤇*TRUE N⤇*N′ , VN′


-- If `M` reduces to `FALSE` and `O` reduces to `O′` then `IF M N O` reduces to `O′`.
leap-IF-FALSE : ∀ {g} → {M N O O′ : Term g}
                      → M ⤇* FALSE → O ⇓ O′
                      → IF M N O ⇓ O′
leap-IF-FALSE M⤇*FALSE (O⤇*O′ , VO′) = step-IF-FALSE M⤇*FALSE O⤇*O′ , VO′


--------------------------------------------------------------------------------


-- `_⇓` is the CBV termination relation.
_⇓ : ∀ {g} → Term g → Set
M ⇓ = Σ (Term _) (\ M′ → M ⇓ M′)


-- Termination is preserved by small-step reduction.
step⇓° : ∀ {g} → {M M′ : Term g}
               → M ⤇ M′ → M′ ⇓
               → M ⇓
step⇓° M⤇M′ (M″ , M′⇓M″) = M″ , step⇓ M⤇M′ M′⇓M″


-- Termination is preserved by small-step reduction, in reverse.
rev-step⇓° : ∀ {g} → {M M′ : Term g}
                   → M ⤇ M′ → M ⇓
                   → M′ ⇓
rev-step⇓° M⤇M′ (M″ , M′⇓M″) = M″ , rev-step⇓ M⤇M′ M′⇓M″


-- If `M` reduces to `TRUE` and `N` terminates, then `IF M N O` terminates.
halt-IF-TRUE : ∀ {g} → {M N O : Term g}
                     → M ⤇* TRUE → N ⇓
                     → IF M N O ⇓
halt-IF-TRUE M⤇*TRUE (N′ , N⇓N′) = N′ , leap-IF-TRUE M⤇*TRUE N⇓N′


-- If `M` reduces to `FALSE` and `O` terminates, then `IF M N O` terminates.
halt-IF-FALSE : ∀ {g} → {M N O : Term g}
                      → M ⤇* FALSE → O ⇓
                      → IF M N O ⇓
halt-IF-FALSE M⤇*FALSE (O′ , O⇓O′) = O′ , leap-IF-FALSE M⤇*FALSE O⇓O′


-- Impossible without a stronger induction hypothesis.
-- halt : ∀ {M A} → ∙ ⊢ M ⦂ A
--                → M ⇓
-- halt (var ())
-- halt (lam 𝒟)    = LAM _ , done , VLAM
-- halt (app 𝒟 ℰ)  = {!!}
-- halt true       = TRUE  , done , VTRUE
-- halt false      = FALSE , done , VFALSE
-- halt (if 𝒟 ℰ ℱ) with halt 𝒟
-- halt (if 𝒟 ℰ ℱ) | M′     , M⤇*M′    , VM′    with tp⤇* M⤇*M′ 𝒟
-- halt (if 𝒟 ℰ ℱ) | LAM _  , _         , VLAM   | ()
-- halt (if 𝒟 ℰ ℱ) | TRUE   , M⤇*TRUE  , VTRUE  | true  = halt-IF-TRUE M⤇*TRUE (halt ℰ)
-- halt (if 𝒟 ℰ ℱ) | FALSE  , M⤇*FALSE , VFALSE | false = halt-IF-FALSE M⤇*FALSE (halt ℱ)


--------------------------------------------------------------------------------
