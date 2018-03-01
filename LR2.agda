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
      VUNIT  : Val UNIT
      VPAIR  : ∀ {M N} → {{_ : Val M}} {{_ : Val N}} → Val (PAIR M N)
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
    APP-LAM  : ∀ {M N} → {{_ : Val N}} → APP (LAM M) N ↦ CUT N M
    FST-PAIR : ∀ {M N} → {{_ : Val M}} {{_ : Val N}} → FST (PAIR M N) ↦ M
    SND-PAIR : ∀ {M N} → {{_ : Val M}} {{_ : Val N}} → SND (PAIR M N) ↦ N
    IF-TRUE  : ∀ {N O} → IF TRUE N O ↦ N
    IF-FALSE : ∀ {N O} → IF FALSE N O ↦ O


-- Values do not compute.
¬val↦ : ∀ {g} → {M M′ : Term g} → {{_ : Val M}}
               → ¬ (M ↦ M′)
¬val↦ {{VLAM}}   ()
¬val↦ {{VUNIT}}  ()
¬val↦ {{VPAIR}}  ()
¬val↦ {{VTRUE}}  ()
¬val↦ {{VFALSE}} ()


-- Computation is deterministic.
det↦ : ∀ {g} → {M M′₁ M′₂ : Term g}
              → M ↦ M′₁ → M ↦ M′₂
              → M′₁ ≡ M′₂
det↦ APP-LAM  APP-LAM  = refl
det↦ FST-PAIR FST-PAIR = refl
det↦ SND-PAIR SND-PAIR = refl
det↦ IF-TRUE  IF-TRUE  = refl
det↦ IF-FALSE IF-FALSE = refl


-- Computation is type-preserving.
tp↦ : ∀ {g M M′ A} → {Γ : Types g}
                    → M ↦ M′ → Γ ⊢ M ⦂ A
                    → Γ ⊢ M′ ⦂ A
tp↦ APP-LAM  (app (lam 𝒟) ℰ)  = cut ℰ 𝒟
tp↦ FST-PAIR (fst (pair 𝒟 ℰ)) = 𝒟
tp↦ SND-PAIR (snd (pair 𝒟 ℰ)) = ℰ
tp↦ IF-TRUE  (if 𝒟 ℰ ℱ)       = ℰ
tp↦ IF-FALSE (if 𝒟 ℰ ℱ)       = ℱ


--------------------------------------------------------------------------------


-- `_⤇_` is the CBV small-step reduction relation.
infix 3 _⤇_
data _⤇_ {g} : Term g → Term g → Set
  where
    red : ∀ {M M′} → M ↦ M′
                   → M ⤇ M′

    cong-APP : ∀ {M M′ N} → M ⤇ M′
                          → APP M N ⤇ APP M′ N

    cong-APP-LAM : ∀ {M N N′} → N ⤇ N′
                              → APP (LAM M) N ⤇ APP (LAM M) N′

    cong-PAIR₁ : ∀ {M M′ N} → M ⤇ M′ → PAIR M N ⤇ PAIR M′ N

    cong-PAIR₂ : ∀ {M N N′} → {{_ : Val M}}
                            → N ⤇ N′
                            → PAIR M N ⤇ PAIR M N′

    cong-FST : ∀ {M M′} → M ⤇ M′
                        → FST M ⤇ FST M′

    cong-SND : ∀ {M M′} → M ⤇ M′
                        → SND M ⤇ SND M′

    cong-IF : ∀ {M M′ N O} → M ⤇ M′
                           → IF M N O ⤇ IF M′ N O


-- Values do not reduce.
¬val⤇ : ∀ {g} → {M M′ : Term g} → {{_ : Val M}}
               → ¬ (M ⤇ M′)
¬val⤇ {{VLAM}}   (red ())
¬val⤇ {{VUNIT}}  (red ())
¬val⤇ {{VPAIR}}  (red ())
¬val⤇ {{VPAIR}}  (cong-PAIR₁ M⤇M′) = M⤇M′ ↯ ¬val⤇
¬val⤇ {{VPAIR}}  (cong-PAIR₂ N⤇N′) = N⤇N′ ↯ ¬val⤇
¬val⤇ {{VTRUE}}  (red ())
¬val⤇ {{VFALSE}} (red ())


-- Computation determines small-step reduction.
red-det⤇ : ∀ {g} → {M M′₁ M′₂ : Term g}
                 → M ↦ M′₁ → M ⤇ M′₂
                 → M′₁ ≡ M′₂
red-det⤇ M↦M′₁               (red M↦M′₂)                       = det↦ M↦M′₁ M↦M′₂
red-det⤇ APP-LAM              (cong-APP (red ()))
red-det⤇ (APP-LAM {{VLAM}})   (cong-APP-LAM (red ()))
red-det⤇ (APP-LAM {{VUNIT}})  (cong-APP-LAM (red ()))
red-det⤇ (APP-LAM {{VPAIR}})  (cong-APP-LAM (red ()))
red-det⤇ (APP-LAM {{VPAIR}})  (cong-APP-LAM (cong-PAIR₁ M⤇M′₂)) = M⤇M′₂ ↯ ¬val⤇
red-det⤇ (APP-LAM {{VPAIR}})  (cong-APP-LAM (cong-PAIR₂ N⤇N′₂)) = N⤇N′₂ ↯ ¬val⤇
red-det⤇ (APP-LAM {{VTRUE}})  (cong-APP-LAM (red ()))
red-det⤇ (APP-LAM {{VFALSE}}) (cong-APP-LAM (red ()))
red-det⤇ FST-PAIR             (cong-FST (red ()))
red-det⤇ FST-PAIR             (cong-FST (cong-PAIR₁ M⤇M′₂))     = M⤇M′₂ ↯ ¬val⤇
red-det⤇ FST-PAIR             (cong-FST (cong-PAIR₂ N⤇N′₂))     = N⤇N′₂ ↯ ¬val⤇
red-det⤇ SND-PAIR             (cong-SND (red ()))
red-det⤇ SND-PAIR             (cong-SND (cong-PAIR₁ M⤇M′₂))     = M⤇M′₂ ↯ ¬val⤇
red-det⤇ SND-PAIR             (cong-SND (cong-PAIR₂ N⤇N′₂))     = N⤇N′₂ ↯ ¬val⤇
red-det⤇ IF-TRUE              (cong-IF (red ()))
red-det⤇ IF-FALSE             (cong-IF (red ()))
red-det⤇ ()                   (cong-PAIR₁ _)
red-det⤇ ()                   (cong-PAIR₂ _)


-- Small-step reduction is deterministic.
det⤇ : ∀ {g} → {M M′₁ M′₂ : Term g}
              → M ⤇ M′₁ → M ⤇ M′₂
              → M′₁ ≡ M′₂
det⤇ (red M↦M′₁)                     M⤇M′₂                           = red-det⤇ M↦M′₁ M⤇M′₂
det⤇ (cong-APP M⤇M′₁)                (red M↦M′₂)                     = red-det⤇ M↦M′₂ (cong-APP M⤇M′₁) ⁻¹
det⤇ (cong-APP M⤇M′₁)                (cong-APP M⤇M′₂)                = (\ M′ → APP M′ _) & det⤇ M⤇M′₁ M⤇M′₂
det⤇ (cong-APP (red ()))              (cong-APP-LAM _)
det⤇ (cong-APP-LAM N⤇N′₁)            (red M↦M′₂)                     = red-det⤇ M↦M′₂ (cong-APP-LAM N⤇N′₁) ⁻¹
det⤇ (cong-APP-LAM _)                 (cong-APP (red ()))
det⤇ (cong-APP-LAM N⤇N′₁)            (cong-APP-LAM N⤇N′₂)            = (\ N′ → APP _ N′) & det⤇ N⤇N′₁ N⤇N′₂
det⤇ (cong-FST M⤇M′₁)                (red M↦M′₂)                     = red-det⤇ M↦M′₂ (cong-FST M⤇M′₁) ⁻¹
det⤇ (cong-FST M⤇M′₁)                (cong-FST M⤇M′₂)                = FST & det⤇ M⤇M′₁ M⤇M′₂
det⤇ (cong-SND M⤇M′₁)                (red M↦M′₂)                     = red-det⤇ M↦M′₂ (cong-SND M⤇M′₁) ⁻¹
det⤇ (cong-SND M⤇M′₁)                (cong-SND M⤇M′₂)                = SND & det⤇ M⤇M′₁ M⤇M′₂
det⤇ (cong-PAIR₁ M⤇M′₁)              (red M↦M′₂)                     = red-det⤇ M↦M′₂ (cong-PAIR₁ M⤇M′₁) ⁻¹
det⤇ (cong-PAIR₁ M⤇M′₁)              (cong-PAIR₁ M⤇M′₂)              = (\ M′ → PAIR M′ _) & det⤇ M⤇M′₁ M⤇M′₂
det⤇ (cong-PAIR₁ (red ()))            (cong-PAIR₂ {{VLAM}} N⤇N′₂)
det⤇ (cong-PAIR₁ (red ()))            (cong-PAIR₂ {{VUNIT}} N⤇N′₂)
det⤇ (cong-PAIR₁ (red ()))            (cong-PAIR₂ {{VPAIR}} N⤇N′₂)
det⤇ (cong-PAIR₁ (cong-PAIR₁ M⤇M′₁)) (cong-PAIR₂ {{VPAIR}} N⤇N′₂)    = M⤇M′₁ ↯ ¬val⤇
det⤇ (cong-PAIR₁ (cong-PAIR₂ M⤇M′₁)) (cong-PAIR₂ {{VPAIR}} N⤇N′₂)    = M⤇M′₁ ↯ ¬val⤇
det⤇ (cong-PAIR₁ (red ()))            (cong-PAIR₂ {{VTRUE}} N⤇N′₂)
det⤇ (cong-PAIR₁ (red ()))            (cong-PAIR₂ {{VFALSE}} N⤇N′₂)
det⤇ (cong-PAIR₂ N⤇N′₁)              (red M↦M′₂)                     = red-det⤇ M↦M′₂ (cong-PAIR₂ N⤇N′₁) ⁻¹
det⤇ (cong-PAIR₂ {{VLAM}} N⤇N′₁)     (cong-PAIR₁ (red ()))
det⤇ (cong-PAIR₂ {{VUNIT}} N⤇N′₁)    (cong-PAIR₁ (red ()))
det⤇ (cong-PAIR₂ {{VPAIR}} N⤇N′₁)    (cong-PAIR₁ (red ()))
det⤇ (cong-PAIR₂ {{VPAIR}} N⤇N′₁)    (cong-PAIR₁ (cong-PAIR₁ M⤇M′₂)) = M⤇M′₂ ↯ ¬val⤇
det⤇ (cong-PAIR₂ {{VPAIR}} N⤇N′₁)    (cong-PAIR₁ (cong-PAIR₂ N⤇N′₂)) = N⤇N′₂ ↯ ¬val⤇
det⤇ (cong-PAIR₂ {{VTRUE}} N⤇N′₁)    (cong-PAIR₁ (red ()))
det⤇ (cong-PAIR₂ {{VFALSE}} N⤇N′₁)   (cong-PAIR₁ (red ()))
det⤇ (cong-PAIR₂ N⤇N′₁)              (cong-PAIR₂ N⤇N′₂)              = (\ N′ → PAIR _ N′) & det⤇ N⤇N′₁ N⤇N′₂
det⤇ (cong-IF M⤇M′₁)                 (red M↦M′₂)                     = red-det⤇ M↦M′₂ (cong-IF M⤇M′₁) ⁻¹
det⤇ (cong-IF M⤇M′₁)                 (cong-IF M⤇M′₂)                 = (\ M′ → IF M′ _ _) & det⤇ M⤇M′₁ M⤇M′₂


-- Small-step reduction is type-preserving.
tp⤇ : ∀ {g M M′ A} → {Γ : Types g}
                    → M ⤇ M′ → Γ ⊢ M ⦂ A
                    → Γ ⊢ M′ ⦂ A
tp⤇ (red M↦M′)          𝒟          = tp↦ M↦M′ 𝒟
tp⤇ (cong-APP M⤇M′)     (app 𝒟 ℰ)  = app (tp⤇ M⤇M′ 𝒟) ℰ
tp⤇ (cong-APP-LAM M⤇M′) (app 𝒟 ℰ)  = app 𝒟 (tp⤇ M⤇M′ ℰ)
tp⤇ (cong-PAIR₁ M⤇M′)   (pair 𝒟 ℰ) = pair (tp⤇ M⤇M′ 𝒟) ℰ
tp⤇ (cong-PAIR₂ N⤇N′)   (pair 𝒟 ℰ) = pair 𝒟 (tp⤇ N⤇N′ ℰ)
tp⤇ (cong-FST M⤇M′)     (fst 𝒟)    = fst (tp⤇ M⤇M′ 𝒟)
tp⤇ (cong-SND M⤇M′)     (snd 𝒟)    = snd (tp⤇ M⤇M′ 𝒟)
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
unstep M⤇M′₁             (step M⤇M′₂ M′₂⤇*M″) with det⤇ M⤇M′₁ M⤇M′₂
unstep M⤇M′              (step _      M′⤇*M″)  | refl = M′⤇*M″
unstep (red ())           done {{VLAM}}
unstep (red ())           done {{VUNIT}}
unstep (red ())           done {{VPAIR}}
unstep (red ())           done {{VTRUE}}
unstep (red ())           done {{VFALSE}}
unstep (cong-PAIR₁ M⤇M′) done {{VPAIR}}         = M⤇M′ ↯ ¬val⤇
unstep (cong-PAIR₂ N⤇N′) done {{VPAIR}}         = N⤇N′ ↯ ¬val⤇


-- When reducing down to a value, iterated small-step reduction is deterministic.
det⤇* : ∀ {g} → {M M′₁ M′₂ : Term g}
               → M ⤇* M′₁ → {{_ : Val M′₁}} → M ⤇* M′₂ → {{_ : Val M′₂}}
               → M′₁ ≡ M′₂
det⤇* done                    done                        = refl
det⤇* (step M⤇M″₁ M″₁⤇*M′₁) M⤇*M′₂                     = det⤇* M″₁⤇*M′₁ (unstep M⤇M″₁ M⤇*M′₂)
det⤇* done {{VLAM}}           (step (red ()) _)
det⤇* done {{VUNIT}}          (step (red ()) _)
det⤇* done {{VPAIR}}          (step (red ()) _)
det⤇* done {{VTRUE}}          (step (red ()) _)
det⤇* done {{VFALSE}}         (step (red ()) _)
det⤇* done {{VPAIR}}          (step (cong-PAIR₁ M⤇M′) _) = M⤇M′ ↯ ¬val⤇
det⤇* done {{VPAIR}}          (step (cong-PAIR₂ N⤇N′) _) = N⤇N′ ↯ ¬val⤇


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


-- If `M` reduces to `M′` and `N` reduces to `N′`, then `PAIR M N` reduces to `PAIR M′ N′`.
congs-PAIR : ∀ {g} → {M M′ N N′ : Term g} → {{_ : Val M′}} {{_ : Val N′}}
                   → M ⤇* M′ → N ⤇* N′
                   → PAIR M N ⤇* PAIR M′ N′
congs-PAIR done                 done                 = done
congs-PAIR done                 (step N⤇N″ N″⤇*N′) = step (cong-PAIR₂ N⤇N″) (congs-PAIR done N″⤇*N′)
congs-PAIR (step M⤇M″ M″⤇*M′) N⤇*N′               = step (cong-PAIR₁ M⤇M″) (congs-PAIR M″⤇*M′ N⤇*N′)


-- If `M` reduces to `M′`, then `FST M` reduces to `FST M′`.
congs-FST : ∀ {g} → {M M′ : Term g}
                  → M ⤇* M′
                  → FST M ⤇* FST M′
congs-FST done                 = done
congs-FST (step M⤇M″ M″⤇*M′) = step (cong-FST M⤇M″) (congs-FST M″⤇*M′)


-- If `M` reduces to `M′`, then `SND M` reduces to `SND M′`.
congs-SND : ∀ {g} → {M M′ : Term g}
                  → M ⤇* M′
                  → SND M ⤇* SND M′
congs-SND done                 = done
congs-SND (step M⤇M″ M″⤇*M′) = step (cong-SND M⤇M″) (congs-SND M″⤇*M′)


-- If `M` reduces to `M′`, then `IF M N O` reduces to `IF M′ N O`.
congs-IF : ∀ {g} → {M M′ N O : Term g}
                 → M ⤇* M′
                 → IF M N O ⤇* IF M′ N O
congs-IF done                 = done
congs-IF (step M⤇M″ M″⤇*M′) = step (cong-IF M⤇M″) (congs-IF M″⤇*M′)


-- If `M` reduces to `PAIR M′ N′`, then `FST M` reduces to `M′`.
reds-FST-PAIR : ∀ {g} → {M M′ N′ : Term g} → {{_ : Val M′}} {{_ : Val N′}}
                      → M ⤇* PAIR M′ N′
                      → FST M ⤇* M′
reds-FST-PAIR M⤇*PAIR = steps (congs-FST M⤇*PAIR) (step (red FST-PAIR) done)


-- If `M` reduces to `PAIR M′ N′`, then `SND M` reduces to `N′`.
reds-SND-PAIR : ∀ {g} → {M M′ N′ : Term g} → {{_ : Val M′}} {{_ : Val N′}}
                      → M ⤇* PAIR M′ N′
                      → SND M ⤇* N′
reds-SND-PAIR M⤇*PAIR = steps (congs-SND M⤇*PAIR) (step (red SND-PAIR) done)


-- If `M` reduces to `TRUE` and `N` reduces to `N′`, then `IF M N O` reduces to `N′`.
reds-IF-TRUE : ∀ {g} → {M N N′ O : Term g}
                     → M ⤇* TRUE → N ⤇* N′
                     → IF M N O ⤇* N′
reds-IF-TRUE M⤇*TRUE N⤇*N′ = steps (congs-IF M⤇*TRUE) (step (red IF-TRUE) N⤇*N′)


-- If `M` reduces to `FALSE` and `O` reduces to `O′`, then `IF M N O` reduces to `O′`.
reds-IF-FALSE : ∀ {g} → {M N O O′ : Term g}
                      → M ⤇* FALSE → O ⤇* O′
                      → IF M N O ⤇* O′
reds-IF-FALSE M⤇*FALSE N⤇*N′ = steps (congs-IF M⤇*FALSE) (step (red IF-FALSE) N⤇*N′)


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


-- If `M` reduces to `M′` and `N` reduces to `N′`, then `PAIR M N` reduces to `PAIR M′ N′`.
big-red-PAIR : ∀ {g} → {M M′ N N′ : Term g}
                     → M ⇓ M′ → N ⇓ N′
                     → PAIR M N ⇓ PAIR M′ N′
big-red-PAIR (M⤇*M′ , VM′) (N⤇*N′ , VN′) = congs-PAIR {{VM′}} {{VN′}} M⤇*M′ N⤇*N′ , VPAIR {{VM′}} {{VN′}}


-- If `M` reduces to `PAIR M′ N′`, then `FST M` reduces to `M′`.
big-red-FST-PAIR : ∀ {g} → {M M′ N′ : Term g} → {{_ : Val M′}} {{_ : Val N′}}
                         → M ⤇* PAIR M′ N′
                         → FST M ⇓ M′
big-red-FST-PAIR {{VM′}} M⤇*PAIR = reds-FST-PAIR M⤇*PAIR , VM′


-- If `M` reduces to `PAIR M′ N′`, then `SND M` reduces to `N′`.
big-red-SND-PAIR : ∀ {g} → {M M′ N′ : Term g} → {{_ : Val M′}} {{_ : Val N′}}
                         → M ⤇* PAIR M′ N′
                         → SND M ⇓ N′
big-red-SND-PAIR {{_}} {{VN′}} M⤇*PAIR = reds-SND-PAIR M⤇*PAIR , VN′


-- If `M` reduces to `TRUE` and `N` reduces to `N′`, then `IF M N O` reduces to `N′`.
big-red-IF-TRUE : ∀ {g} → {M N N′ O : Term g}
                        → M ⤇* TRUE → N ⇓ N′
                        → IF M N O ⇓ N′
big-red-IF-TRUE M⤇*TRUE (N⤇*N′ , VN′) = reds-IF-TRUE M⤇*TRUE N⤇*N′ , VN′


-- If `M` reduces to `FALSE` and `O` reduces to `O′`, then `IF M N O` reduces to `O′`.
big-red-IF-FALSE : ∀ {g} → {M N O O′ : Term g}
                         → M ⤇* FALSE → O ⇓ O′
                         → IF M N O ⇓ O′
big-red-IF-FALSE M⤇*FALSE (O⤇*O′ , VO′) = reds-IF-FALSE M⤇*FALSE O⤇*O′ , VO′


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


-- If `M` terminates and `N` terminates, then `PAIR M N` terminates.
halt-PAIR : ∀ {g} → {M N : Term g}
                  → M ⇓ → N ⇓
                  → PAIR M N ⇓
halt-PAIR (M′ , M⇓M′) (N′ , N⇓N′) = PAIR M′ N′ , big-red-PAIR M⇓M′ N⇓N′


-- If `M` reduces to `PAIR M′ N′`, then `FST M` terminates.
halt-FST-PAIR : ∀ {g} → {M M′ N′ : Term g} → {{_ : Val M′}} {{_ : Val N′}}
                      → M ⤇* PAIR M′ N′
                      → FST M ⇓
halt-FST-PAIR {M′ = M′} M⤇*PAIR = M′ , big-red-FST-PAIR M⤇*PAIR


-- If `M` reduces to `PAIR M′ N′`, then `SND M` terminates.
halt-SND-PAIR : ∀ {g} → {M M′ N′ : Term g} → {{_ : Val M′}} {{_ : Val N′}}
                      → M ⤇* PAIR M′ N′
                      → SND M ⇓
halt-SND-PAIR {N′ = N′} M⤇*PAIR = N′ , big-red-SND-PAIR M⤇*PAIR


-- If `M` reduces to `TRUE` and `N` terminates, then `IF M N O` terminates.
halt-IF-TRUE : ∀ {g} → {M N O : Term g}
                     → M ⤇* TRUE → N ⇓
                     → IF M N O ⇓
halt-IF-TRUE M⤇*TRUE (N′ , N⇓N′) = N′ , big-red-IF-TRUE M⤇*TRUE N⇓N′


-- If `M` reduces to `FALSE` and `O` terminates, then `IF M N O` terminates.
halt-IF-FALSE : ∀ {g} → {M N O : Term g}
                      → M ⤇* FALSE → O ⇓
                      → IF M N O ⇓
halt-IF-FALSE M⤇*FALSE (O′ , O⇓O′) = O′ , big-red-IF-FALSE M⤇*FALSE O⇓O′


-- Every well-typed term terminates.
-- Impossible without a stronger induction hypothesis.
{-
halt : ∀ {M A} → ∙ ⊢ M ⦂ A
               → M ⇓
halt (var ())
halt (lam 𝒟)    = LAM _ , done , VLAM
halt (app 𝒟 ℰ)  = {!!}
halt unit       = UNIT  , done , VUNIT
halt (pair 𝒟 ℰ) = halt-PAIR (halt 𝒟) (halt ℰ)
halt (fst 𝒟)    with halt 𝒟
halt (fst 𝒟)    | M′       , M⤇*M′   , VM′    with tp⤇* M⤇*M′ 𝒟
halt (fst 𝒟)    | LAM _    , _        , VLAM   | ()
halt (fst 𝒟)    | UNIT     , _        , VUNIT  | ()
halt (fst 𝒟)    | PAIR _ _ , M⤇*PAIR , VPAIR  | pair _ _ = halt-FST-PAIR M⤇*PAIR
halt (fst 𝒟)    | TRUE     , _        , VTRUE  | ()
halt (fst 𝒟)    | FALSE    , _        , VFALSE | ()
halt (snd 𝒟)    with halt 𝒟
halt (snd 𝒟)    | M′       , M⤇*M′   , VM′    with tp⤇* M⤇*M′ 𝒟
halt (snd 𝒟)    | LAM _    , _        , VLAM   | ()
halt (snd 𝒟)    | UNIT     , _        , VUNIT  | ()
halt (snd 𝒟)    | PAIR _ _ , M⤇*PAIR , VPAIR  | pair _ _ = halt-SND-PAIR M⤇*PAIR
halt (snd 𝒟)    | TRUE     , _        , VTRUE  | ()
halt (snd 𝒟)    | FALSE    , _        , VFALSE | ()
halt true       = TRUE  , done , VTRUE
halt false      = FALSE , done , VFALSE
halt (if 𝒟 ℰ ℱ) with halt 𝒟
halt (if 𝒟 ℰ ℱ) | M′       , M⤇*M′    , VM′    with tp⤇* M⤇*M′ 𝒟
halt (if 𝒟 ℰ ℱ) | LAM _    , _         , VLAM   | ()
halt (if 𝒟 ℰ ℱ) | UNIT     , _         , VUNIT  | ()
halt (if 𝒟 ℰ ℱ) | PAIR _ _ , _         , VPAIR  | ()
halt (if 𝒟 ℰ ℱ) | TRUE     , M⤇*TRUE  , VTRUE  | true  = halt-IF-TRUE M⤇*TRUE (halt ℰ)
halt (if 𝒟 ℰ ℱ) | FALSE    , M⤇*FALSE , VFALSE | false = halt-IF-FALSE M⤇*FALSE (halt ℱ)
-}


--------------------------------------------------------------------------------
