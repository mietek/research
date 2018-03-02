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
      val-lam   : ∀ {M} → Val (LAM M)
      val-unit  : Val UNIT
      val-pair  : ∀ {M N} → {{_ : Val M}} {{_ : Val N}} → Val (PAIR M N)
      val-true  : Val TRUE
      val-false : Val FALSE


-- `Vals τ` says that all terms `τ` are values.
data Vals {g} : ∀ {n} → Terms g n → Set
  where
    instance
      ∙   : Vals ∙
      _,_ : ∀ {n M} → {τ : Terms g n} → Vals τ → Val M → Vals (τ , M)


--------------------------------------------------------------------------------


-- `_⤠_` is the CBV computation relation.
infix 3 _⤠_
data _⤠_ {g} : Term g → Term g → Set
  where
    app-lam  : ∀ {M N} → {{_ : Val N}} → APP (LAM M) N ⤠ CUT N M
    fst-pair : ∀ {M N} → {{_ : Val M}} {{_ : Val N}} → FST (PAIR M N) ⤠ M
    snd-pair : ∀ {M N} → {{_ : Val M}} {{_ : Val N}} → SND (PAIR M N) ⤠ N
    if-true  : ∀ {N O} → IF TRUE N O ⤠ N
    if-false : ∀ {N O} → IF FALSE N O ⤠ O


-- Values do not compute.
¬val⤠ : ∀ {g} → {M M′ : Term g} → {{_ : Val M}}
               → ¬ (M ⤠ M′)
¬val⤠ {{val-lam}}   ()
¬val⤠ {{val-unit}}  ()
¬val⤠ {{val-pair}}  ()
¬val⤠ {{val-true}}  ()
¬val⤠ {{val-false}} ()


-- Computation is deterministic.
det⤠ : ∀ {g} → {M M′₁ M′₂ : Term g}
              → M ⤠ M′₁ → M ⤠ M′₂
              → M′₁ ≡ M′₂
det⤠ app-lam  app-lam  = refl
det⤠ fst-pair fst-pair = refl
det⤠ snd-pair snd-pair = refl
det⤠ if-true  if-true  = refl
det⤠ if-false if-false = refl


-- Computation is type-preserving.
tp⤠ : ∀ {g M M′ A} → {Γ : Types g}
                    → M ⤠ M′ → Γ ⊢ M ⦂ A
                    → Γ ⊢ M′ ⦂ A
tp⤠ app-lam  (app (lam 𝒟) ℰ)  = cut ℰ 𝒟
tp⤠ fst-pair (fst (pair 𝒟 ℰ)) = 𝒟
tp⤠ snd-pair (snd (pair 𝒟 ℰ)) = ℰ
tp⤠ if-true  (if 𝒟 ℰ ℱ)       = ℰ
tp⤠ if-false (if 𝒟 ℰ ℱ)       = ℱ


--------------------------------------------------------------------------------


-- `_↦_` is the CBV small-step reduction relation.
infix 3 _↦_
data _↦_ {g} : Term g → Term g → Set
  where
    red : ∀ {M M′} → M ⤠ M′
                   → M ↦ M′

    cong-app₁ : ∀ {M M′ N} → M ↦ M′
                           → APP M N ↦ APP M′ N

    cong-app₂ : ∀ {M N N′} → {{_ : Val M}}
                           → N ↦ N′
                           → APP M N ↦ APP M N′

    cong-pair₁ : ∀ {M M′ N} → M ↦ M′
                            → PAIR M N ↦ PAIR M′ N

    cong-pair₂ : ∀ {M N N′} → {{_ : Val M}}
                            → N ↦ N′
                            → PAIR M N ↦ PAIR M N′

    cong-fst : ∀ {M M′} → M ↦ M′
                        → FST M ↦ FST M′

    cong-snd : ∀ {M M′} → M ↦ M′
                        → SND M ↦ SND M′

    cong-if : ∀ {M M′ N O} → M ↦ M′
                           → IF M N O ↦ IF M′ N O


-- Values do not reduce.
¬val↦ : ∀ {g} → {M M′ : Term g} → {{_ : Val M}}
               → ¬ (M ↦ M′)
¬val↦ {{val-lam}}   (red ())
¬val↦ {{val-unit}}  (red ())
¬val↦ {{val-pair}}  (red ())
¬val↦ {{val-pair}}  (cong-pair₁ M↦M′) = M↦M′ ↯ ¬val↦
¬val↦ {{val-pair}}  (cong-pair₂ N↦N′) = N↦N′ ↯ ¬val↦
¬val↦ {{val-true}}  (red ())
¬val↦ {{val-false}} (red ())


-- Computation determines small-step reduction.
red-det↦ : ∀ {g} → {M M′₁ M′₂ : Term g}
                  → M ⤠ M′₁ → M ↦ M′₂
                  → M′₁ ≡ M′₂
red-det↦ M⤠M′₁   (red M⤠M′₂)       = det⤠ M⤠M′₁ M⤠M′₂
red-det↦ app-lam  (cong-app₁ M↦M′₂) = M↦M′₂ ↯ ¬val↦
red-det↦ app-lam  (cong-app₂ M↦M′₂) = M↦M′₂ ↯ ¬val↦
red-det↦ fst-pair (cong-fst M↦M′₂)  = M↦M′₂ ↯ ¬val↦
red-det↦ snd-pair (cong-snd M↦M′₂)  = M↦M′₂ ↯ ¬val↦
red-det↦ if-true  (cong-if M↦M′₂)   = M↦M′₂ ↯ ¬val↦
red-det↦ if-false (cong-if M↦M′₂)   = M↦M′₂ ↯ ¬val↦
red-det↦ ()       (cong-pair₁ _)
red-det↦ ()       (cong-pair₂ _)


-- Small-step reduction is deterministic.
det↦ : ∀ {g} → {M M′₁ M′₂ : Term g}
              → M ↦ M′₁ → M ↦ M′₂
              → M′₁ ≡ M′₂
det↦ (red M⤠M′₁)        M↦M′₂              = red-det↦ M⤠M′₁ M↦M′₂
det↦ (cong-app₁ M↦M′₁)  (cong-app₁ M↦M′₂)  = (\ M′ → APP M′ _) & det↦ M↦M′₁ M↦M′₂
det↦ (cong-app₂ N↦N′₁)  (cong-app₂ N↦N′₂)  = (\ N′ → APP _ N′) & det↦ N↦N′₁ N↦N′₂
det↦ (cong-pair₁ M↦M′₁) (cong-pair₁ M↦M′₂) = (\ M′ → PAIR M′ _) & det↦ M↦M′₁ M↦M′₂
det↦ (cong-pair₂ N↦N′₁) (cong-pair₂ N↦N′₂) = (\ N′ → PAIR _ N′) & det↦ N↦N′₁ N↦N′₂
det↦ (cong-fst M↦M′₁)   (cong-fst M↦M′₂)   = FST & det↦ M↦M′₁ M↦M′₂
det↦ (cong-snd M↦M′₁)   (cong-snd M↦M′₂)   = SND & det↦ M↦M′₁ M↦M′₂
det↦ (cong-if M↦M′₁)    (cong-if M↦M′₂)    = (\ M′ → IF M′ _ _) & det↦ M↦M′₁ M↦M′₂
det↦ (cong-app₁ M↦M′₁)  (cong-app₂ _)       = M↦M′₁ ↯ ¬val↦
det↦ (cong-app₂ _)       (cong-app₁ M↦M′₂)  = M↦M′₂ ↯ ¬val↦
det↦ (cong-pair₁ M↦M′₁) (cong-pair₂ _)      = M↦M′₁ ↯ ¬val↦
det↦ (cong-pair₂ _)      (cong-pair₁ M↦M′₂) = M↦M′₂ ↯ ¬val↦
det↦ M↦M′₁              (red M⤠M′₂)        = red-det↦ M⤠M′₂ M↦M′₁ ⁻¹


-- Small-step reduction is type-preserving.
tp↦ : ∀ {g M M′ A} → {Γ : Types g}
                    → M ↦ M′ → Γ ⊢ M ⦂ A
                    → Γ ⊢ M′ ⦂ A
tp↦ (red M⤠M′)        𝒟          = tp⤠ M⤠M′ 𝒟
tp↦ (cong-app₁ M↦M′)  (app 𝒟 ℰ)  = app (tp↦ M↦M′ 𝒟) ℰ
tp↦ (cong-app₂ M↦M′)  (app 𝒟 ℰ)  = app 𝒟 (tp↦ M↦M′ ℰ)
tp↦ (cong-pair₁ M↦M′) (pair 𝒟 ℰ) = pair (tp↦ M↦M′ 𝒟) ℰ
tp↦ (cong-pair₂ N↦N′) (pair 𝒟 ℰ) = pair 𝒟 (tp↦ N↦N′ ℰ)
tp↦ (cong-fst M↦M′)   (fst 𝒟)    = fst (tp↦ M↦M′ 𝒟)
tp↦ (cong-snd M↦M′)   (snd 𝒟)    = snd (tp↦ M↦M′ 𝒟)
tp↦ (cong-if M↦M′)    (if 𝒟 ℰ ℱ) = if (tp↦ M↦M′ 𝒟) ℰ ℱ


--------------------------------------------------------------------------------


-- `_⤅_` is the iterated small-step reduction relation.
infix 3 _⤅_
data _⤅_ {g} : Term g → Term g → Set
  where
    -- Iterated small-step reduction is reflexive.
    done : ∀ {M} → M ⤅ M

    -- Small-step reduction IN REVERSE preserves iterated small-step reduction.
    step : ∀ {M M′ M″} → M ↦ M′ → M′ ⤅ M″
                       → M ⤅ M″


-- Iterated small-step reduction is transitive.
-- Iterated small-step reduction IN REVERSE preserves iterated small-step reduction.
steps : ∀ {g} → {M M′ M″ : Term g}
              → M ⤅ M′ → M′ ⤅ M″
              → M ⤅ M″
steps done                M⤅M″  = M⤅M″
steps (step M↦M‴ M‴⤅M′) M′⤅M″ = step M↦M‴ (steps M‴⤅M′ M′⤅M″)


-- When reducing down to a value, the initial small step determines the subsequent small steps.
-- Small-step reduction preserves iterated small-step reduction down to a value.
unstep : ∀ {g} → {M M′ M″ : Term g} → {{_ : Val M″}}
               → M ↦ M′ → M ⤅ M″
               → M′ ⤅ M″
unstep M↦M′₁ (step M↦M′₂ M′₂⤅M″) with det↦ M↦M′₁ M↦M′₂
unstep M↦M′  (step _      M′⤅M″)  | refl = M′⤅M″
unstep M↦M′  done                  = M↦M′ ↯ ¬val↦


-- When reducing down to a value, iterated small-step reduction is deterministic.
det⤅ : ∀ {g} → {M M′₁ M′₂ : Term g} → {{_ : Val M′₁}} {{_ : Val M′₂}}
              → M ⤅ M′₁ → M ⤅ M′₂
              → M′₁ ≡ M′₂
det⤅ done                   done                = refl
det⤅ done                   (step M↦M″ M″⤅M′) = M↦M″ ↯ ¬val↦
det⤅ (step M↦M″₁ M″₁⤅M′₁) M⤅M′₂              = det⤅ M″₁⤅M′₁ (unstep M↦M″₁ M⤅M′₂)


-- Iterated small-step reduction is type-preserving.
tp⤅ : ∀ {g M M′ A} → {Γ : Types g}
                    → M ⤅ M′ → Γ ⊢ M ⦂ A
                    → Γ ⊢ M′ ⦂ A
tp⤅ done                𝒟 = 𝒟
tp⤅ (step M↦M″ M″⤅M′) 𝒟 = tp⤅ M″⤅M′ (tp↦ M↦M″ 𝒟)


-- If `M` reduces to `M′`, then `APP M N` reduces to `APP M′ N`.
congs-app₁ : ∀ {g} → {M M′ N : Term g}
                   → M ⤅ M′
                   → APP M N ⤅ APP M′ N
congs-app₁ done                = done
congs-app₁ (step M↦M″ M″⤅M′) = step (cong-app₁ M↦M″) (congs-app₁ M″⤅M′)


-- If `N` reduces to `N′`, then `APP (LAM M) N` reduces to `APP (LAM M) N′`.
congs-app₂ : ∀ {g} → {M : Term (suc g)} {N N′ : Term g}
                   → N ⤅ N′
                   → APP (LAM M) N ⤅ APP (LAM M) N′
congs-app₂ done                = done
congs-app₂ (step M↦M″ M″⤅M′) = step (cong-app₂ M↦M″) (congs-app₂ M″⤅M′)


-- If `M` reduces to `M′` and `N` reduces to `N′`, then `PAIR M N` reduces to `PAIR M′ N′`.
congs-pair : ∀ {g} → {M M′ N N′ : Term g} → {{_ : Val M′}} {{_ : Val N′}}
                   → M ⤅ M′ → N ⤅ N′
                   → PAIR M N ⤅ PAIR M′ N′
congs-pair done                done                = done
congs-pair done                (step N↦N″ N″⤅N′) = step (cong-pair₂ N↦N″) (congs-pair done N″⤅N′)
congs-pair (step M↦M″ M″⤅M′) N⤅N′               = step (cong-pair₁ M↦M″) (congs-pair M″⤅M′ N⤅N′)


-- If `M` reduces to `M′`, then `FST M` reduces to `FST M′`.
congs-fst : ∀ {g} → {M M′ : Term g}
                  → M ⤅ M′
                  → FST M ⤅ FST M′
congs-fst done                = done
congs-fst (step M↦M″ M″⤅M′) = step (cong-fst M↦M″) (congs-fst M″⤅M′)


-- If `M` reduces to `M′`, then `SND M` reduces to `SND M′`.
congs-snd : ∀ {g} → {M M′ : Term g}
                  → M ⤅ M′
                  → SND M ⤅ SND M′
congs-snd done                = done
congs-snd (step M↦M″ M″⤅M′) = step (cong-snd M↦M″) (congs-snd M″⤅M′)


-- If `M` reduces to `M′`, then `IF M N O` reduces to `IF M′ N O`.
congs-if : ∀ {g} → {M M′ N O : Term g}
                 → M ⤅ M′
                 → IF M N O ⤅ IF M′ N O
congs-if done                = done
congs-if (step M↦M″ M″⤅M′) = step (cong-if M↦M″) (congs-if M″⤅M′)


-- If `M` reduces to `PAIR M′ N′`, then `FST M` reduces to `M′`.
reds-fst-pair : ∀ {g} → {M M′ N′ : Term g} → {{_ : Val M′}} {{_ : Val N′}}
                      → M ⤅ PAIR M′ N′
                      → FST M ⤅ M′
reds-fst-pair M⤅PAIR = steps (congs-fst M⤅PAIR) (step (red fst-pair) done)


-- If `M` reduces to `PAIR M′ N′`, then `SND M` reduces to `N′`.
reds-snd-pair : ∀ {g} → {M M′ N′ : Term g} → {{_ : Val M′}} {{_ : Val N′}}
                      → M ⤅ PAIR M′ N′
                      → SND M ⤅ N′
reds-snd-pair M⤅PAIR = steps (congs-snd M⤅PAIR) (step (red snd-pair) done)


-- If `M` reduces to `TRUE` and `N` reduces to `N′`, then `IF M N O` reduces to `N′`.
reds-if-true : ∀ {g} → {M N N′ O : Term g}
                     → M ⤅ TRUE → N ⤅ N′
                     → IF M N O ⤅ N′
reds-if-true M⤅TRUE N⤅N′ = steps (congs-if M⤅TRUE) (step (red if-true) N⤅N′)


-- If `M` reduces to `FALSE` and `O` reduces to `O′`, then `IF M N O` reduces to `O′`.
reds-if-false : ∀ {g} → {M N O O′ : Term g}
                      → M ⤅ FALSE → O ⤅ O′
                      → IF M N O ⤅ O′
reds-if-false M⤅FALSE N⤅N′ = steps (congs-if M⤅FALSE) (step (red if-false) N⤅N′)


--------------------------------------------------------------------------------


-- `_⇓_` is the big-step reduction relation.
infix 3 _⇓_
_⇓_ : ∀ {g} → Term g → Term g → Set
M ⇓ M′ = M ⤅ M′ × Val M′


-- A big step can be extended with an initial small step.
-- Small-step reduction IN REVERSE preserves big-step reduction.
big-step : ∀ {g} → {M M′ M″ : Term g}
                 → M ↦ M′ → M′ ⇓ M″
                 → M ⇓ M″
big-step M↦M′ (M′⤅M″ , VM″) = step M↦M′ M′⤅M″ , VM″


-- The initial small step determines the subsequent big step.
-- Small-step reduction preserves big-step reduction.
big-unstep : ∀ {g} → {M M′ M″ : Term g}
                   → M ↦ M′ → M ⇓ M″
                   → M′ ⇓ M″
big-unstep M↦M′ (M′⤅M″ , VM″) = unstep {{VM″}} M↦M′ M′⤅M″ , VM″


-- Big-step reduction is deterministic.
det⇓ : ∀ {g} → {M M′₁ M′₂ : Term g}
             → M ⇓ M′₁ → M ⇓ M′₂
             → M′₁ ≡ M′₂
det⇓ (M⤅M′₁ , VM′₁) (M⤅M′₂ , VM′₂) = det⤅ {{VM′₁}} {{VM′₂}} M⤅M′₁ M⤅M′₂


-- If `M` reduces to `M′` and `N` reduces to `N′`, then `PAIR M N` reduces to `PAIR M′ N′`.
big-red-pair : ∀ {g} → {M M′ N N′ : Term g}
                     → M ⇓ M′ → N ⇓ N′
                     → PAIR M N ⇓ PAIR M′ N′
big-red-pair (M⤅M′ , VM′) (N⤅N′ , VN′) = congs-pair {{VM′}} {{VN′}} M⤅M′ N⤅N′ , val-pair {{VM′}} {{VN′}}


-- If `M` reduces to `PAIR M′ N′`, then `FST M` reduces to `M′`.
big-red-fst-pair : ∀ {g} → {M M′ N′ : Term g} → {{_ : Val M′}} {{_ : Val N′}}
                         → M ⤅ PAIR M′ N′
                         → FST M ⇓ M′
big-red-fst-pair {{VM′}} M⤅PAIR = reds-fst-pair M⤅PAIR , VM′


-- If `M` reduces to `PAIR M′ N′`, then `SND M` reduces to `N′`.
big-red-snd-pair : ∀ {g} → {M M′ N′ : Term g} → {{_ : Val M′}} {{_ : Val N′}}
                         → M ⤅ PAIR M′ N′
                         → SND M ⇓ N′
big-red-snd-pair {{_}} {{VN′}} M⤅PAIR = reds-snd-pair M⤅PAIR , VN′


-- If `M` reduces to `TRUE` and `N` reduces to `N′`, then `IF M N O` reduces to `N′`.
big-red-if-true : ∀ {g} → {M N N′ O : Term g}
                        → M ⤅ TRUE → N ⇓ N′
                        → IF M N O ⇓ N′
big-red-if-true M⤅TRUE (N⤅N′ , VN′) = reds-if-true M⤅TRUE N⤅N′ , VN′


-- If `M` reduces to `FALSE` and `O` reduces to `O′`, then `IF M N O` reduces to `O′`.
big-red-if-false : ∀ {g} → {M N O O′ : Term g}
                         → M ⤅ FALSE → O ⇓ O′
                         → IF M N O ⇓ O′
big-red-if-false M⤅FALSE (O⤅O′ , VO′) = reds-if-false M⤅FALSE O⤅O′ , VO′


--------------------------------------------------------------------------------


-- `_⇓` is the CBV termination relation.
_⇓ : ∀ {g} → Term g → Set
M ⇓ = Σ (Term _) (\ M′ → M ⇓ M′)


-- Small-step reduction IN REVERSE preserves termination.
-- Reversed small-step reduction is halt-preserving.
hpr↦ : ∀ {g} → {M M′ : Term g}
              → M ↦ M′ → M′ ⇓
              → M ⇓
hpr↦ M↦M′ (M″ , M′⇓M″) = M″ , big-step M↦M′ M′⇓M″


-- Small-step reduction preserves termination.
-- Small-step reduction is halt-preserving.
hp↦ : ∀ {g} → {M M′ : Term g}
             → M ↦ M′ → M ⇓
             → M′ ⇓
hp↦ M↦M′ (M″ , M′⇓M″) = M″ , big-unstep M↦M′ M′⇓M″


-- If `M` terminates and `N` terminates, then `PAIR M N` terminates.
halt-pair : ∀ {g} → {M N : Term g}
                  → M ⇓ → N ⇓
                  → PAIR M N ⇓
halt-pair (M′ , M⇓M′) (N′ , N⇓N′) = PAIR M′ N′ , big-red-pair M⇓M′ N⇓N′


-- If `M` reduces to `PAIR M′ N′`, then `FST M` terminates.
halt-fst-pair : ∀ {g} → {M M′ N′ : Term g} → {{_ : Val M′}} {{_ : Val N′}}
                      → M ⤅ PAIR M′ N′
                      → FST M ⇓
halt-fst-pair {M′ = M′} M⤅PAIR = M′ , big-red-fst-pair M⤅PAIR


-- If `M` reduces to `PAIR M′ N′`, then `SND M` terminates.
halt-snd-pair : ∀ {g} → {M M′ N′ : Term g} → {{_ : Val M′}} {{_ : Val N′}}
                      → M ⤅ PAIR M′ N′
                      → SND M ⇓
halt-snd-pair {N′ = N′} M⤅PAIR = N′ , big-red-snd-pair M⤅PAIR


-- If `M` reduces to `TRUE` and `N` terminates, then `IF M N O` terminates.
halt-if-true : ∀ {g} → {M N O : Term g}
                     → M ⤅ TRUE → N ⇓
                     → IF M N O ⇓
halt-if-true M⤅TRUE (N′ , N⇓N′) = N′ , big-red-if-true M⤅TRUE N⇓N′


-- If `M` reduces to `FALSE` and `O` terminates, then `IF M N O` terminates.
halt-if-false : ∀ {g} → {M N O : Term g}
                      → M ⤅ FALSE → O ⇓
                      → IF M N O ⇓
halt-if-false M⤅FALSE (O′ , O⇓O′) = O′ , big-red-if-false M⤅FALSE O⇓O′


-- Every well-typed term terminates.
-- Impossible without a stronger induction hypothesis.
{-
halt : ∀ {M A} → ∙ ⊢ M ⦂ A
               → M ⇓
halt (var ())
halt (lam 𝒟)    = LAM _ , done , val-lam
halt (app 𝒟 ℰ)  = {!!}
halt unit       = UNIT  , done , val-unit
halt (pair 𝒟 ℰ) = halt-pair (halt 𝒟) (halt ℰ)
halt (fst 𝒟)    with halt 𝒟
halt (fst 𝒟)    | M′       , M⤅M′   , VM′       with tp⤅ M⤅M′ 𝒟
halt (fst 𝒟)    | LAM _    , _       , val-lam   | ()
halt (fst 𝒟)    | UNIT     , _       , val-unit  | ()
halt (fst 𝒟)    | PAIR _ _ , M⤅PAIR , val-pair  | pair _ _ = halt-fst-pair M⤅PAIR
halt (fst 𝒟)    | TRUE     , _       , val-true  | ()
halt (fst 𝒟)    | FALSE    , _       , val-false | ()
halt (snd 𝒟)    with halt 𝒟
halt (snd 𝒟)    | M′       , M⤅M′   , VM′       with tp⤅ M⤅M′ 𝒟
halt (snd 𝒟)    | LAM _    , _       , val-lam   | ()
halt (snd 𝒟)    | UNIT     , _       , val-unit  | ()
halt (snd 𝒟)    | PAIR _ _ , M⤅PAIR , val-pair  | pair _ _ = halt-snd-pair M⤅PAIR
halt (snd 𝒟)    | TRUE     , _       , val-true  | ()
halt (snd 𝒟)    | FALSE    , _       , val-false | ()
halt true       = TRUE  , done , val-true
halt false      = FALSE , done , val-false
halt (if 𝒟 ℰ ℱ) with halt 𝒟
halt (if 𝒟 ℰ ℱ) | M′       , M⤅M′    , VM′       with tp⤅ M⤅M′ 𝒟
halt (if 𝒟 ℰ ℱ) | LAM _    , _        , val-lam   | ()
halt (if 𝒟 ℰ ℱ) | UNIT     , _        , val-unit  | ()
halt (if 𝒟 ℰ ℱ) | PAIR _ _ , _        , val-pair  | ()
halt (if 𝒟 ℰ ℱ) | TRUE     , M⤅TRUE  , val-true  | true  = halt-if-true M⤅TRUE (halt ℰ)
halt (if 𝒟 ℰ ℱ) | FALSE    , M⤅FALSE , val-false | false = halt-if-false M⤅FALSE (halt ℱ)
-}


--------------------------------------------------------------------------------
