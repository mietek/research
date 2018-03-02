module LR3 where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec
open import VecLemmas
open import AllVec
open import LR0
open import LR0Lemmas
open import LR1
open import LR2


--------------------------------------------------------------------------------


-- `SN _ A` is the strong normalisation predicate on terms at type `A`.
mutual
  SN : Term 0 → Type → Set
  SN M A = ∙ ⊢ M ⦂ A × M ⇓ × SN! M A

  SN! : Term 0 → Type → Set
  SN! M 𝔹       = ⊤
  SN! M 𝟘       = ⊥
  SN! M 𝟙       = ⊤
  SN! M (A ∧ B) = SN (FST M) A × SN (SND M) B
  SN! M (A ⊃ B) = ∀ {N} → SN N A → SN (APP M N) B


-- Every SN term is well-typed.
derp : ∀ {A M} → SN M A
               → ∙ ⊢ M ⦂ A
derp (𝒟 , M⇓ , s!) = 𝒟


--------------------------------------------------------------------------------


-- `SNs _ Γ` is the strong normalisation predicate on substitutions at all types `Γ`.
SNs : ∀ {g} → (τ : Terms 0 g) → Types g → Set
SNs τ Γ = All (\ { (M , A) → SN M A }) (zip τ Γ)


-- Every SN substitution is well-typed.
derps : ∀ {g} → {τ : Terms 0 g} {Γ : Types g}
              → SNs τ Γ
              → ∙ ⊢ τ ⦂ Γ all
derps σ = maps derp σ


--------------------------------------------------------------------------------


-- Small-step reduction IN REVERSE preserves SN.
mutual
  snpr↦ : ∀ {A M M′} → M ↦ M′ → ∙ ⊢ M ⦂ A → SN M′ A
                      → SN M A
  snpr↦ M↦M′ 𝒟 (𝒟′ , M′⇓ , s!′) = 𝒟 , hpr↦ M↦M′ M′⇓ , sn!pr↦ M↦M′ 𝒟 s!′

  sn!pr↦ : ∀ {A M M′} → M ↦ M′ → ∙ ⊢ M ⦂ A → SN! M′ A
                       → SN! M A
  sn!pr↦ {𝔹}     M↦M′ 𝒟 ∙         = ∙
  sn!pr↦ {𝟘}     M↦M′ 𝒟 ()
  sn!pr↦ {𝟙}     M↦M′ 𝒟 ∙         = ∙
  sn!pr↦ {A ∧ B} M↦M′ 𝒟 (s₁ , s₂) = snpr↦ (cong-fst M↦M′) (fst 𝒟) s₁ , snpr↦ (cong-snd M↦M′) (snd 𝒟) s₂
  sn!pr↦ {A ⊃ B} M↦M′ 𝒟 f s       = snpr↦ (cong-app₁ M↦M′) (app 𝒟 (derp s)) (f s)


-- Iterated small-step reduction IN REVERSE preserves SN.
snpr⤅ : ∀ {A M M′} → M ⤅ M′ → ∙ ⊢ M ⦂ A → SN M′ A
                    → SN M A
snpr⤅ done                𝒟 s = s
snpr⤅ (step M↦M″ M″⤅M′) 𝒟 s = snpr↦ M↦M″ 𝒟 (snpr⤅ M″⤅M′ (tp↦ M↦M″ 𝒟) s)


-- Big-step reduction IN REVERSE preserves SN.
snpr⇓ : ∀ {A M M′} → M ⇓ M′ → ∙ ⊢ M ⦂ A → SN M′ A
                   → SN M A
snpr⇓ (M⤅M′ , VM′) 𝒟 s = snpr⤅ M⤅M′ 𝒟 s


--------------------------------------------------------------------------------


-- Small-step reduction preserves SN.
mutual
  snp↦ : ∀ {A M M′} → M ↦ M′ → ∙ ⊢ M ⦂ A → SN M A
                     → SN M′ A
  snp↦ M↦M′ 𝒟 (_ , M⇓ , s!) = tp↦ M↦M′ 𝒟 , hp↦ M↦M′ M⇓ , sn!p↦ M↦M′ 𝒟 s!

  sn!p↦ : ∀ {A M M′} → M ↦ M′ → ∙ ⊢ M ⦂ A → SN! M A
                      → SN! M′ A
  sn!p↦ {𝔹}     M↦M′ 𝒟 ∙         = ∙
  sn!p↦ {𝟘}     M↦M′ 𝒟 ()
  sn!p↦ {𝟙}     M↦M′ 𝒟 ∙         = ∙
  sn!p↦ {A ∧ B} M↦M′ 𝒟 (s₁ , s₂) = snp↦ (cong-fst M↦M′) (fst 𝒟) s₁ , snp↦ (cong-snd M↦M′) (snd 𝒟) s₂
  sn!p↦ {A ⊃ B} M↦M′ 𝒟 f s       = snp↦ (cong-app₁ M↦M′) (app 𝒟 (derp s)) (f s)


-- Iterated small-step reduction preserves SN.
snp⤅ : ∀ {A M M′} → M ⤅ M′ → ∙ ⊢ M ⦂ A → SN M A
                   → SN M′ A
snp⤅ done                𝒟 s = s
snp⤅ (step M↦M″ M″⤅M′) 𝒟 s = snp⤅ M″⤅M′ (tp↦ M↦M″ 𝒟) (snp↦ M↦M″ 𝒟 s)


-- Big-step reduction preserves SN.
snp⇓ : ∀ {A M M′} → M ⇓ M′ → ∙ ⊢ M ⦂ A → SN M A
                  → SN M′ A
snp⇓ (M⤅M′ , VM′) 𝒟 s = snp⤅ M⤅M′ 𝒟 s


--------------------------------------------------------------------------------


-- If `M` is SN at type `A` and `N` is SN at type `B`, then `PAIR M N` is SN at type `A ∧ B`.
sn-pair : ∀ {A B M N} → SN M A → SN N B
                      → SN (PAIR M N) (A ∧ B)
sn-pair s₁@(𝒟 , M⇓@(M′ , M⇓M′@(M⤅M′ , VM′)) , s!₁) s₂@(ℰ , N⇓@(N′ , N⇓N′@(N⤅N′ , VN′)) , s!₂)
  = pair 𝒟 ℰ ,
    halt-pair M⇓ N⇓ ,
    snpr⇓ (big-red-fst-pair {{VM′}} {{VN′}} (congs-pair {{VM′}} {{VN′}} M⤅M′ N⤅N′)) (fst (pair 𝒟 ℰ)) (snp⤅ M⤅M′ 𝒟 s₁) ,
    snpr⇓ (big-red-snd-pair {{VM′}} {{VN′}} ((congs-pair {{VM′}} {{VN′}} M⤅M′ N⤅N′))) (snd (pair 𝒟 ℰ)) (snp⤅ N⤅N′ ℰ s₂)


-- If `M` is SN at type `A ∧ B`, then `FST M` is SN at type `A`.
mutual
  sn-fst : ∀ {A B M} → SN M (A ∧ B)
                     → SN (FST M) A
  sn-fst (𝒟 , M⇓ , s!) = fst 𝒟 , halt-fst 𝒟 M⇓ , sn!-fst s!

  sn!-fst : ∀ {A B M} → SN! M (A ∧ B)
                      → SN! (FST M) A
  sn!-fst {𝔹}       _                      = ∙
  sn!-fst {𝟘}       ()
  sn!-fst {𝟙}       _                      = ∙
  sn!-fst {A₁ ∧ A₂} ((ℰ , FST⇓ , s) , _)   = s
  sn!-fst {A₁ ⊃ A₂} ((ℰ , FST⇓ , f) , _) s = f s


-- If `M` is SN at type `A ∧ B`, then `SND M` is SN at type `B`.
mutual
  sn-snd : ∀ {A B M} → SN M (A ∧ B)
                     → SN (SND M) B
  sn-snd (𝒟 , M⇓ , s!) = snd 𝒟 , halt-snd 𝒟 M⇓ , sn!-snd s!

  sn!-snd : ∀ {B A M} → SN! M (A ∧ B)
                      → SN! (SND M) B
  sn!-snd {𝔹}       _                      = ∙
  sn!-snd {𝟘}       ()
  sn!-snd {𝟙}       _                      = ∙
  sn!-snd {B₁ ∧ B₂} (_ , (ℰ , SND⇓ , s))   = s
  sn!-snd {B₁ ⊃ B₂} (_ , (ℰ , SND⇓ , f)) s = f s


-- If `M` is SN at type `𝟘`, then `ABORT M` is SN at type `C`.
mutual
  sn-abort : ∀ {C M} → SN M 𝟘
                     → SN (ABORT M) C
  sn-abort {C} (𝒟 , M⇓ , s!) = abort 𝒟 , halt-abort 𝒟 M⇓ , sn!-abort {C} s!

  sn!-abort : ∀ {C M} → SN! M 𝟘
                      → SN! (ABORT M) C
  sn!-abort {𝔹}     ()
  sn!-abort {𝟘}     ()
  sn!-abort {𝟙}     ()
  sn!-abort {A ∧ B} ()
  sn!-abort {A ⊃ B} () _


-- If `M` reduces to `TRUE` and `N` is SN at type `C`, then `IF M N O` is SN at type `C`.
mutual
  sn-if-true : ∀ {C M N O} → M ⤅ TRUE → ∙ ⊢ M ⦂ 𝔹 → SN N C → ∙ ⊢ O ⦂ C
                           → SN (IF M N O) C
  sn-if-true M⤅TRUE 𝒟 (ℰ , N⇓ , s!) ℱ = if 𝒟 ℰ ℱ , halt-if-true M⤅TRUE N⇓ , sn!-if-true M⤅TRUE 𝒟 ℰ ℱ s!

  sn!-if-true : ∀ {C M N O} → M ⤅ TRUE → ∙ ⊢ M ⦂ 𝔹 → ∙ ⊢ N ⦂ C → ∙ ⊢ O ⦂ C → SN! N C
                            → SN! (IF M N O) C
  sn!-if-true {𝔹}     M⤅TRUE 𝒟 ℰ ℱ ∙         = ∙
  sn!-if-true {𝟘}     M⤅TRUE 𝒟 ℰ ℱ ()
  sn!-if-true {𝟙}     M⤅TRUE 𝒟 ℰ ℱ ∙         = ∙
  sn!-if-true {A ∧ B} M⤅TRUE 𝒟 ℰ ℱ (s₁ , s₂) = snpr⤅ (congs-fst (reds-if-true M⤅TRUE done)) (fst (if 𝒟 ℰ ℱ)) s₁ ,
                                                snpr⤅ (congs-snd (reds-if-true M⤅TRUE done)) (snd (if 𝒟 ℰ ℱ)) s₂
  sn!-if-true {A ⊃ B} M⤅TRUE 𝒟 ℰ ℱ f s       = snpr⤅ (congs-app₁ (reds-if-true M⤅TRUE done)) (app (if 𝒟 ℰ ℱ) (derp s)) (f s)


-- If `M` reduces to `FALSE` and `O` is SN at type `C`, then `IF M N O` is SN at type `C`.
mutual
  sn-if-false : ∀ {C M N O} → M ⤅ FALSE → ∙ ⊢ M ⦂ 𝔹 → ∙ ⊢ N ⦂ C → SN O C
                            → SN (IF M N O) C
  sn-if-false M⤅FALSE 𝒟 ℰ (ℱ , N⇓ , s!) = if 𝒟 ℰ ℱ , halt-if-false M⤅FALSE N⇓ , sn!-if-false M⤅FALSE 𝒟 ℰ ℱ s!

  sn!-if-false : ∀ {C M N O} → M ⤅ FALSE → ∙ ⊢ M ⦂ 𝔹 → ∙ ⊢ N ⦂ C → ∙ ⊢ O ⦂ C → SN! O C
                             → SN! (IF M N O) C
  sn!-if-false {𝔹}     M⤅FALSE 𝒟 ℰ ℱ ∙         = ∙
  sn!-if-false {𝟘}     M⤅FALSE 𝒟 ℰ ℱ ()
  sn!-if-false {𝟙}     M⤅FALSE 𝒟 ℰ ℱ ∙         = ∙
  sn!-if-false {A ∧ B} M⤅FALSE 𝒟 ℰ ℱ (s₁ , s₂) = snpr⤅ (congs-fst (reds-if-false M⤅FALSE done)) (fst (if 𝒟 ℰ ℱ)) s₁ ,
                                                  snpr⤅ (congs-snd (reds-if-false M⤅FALSE done)) (snd (if 𝒟 ℰ ℱ)) s₂
  sn!-if-false {A ⊃ B} M⤅FALSE 𝒟 ℰ ℱ f s       = snpr⤅ (congs-app₁ (reds-if-false M⤅FALSE done)) (app (if 𝒟 ℰ ℱ) (derp s)) (f s)


--------------------------------------------------------------------------------


-- The fundamental theorem and the troublecome `lam` case.
-- TODO: Clean this up.


gen-red-app-lam : ∀ {g M N} → {τ : Terms 0 g} → {{_ : Val N}}
                            → APP (LAM (SUB (LIFTS τ) M)) N ↦ SUB (τ , N) M
gen-red-app-lam {M = M} {N} {τ} rewrite simp-CUT-SUB N τ M ⁻¹ = red app-lam


gen-big-red-app-lam : ∀ {g M M′ N} → {τ : Terms 0 g} → {{_ : Vals τ}} {{_ : Val N}}
                                   → SUB (τ , N) M ⇓ M′
                                   → APP (LAM (SUB (LIFTS τ) M)) N ⇓ M′
gen-big-red-app-lam {M = M} (SUB⤅M′ , VM′) = step (gen-red-app-lam {M = M}) SUB⤅M′ , VM′


gen-halt-app-lam : ∀ {g M N} → {τ : Terms 0 g} → {{_ : Vals τ}} {{_ : Val N}}
                             → SUB (τ , N) M ⇓
                             → APP (LAM (SUB (LIFTS τ) M)) N ⇓
gen-halt-app-lam {M = M} (M′ , SUB⇓M′) = M′ , gen-big-red-app-lam {M = M} SUB⇓M′


mutual
  gen-sn-app-lam : ∀ {B g M N A} → {τ : Terms 0 g} → {{_ : Vals τ}} {{_ : Val N}}
                                 → ∙ ⊢ SUB τ (LAM M) ⦂ A ⊃ B → ∙ ⊢ N ⦂ A → SN (SUB (τ , N) M) B
                                 → SN (APP (LAM (SUB (LIFTS τ) M)) N) B
  gen-sn-app-lam {M = M} 𝒟 ℰ (𝒟′ , SUB⇓ , s!) = app 𝒟 ℰ , gen-halt-app-lam {M = M} SUB⇓ , gen-sn!-app-lam {M = M} 𝒟 ℰ s!

  gen-sn!-app-lam : ∀ {B g M N A} → {τ : Terms 0 g} → {{_ : Vals τ}} {{_ : Val N}}
                                  → ∙ ⊢ SUB τ (LAM M) ⦂ A ⊃ B → ∙ ⊢ N ⦂ A → SN! (SUB (τ , N) M) B
                                  → SN! (APP (LAM (SUB (LIFTS τ) M)) N) B
  gen-sn!-app-lam {𝔹}       {M = M} 𝒟 ℰ ∙         = ∙
  gen-sn!-app-lam {𝟘}       {M = M} 𝒟 ℰ ()
  gen-sn!-app-lam {𝟙}       {M = M} 𝒟 ℰ ∙         = ∙
  gen-sn!-app-lam {B₁ ∧ B₂} {M = M} 𝒟 ℰ (s₁ , s₂) = snpr↦ (cong-fst (gen-red-app-lam {M = M})) (fst (app 𝒟 ℰ)) s₁ ,
                                                    snpr↦ (cong-snd (gen-red-app-lam {M = M})) (snd (app 𝒟 ℰ)) s₂
  gen-sn!-app-lam {B₁ ⊃ B₂} {M = M} 𝒟 ℰ f s       = snpr↦ (cong-app₁ (gen-red-app-lam {M = M})) (app (app 𝒟 ℰ) (derp s)) (f s)


mutual
  gen-sn : ∀ {g M A} → {τ : Terms 0 g} {Γ : Types g} → {{_ : Vals τ}}
                     → SNs τ Γ → Γ ⊢ M ⦂ A
                     → SN (SUB τ M) A
  gen-sn σ (var i)    = get σ (zip∋₂ i)
  gen-sn σ (lam 𝒟)    = let 𝒟′ = sub (derps σ) (lam 𝒟) in
                          𝒟′ , (LAM _ , done , val-lam) , gen-sn-lam σ 𝒟 𝒟′
  gen-sn σ (app 𝒟 ℰ)  with gen-sn σ 𝒟
  gen-sn σ (app 𝒟 ℰ)  | 𝒟′ , M′⇓ , f = f (gen-sn σ ℰ)
  gen-sn σ (pair 𝒟 ℰ) = sn-pair (gen-sn σ 𝒟) (gen-sn σ ℰ)
  gen-sn σ (fst 𝒟)    = sn-fst (gen-sn σ 𝒟)
  gen-sn σ (snd 𝒟)    = sn-snd (gen-sn σ 𝒟)
  gen-sn σ unit       = unit  , (UNIT  , done , val-unit)  , ∙
  gen-sn σ (abort 𝒟)  = sn-abort (gen-sn σ 𝒟)
  gen-sn σ true       = true  , (TRUE  , done , val-true)  , ∙
  gen-sn σ false      = false , (FALSE , done , val-false) , ∙
  gen-sn σ (if 𝒟 ℰ ℱ) with gen-sn σ 𝒟
  gen-sn σ (if 𝒟 ℰ ℱ) | 𝒟′ , (M′       , SUB⤅M′    , VM′)       , ∙ with tp⤅ SUB⤅M′ 𝒟′
  gen-sn σ (if 𝒟 ℰ ℱ) | 𝒟′ , (LAM _    , _          , val-lam)   , ∙ | ()
  gen-sn σ (if 𝒟 ℰ ℱ) | 𝒟′ , (PAIR _ _ , _          , val-pair)  , ∙ | ()
  gen-sn σ (if 𝒟 ℰ ℱ) | 𝒟′ , (UNIT     , _          , val-unit)  , ∙ | ()
  gen-sn σ (if 𝒟 ℰ ℱ) | 𝒟′ , (TRUE     , SUB⤅TRUE  , val-true)  , ∙ | true  = sn-if-true SUB⤅TRUE 𝒟′ (gen-sn σ ℰ) (sub (derps σ) ℱ)
  gen-sn σ (if 𝒟 ℰ ℱ) | 𝒟′ , (FALSE    , SUB⤅FALSE , val-false) , ∙ | false = sn-if-false SUB⤅FALSE 𝒟′ (sub (derps σ) ℰ) (gen-sn σ ℱ)

  gen-sn-lam : ∀ {g M N A B} → {τ : Terms 0 g} {Γ : Types g} → {{_ : Vals τ}}
                             → SNs τ Γ → Γ , A ⊢ M ⦂ B → ∙ ⊢ LAM (SUB (LIFTS τ) M) ⦂ A ⊃ B → SN N A
                             → SN (APP (LAM (SUB (LIFTS τ) M)) N) B
  gen-sn-lam {M = M} {{Vτ}} σ 𝒟 𝒟′ s@(ℰ , (N′ , N⇓N′@(N⤅N′ , VN′)) , s!)
    = let s′ = snp⇓ N⇓N′ ℰ s in
        snpr⤅ (congs-app₂ N⤅N′) (app 𝒟′ ℰ) (gen-sn-app-lam {M = M} {{Vτ}} {{VN′}} 𝒟′ (derp s′) (gen-sn {{Vτ , VN′}} (σ , s′) 𝒟))


--------------------------------------------------------------------------------


-- Every well-typed term is SN.
sn : ∀ {A M} → ∙ ⊢ M ⦂ A
             → SN M A
sn {A} {M} 𝒟 = subst (\ M′ → SN M′ A) (id-SUB M) (gen-sn ∙ 𝒟)


-- Every SN term terminates.
herp : ∀ {A M} → SN M A
               → M ⇓
herp (𝒟 , M⇓ , s!) = M⇓


-- Every well-typed term terminates.
halt : ∀ {A M} → ∙ ⊢ M ⦂ A
               → M ⇓
halt {A} 𝒟 = herp {A} (sn 𝒟)


--------------------------------------------------------------------------------
