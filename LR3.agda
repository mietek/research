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


{-
-- Value non-reduction.
vnr : ∀ {g} → {M : Val g} {M′ : Term g}
            → ¬ (Val.term M ↦ M′)
vnr {M = val (LAM M) {{iv-LAM}}}   M↦M′ = {!!}
vnr {M = val TRUE    {{iv-TRUE}}}  M↦M′ = {!!}
vnr {M = val FALSE   {{iv-FALSE}}} M↦M′ = {!!}


-- Determinism.
uniq↦ : ∀ {g} → {M M′₁ M′₂ : Term g}
               → M ↦ M′₁ → M ↦ M′₂
               → M′₁ ≡ M′₂
uniq↦ red-APP-LAM         M↦M′₂ = {!!}
uniq↦ red-IF-TRUE         M↦M′₂ = {!!}
uniq↦ red-IF-FALSE        M↦M′₂ = {!!}
uniq↦ (red-cong E M↦M′₁) M↦M′₂ = {!!}

uniq⤅ : ∀ {g} → {M M′₁ M′₂ : Term g}
               → M ⤅ M′₁ → M ⤅ M′₂
               → M′₁ ≡ M′₂
uniq⤅ done                   done                   = refl
uniq⤅ done                   (step M↦M″₂ M″₂⤅M′₂) = {!!}
uniq⤅ (step M↦M″₁ M″₁⤅M′₁) done                   = {!!}
uniq⤅ (step M↦M″₁ M″₁⤅M′₁) (step M↦M″₂ M″₂⤅M′₂) = {!!}
-}


foo : ∀ {g} → {M M′ : Term g}
            → M ⤅ M′
            → M ≡ M′ ⊎ Σ (Term g) (\ M″ → M ↦ M″ × M″ ⤅ M′)
foo done                = inj₁ refl
foo (step M↦M″ M″⤅M′) = inj₂ (_ , (M↦M″ , M″⤅M′))


uniq↦ : ∀ {g} → {M M′₁ M′₂ : Term g} → M ↦ M′₁ → M ↦ M′₂ → M′₁ ≡ M′₂
uniq↦ {M = VAR I}    {M′₁} {M′₂} M↦M′₁ M↦M′₂ = {!!}
uniq↦ {M = LAM M}    {M′₁} {M′₂} M↦M′₁ M↦M′₂ = {!!}
uniq↦ {M = APP M N}  {M′₁} {M′₂} M↦M′₁ M↦M′₂ = {!!}
uniq↦ {M = TRUE}     {M′₁} {M′₂} M↦M′₁ M↦M′₂ = {!!}
uniq↦ {M = FALSE}    {M′₁} {M′₂} M↦M′₁ M↦M′₂ = {!!}
uniq↦ {M = IF M N O} {M′₁} {M′₂} M↦M′₁ M↦M′₂ = {!!}


bar : ∀ {g} → {M M′ M″ : Term g}
            → M ↦ M′ → M ⤅ M″ → {{_ : ¬ (M ≡ M″)}}
            → M′ ⤅ M″
bar M↦M′ done                {{p}} = refl ↯ p
bar M↦M′ (step M↦M° M°⤅M″) = {!!}


oops : ∀ {g} → {M M′ M″ : Term g}
             → M ↦ M′ → M ⤅ M″
             → M′ ⤅ M″
oops M↦M′ done                = {!!}
oops M↦M′ (step M↦M° M°⤅M″) = {!!}


--------------------------------------------------------------------------------


red-cong-APP-LAM : ∀ {g} → {M N N′ : Term g} {M′ : Term (suc g)}
                         → M ⤅ LAM M′ → N ⤅ N′
                         → APP (LAM M′) N ⤅ CUT N′ M′
red-cong-APP-LAM M⤅LAM-M′ N⤅N′ = {!!}


halt-APP : ∀ {g} → {M N : Term g} {M′ : Term (suc g)}
                 → M ⤅ LAM M′ → M′ ⇓ → N ⇓
                 → APP M N ⇓
halt-APP M⤅LAM-M′ M′⇓ N⇓ = {!!}


--------------------------------------------------------------------------------


SN : Term 0 → Type → Set
SN M 𝔹       = ∙ ⊢ M ⦂ 𝔹 × M ⇓
SN M (A ⊃ B) = ∙ ⊢ M ⦂ A ⊃ B × M ⇓ × (∀ {N} → SN N A → SN (APP M N) B)


derp : ∀ {A M} → SN M A
               → ∙ ⊢ M ⦂ A
derp {𝔹}     (𝒟 , M⇓)     = 𝒟
derp {A ⊃ B} (𝒟 , M⇓ , f) = 𝒟


sn-lem₁ : ∀ {A M M′} → M ↦ M′ → ∙ ⊢ M ⦂ A → SN M′ A
                     → SN M A
sn-lem₁ {𝔹}     M↦M′ 𝒟 (𝒟′ , (M″ , M′⤅M″))     = 𝒟 , (M″ , step M↦M′ M′⤅M″)
sn-lem₁ {A ⊃ B} M↦M′ 𝒟 (𝒟′ , (M″ , M′⤅M″) , f) = 𝒟 , (M″ , step M↦M′ M′⤅M″) , (\ s →
                                                     sn-lem₁ (red-cong (ec-fun-APP ec-[] _) M↦M′) (app 𝒟 (derp s)) (f s))


sn-lem₂ : ∀ {A M M′} → M ↦ M′ → ∙ ⊢ M ⦂ A → SN M A
                     → SN M′ A
sn-lem₂ {𝔹}     M↦M′ 𝒟 (_ , (M″ , M⤅M″))     = tp↦ M↦M′ 𝒟 , (M″ , oops M↦M′ M⤅M″)
sn-lem₂ {A ⊃ B} M↦M′ 𝒟 (_ , (M″ , M⤅M″) , f) = tp↦ M↦M′ 𝒟 , (M″ , oops M↦M′ M⤅M″) , (\ s →
                                                   sn-lem₂ (red-cong (ec-fun-APP ec-[] _) M↦M′) (app 𝒟 (derp s)) (f s))


sn-IF-TRUE : ∀ {C M N O} → M ⤅ TRUE → ∙ ⊢ M ⦂ 𝔹 → SN N C → ∙ ⊢ O ⦂ C
                         → SN (IF M N O) C
sn-IF-TRUE {𝔹}     M⤅TRUE 𝒟 (ℰ , N⇓)     ℱ = if 𝒟 ℰ ℱ , halt-IF-TRUE M⤅TRUE N⇓
sn-IF-TRUE {A ⊃ B} M⤅TRUE 𝒟 (ℰ , N⇓ , f) ℱ = if 𝒟 ℰ ℱ , halt-IF-TRUE M⤅TRUE N⇓ , (\ s →
                                                {!!}) -- SN (APP (IF M N O) P) B


sn-IF-FALSE : ∀ {C M N O} → M ⤅ FALSE → ∙ ⊢ M ⦂ 𝔹 → ∙ ⊢ N ⦂ C → SN O C
                           → SN (IF M N O) C
sn-IF-FALSE {𝔹}     M⤅FALSE 𝒟 ℰ (ℱ , O⇓)     = if 𝒟 ℰ ℱ , halt-IF-FALSE M⤅FALSE O⇓
sn-IF-FALSE {A ⊃ B} M⤅FALSE 𝒟 ℰ (ℱ , O⇓ , f) = if 𝒟 ℰ ℱ , halt-IF-FALSE M⤅FALSE O⇓ , (\ s →
                                                  {!!}) -- SN (APP (IF M N O) P) B


--------------------------------------------------------------------------------


SNs : ∀ {g} → Terms 0 g → Types g → Set
SNs ∙       ∙       = ⊤
SNs (τ , M) (Γ , A) = SNs τ Γ × SN M A


derps : ∀ {g} → {τ : Terms 0 g} {Γ : Types g}
              → SNs τ Γ
              → ∙ ⊢ τ ⦂ Γ all
derps {τ = ∙}     {∙}     ∙       = ∙
derps {τ = τ , M} {Γ , A} (σ , s) = derps σ , derp s


tp-SUB : ∀ {g M A} → {τ : Terms 0 g} {Γ : Types g}
                   → SNs τ Γ → Γ ⊢ M ⦂ A
                   → ∙ ⊢ SUB τ M ⦂ A
tp-SUB σ 𝒟 = sub (derps σ) 𝒟


sn-SUB : ∀ {g M A} → {τ : Terms 0 g} {Γ : Types g}
                   → SNs τ Γ → Γ ⊢ M ⦂ A
                   → SN (SUB τ M) A
sn-SUB σ (var i)        = {!!}
sn-SUB σ (lam 𝒟)        = lam (sub (lifts (derps σ)) 𝒟) , (val (LAM _) , done) , (\ s →
                            {!!}) -- SN (APP (LAM (SUB (LIFTS τ) M)) N) B
sn-SUB σ (app 𝒟 ℰ)      = {!!}
sn-SUB σ true           = true , (val TRUE , done)
sn-SUB σ false          = false , (val FALSE , done)
sn-SUB σ (if {C} 𝒟 ℰ ℱ) with sn-SUB σ 𝒟
sn-SUB σ (if {C} 𝒟 ℰ ℱ) | 𝒟′ , (M′ , SUB-M⤅M′) with tp⤅ SUB-M⤅M′ 𝒟′
sn-SUB σ (if {C} 𝒟 ℰ ℱ) | 𝒟′ , (val (LAM M″) {{iv-LAM}}   , SUB-M⤅M′)    | ()
sn-SUB σ (if {C} 𝒟 ℰ ℱ) | 𝒟′ , (val TRUE     {{iv-TRUE}}  , SUB-M⤅TRUE)  | true  = sn-IF-TRUE {C} SUB-M⤅TRUE 𝒟′ (sn-SUB σ ℰ) (tp-SUB σ ℱ)
sn-SUB σ (if {C} 𝒟 ℰ ℱ) | 𝒟′ , (val FALSE    {{iv-FALSE}} , SUB-M⤅FALSE) | false = sn-IF-FALSE {C} SUB-M⤅FALSE 𝒟′ (tp-SUB σ ℰ) (sn-SUB σ ℱ)


--------------------------------------------------------------------------------


private
  module Impossible3
    where
      sn : ∀ {M A} → ∙ ⊢ M ⦂ A
                   → SN M A
      sn (var ())
      sn (lam 𝒟)        = lam 𝒟 , (val (LAM _) , done) , (\ s → {!!}) -- SN (APP (LAM M) N) B
      sn (app 𝒟 ℰ)      = {!!} -- SN (APP M N) A
      sn true           = true , (val TRUE , done)
      sn false          = false , (val FALSE , done)
      sn (if {C} 𝒟 ℰ ℱ) with sn 𝒟
      sn (if {C} 𝒟 ℰ ℱ) | _ , (M′ , M⤅M′) with tp⤅ M⤅M′ 𝒟
      sn (if {C} 𝒟 ℰ ℱ) | _ , (val (LAM M″) {{iv-LAM}}   , M⤅LAM-M″) | ()
      sn (if {C} 𝒟 ℰ ℱ) | _ , (val TRUE     {{iv-TRUE}}  , M⤅TRUE)   | true  = sn-IF-TRUE {C} M⤅TRUE 𝒟 (sn ℰ) ℱ
      sn (if {C} 𝒟 ℰ ℱ) | _ , (val FALSE    {{iv-FALSE}} , M⤅FALSE)  | false = sn-IF-FALSE {C} M⤅FALSE 𝒟 ℰ (sn ℱ)


sn : ∀ {M A} → ∙ ⊢ M ⦂ A
             → SN M A
sn {M} {A} 𝒟 = subst (\ M′ → SN M′ A) (id-SUB M) (sn-SUB ∙ 𝒟)


halt-sn : ∀ {A M} → SN M A
                  → M ⇓
halt-sn {𝔹}     (𝒟 , M⇓)     = M⇓
halt-sn {A ⊃ B} (𝒟 , M⇓ , f) = M⇓


halt : ∀ {A M} → ∙ ⊢ M ⦂ A
               → M ⇓
halt {A} 𝒟 = halt-sn {A} (sn 𝒟)


-- --------------------------------------------------------------------------------


-- SNs : ∀ {g} → Vals 0 g → Types g → Set
-- SNs (vals ∙)                       ∙       = ⊤
-- SNs (vals (τ , M) {{av-τ , iv-M}}) (Γ , A) = SNs (vals τ {{av-τ}}) Γ × SN M A


-- derps : ∀ {g} → {τ : Vals 0 g} {Γ : Types g}
--               → SNs τ Γ
--               → ∙ ⊢ Vals.terms τ ⦂ Γ all
-- derps {τ = vals ∙}                       {∙}     ∙       = ∙
-- derps {τ = vals (τ , M) {{av-τ , iv-M}}} {Γ , A} (σ , s) = derps σ , derp s


-- tp-SUB : ∀ {g M A} → {τ : Vals 0 g} {Γ : Types g}
--                    → SNs τ Γ → Γ ⊢ M ⦂ A
--                    → ∙ ⊢ SUB (Vals.terms τ) M ⦂ A
-- tp-SUB σ 𝒟 = sub (derps σ) 𝒟


-- sn-lem₁ : ∀ {A M M′} → M ↦ M′ → ∙ ⊢ M ⦂ A → SN M′ A
--                      → SN M A
-- sn-lem₁ {𝔹}     M↦M′ 𝒟 (𝒟′ , (M″ , M′⤅M″))     = 𝒟 , (M″ , step M↦M′ M′⤅M″)
-- sn-lem₁ {A ⊃ B} M↦M′ 𝒟 (𝒟′ , (M″ , M′⤅M″) , f) =
--   𝒟 , (M″ , step M↦M′ M′⤅M″) , (\ s → sn-lem₁ (red-cong (ec-fun-APP ec-[] _) M↦M′)
--                                                  (app 𝒟 (derp s)) (f s))


-- sn-lem₂ : ∀ {A M M′} → M ↦ M′ → ∙ ⊢ M ⦂ A → SN M A
--                      → SN M′ A
-- sn-lem₂ {𝔹}     M↦M′ 𝒟 (_ , (M″ , M⤅M″))     = {!!}
-- sn-lem₂ {A ⊃ B} M↦M′ 𝒟 (_ , (M″ , M⤅M″) , f) = {!!}


-- sn-SUB : ∀ {g M A} → {τ : Vals 0 g} {Γ : Types g}
--                    → SNs τ Γ → Γ ⊢ M ⦂ A
--                    → SN (SUB (Vals.terms τ) M) A
-- sn-SUB σ (var i)    = {!!}
-- sn-SUB σ (lam 𝒟)    = {!!}
-- sn-SUB σ (app 𝒟 ℰ)  = {!!}
-- sn-SUB σ true       = true , (val TRUE , done)
-- sn-SUB σ false      = false , (val FALSE , done)
-- sn-SUB σ (if 𝒟 ℰ ℱ) = {!!}


-- --------------------------------------------------------------------------------
