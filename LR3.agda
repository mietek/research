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


-- TODO: Improve naming for all `id-cons-*` lemmas and this one.
lem-cons-SUBS : ∀ {g n m} → (τ : Terms g n) (M : Term g) (υ : Terms n m)
                          → (SUBS (τ , M) ∘ LIFTS) υ ≡ SUBS τ υ , M
lem-cons-SUBS τ M υ = (_, M) & id-cons-WKS-SUBS τ M υ


comp-CUT-SUB-LIFTS : ∀ {g n} → (N : Term g) (τ : Terms g n) (M : Term (suc n))
                             → SUB (τ , N) M ≡ (CUT N ∘ SUB (LIFTS τ)) M
comp-CUT-SUB-LIFTS N τ M = (\ τ′ → SUB τ′ M) & ( (_, N) & lid-SUBS τ ⁻¹
                                                ⋮ lem-cons-SUBS IDS N τ ⁻¹
                                                )
                         ⋮ comp-SUB (IDS , N) (LIFTS τ) M


--------------------------------------------------------------------------------


SN : Term 0 → Type → Set
SN M 𝔹       = ∙ ⊢ M ⦂ 𝔹 × M ⇓
SN M (A ⊃ B) = ∙ ⊢ M ⦂ A ⊃ B × M ⇓ × (∀ {N} → SN N A → SN (APP M N) B)


derp : ∀ {A M} → SN M A
               → ∙ ⊢ M ⦂ A
derp {𝔹}     (𝒟 , M⇓)     = 𝒟
derp {A ⊃ B} (𝒟 , M⇓ , f) = 𝒟


-- Forward reduction preserves SN.
sn-lem₁ : ∀ {A M M′} → M ↦ M′ → ∙ ⊢ M ⦂ A → SN M′ A
                     → SN M A
sn-lem₁ {𝔹}     M↦M′ 𝒟 (𝒟′ , (M″ , M′⤅M″))     = 𝒟 , (M″ , step M↦M′ M′⤅M″)
sn-lem₁ {A ⊃ B} M↦M′ 𝒟 (𝒟′ , (M″ , M′⤅M″) , f) = 𝒟 , (M″ , step M↦M′ M′⤅M″) , (\ s →
                                                     sn-lem₁ (red-cong (ec-fun-APP ec-[] _) M↦M′ {{refl}} {{refl}}) (app 𝒟 (derp s)) (f s))


oops : ∀ {g} → {M M′ M″ : Term g}
             → M ↦ M′ → M ⤅ M″
             → M′ ⤅ M″
oops M↦M′ done                = {!!}
oops M↦M′ (step M↦M° M°⤅M″) = {!!}


-- Backward reduction preserves SN.
sn-lem₂ : ∀ {A M M′} → M ↦ M′ → ∙ ⊢ M ⦂ A → SN M A
                     → SN M′ A
sn-lem₂ {𝔹}     M↦M′ 𝒟 (_ , (M″ , M⤅M″))     = tp↦ M↦M′ 𝒟 , (M″ , oops M↦M′ M⤅M″)
sn-lem₂ {A ⊃ B} M↦M′ 𝒟 (_ , (M″ , M⤅M″) , f) = tp↦ M↦M′ 𝒟 , (M″ , oops M↦M′ M⤅M″) , (\ s →
                                                   sn-lem₂ (red-cong (ec-fun-APP ec-[] _) M↦M′ {{refl}} {{refl}}) (app 𝒟 (derp s)) (f s))


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
SNs τ Γ = All (\ { (M , A) → SN M A }) (zip τ Γ)


derps : ∀ {g} → {τ : Terms 0 g} {Γ : Types g}
              → SNs τ Γ
              → ∙ ⊢ τ ⦂ Γ all
derps σ = maps derp σ


-- Substitution lemma.
tp-SUB : ∀ {g M A} → {τ : Terms 0 g} {Γ : Types g}
                   → SNs τ Γ → Γ ⊢ M ⦂ A
                   → ∙ ⊢ SUB τ M ⦂ A
tp-SUB σ 𝒟 = sub (derps σ) 𝒟


-- TODO: Clean this up
halt-APP-LAM : ∀ {g N} → {τ : Terms 0 g}
                       → (M : Term (suc g)) → SUB (τ , N) M ⇓
                       → APP (LAM (SUB (LIFTS τ) M)) N ⇓
halt-APP-LAM {N = N} {τ} M (M′ , SUB-M⤅M′) rewrite comp-CUT-SUB-LIFTS N τ M
  = M′ , step (red-APP-LAM {M = SUB (LIFTS τ) M} {N} {{refl}}) SUB-M⤅M′


sn-APP-LAM : ∀ {B g M N A} → {τ : Terms 0 g} {Γ : Types g}
                           → SNs τ Γ → Γ , A ⊢ M ⦂ B → ∙ ⊢ N ⦂ A → SN (SUB (τ , N) M) B
                           → SN (APP (LAM (SUB (LIFTS τ) M)) N) B
sn-APP-LAM {𝔹}       {M = M} σ 𝒟 ℰ (𝒟′ , SUB-M⇓)     = app (tp-SUB σ (lam 𝒟)) ℰ ,
                                                       halt-APP-LAM M SUB-M⇓
sn-APP-LAM {B₁ ⊃ B₂} {M = M} σ 𝒟 ℰ (𝒟′ , SUB-M⇓ , f) = app (tp-SUB σ (lam 𝒟)) ℰ ,
                                                       halt-APP-LAM M SUB-M⇓ ,
                                                       (\ s′ → {!!})


sn-SUB : ∀ {g M A} → {τ : Terms 0 g} {Γ : Types g}
                   → SNs τ Γ → Γ ⊢ M ⦂ A
                   → SN (SUB τ M) A
sn-SUB σ (var i)        = get σ (zip∋₂ i)
sn-SUB σ (lam 𝒟)        = tp-SUB σ (lam 𝒟) , (val (LAM _) , done) , (\ s → sn-APP-LAM σ 𝒟 (derp s) (sn-SUB (σ , s) 𝒟))
sn-SUB σ (app 𝒟 ℰ)      with sn-SUB σ 𝒟
sn-SUB σ (app 𝒟 ℰ)      | 𝒟′ , (M′ , SUB-M⤅M′) , f = f (sn-SUB σ ℰ)
sn-SUB σ true           = true , (val TRUE , done)
sn-SUB σ false          = false , (val FALSE , done)
sn-SUB σ (if {C} 𝒟 ℰ ℱ) with sn-SUB σ 𝒟
sn-SUB σ (if {C} 𝒟 ℰ ℱ) | 𝒟′ , (M′ , SUB-M⤅M′) with tp⤅ SUB-M⤅M′ 𝒟′
sn-SUB σ (if {C} 𝒟 ℰ ℱ) | 𝒟′ , (val (LAM M″) {{iv-LAM}}   , SUB-M⤅M′)    | ()
sn-SUB σ (if {C} 𝒟 ℰ ℱ) | 𝒟′ , (val TRUE     {{iv-TRUE}}  , SUB-M⤅TRUE)  | true  = sn-IF-TRUE {C} SUB-M⤅TRUE 𝒟′ (sn-SUB σ ℰ) (tp-SUB σ ℱ)
sn-SUB σ (if {C} 𝒟 ℰ ℱ) | 𝒟′ , (val FALSE    {{iv-FALSE}} , SUB-M⤅FALSE) | false = sn-IF-FALSE {C} SUB-M⤅FALSE 𝒟′ (tp-SUB σ ℰ) (sn-SUB σ ℱ)


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


--------------------------------------------------------------------------------
