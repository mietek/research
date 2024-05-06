module A201802.WIP.LR3NonMutual where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.FinLemmas
open import A201801.Vec
open import A201801.VecLemmas
open import A201801.AllVec

open import A201802.LR0
open import A201802.LR0Lemmas
open import A201802.LR1
open import A201802.LR2 -- TODO: which LR2?


--------------------------------------------------------------------------------


-- -- `SN _ A` is the strong normalisation predicate on terms at type `A`.
-- SN : Term 0 → Type → Set
-- SN M 𝟙       = ∙ ⊢ M ⦂ 𝟙 × M ⇓
-- SN M 𝔹       = ∙ ⊢ M ⦂ 𝔹 × M ⇓
-- SN M (A ⊃ B) = ∙ ⊢ M ⦂ A ⊃ B × M ⇓ × (∀ {N} → SN N A → SN (APP M N) B)


-- -- Every SN term is well-typed.
-- derp : ∀ {A M} → SN M A
--                → ∙ ⊢ M ⦂ A
-- derp {𝟙}     (𝒟 , M⇓)     = 𝒟
-- derp {𝔹}     (𝒟 , M⇓)     = 𝒟
-- derp {A ⊃ B} (𝒟 , M⇓ , f) = 𝒟


-- --------------------------------------------------------------------------------


-- -- Small-step reduction IN REVERSE preserves SN.
-- snpr⤇ : ∀ {A M M′} → M ⤇ M′ → ∙ ⊢ M ⦂ A → SN M′ A
--                     → SN M A
-- snpr⤇ {𝟙}     r 𝒟 (𝒟′ , M⇓)     = 𝒟 , hpr⤇ r M⇓
-- snpr⤇ {𝔹}     r 𝒟 (𝒟′ , M⇓)     = 𝒟 , hpr⤇ r M⇓
-- snpr⤇ {A ⊃ B} r 𝒟 (𝒟′ , M⇓ , f) = 𝒟 , hpr⤇ r M⇓ , (\ s →
--                                      snpr⤇ (cong-APP r) (app 𝒟 (derp s)) (f s))


-- -- Iterated small-step reduction IN REVERSE preserves SN.
-- snpr⤇* : ∀ {A M M′} → M ⤇* M′ → ∙ ⊢ M ⦂ A → SN M′ A
--                      → SN M A
-- snpr⤇* done                 𝒟 s = s
-- snpr⤇* (step M⤇M″ M″⤇*M′) 𝒟 s = snpr⤇ M⤇M″ 𝒟 (snpr⤇* M″⤇*M′ (tp⤇ M⤇M″ 𝒟) s)


-- -- Big-step reduction IN REVERSE preserves SN.
-- snpr⇓ : ∀ {A M M′} → M ⇓ M′ → ∙ ⊢ M ⦂ A → SN M′ A
--                    → SN M A
-- snpr⇓ (M⤇*M′ , VM′) 𝒟 s = snpr⤇* M⤇*M′ 𝒟 s


-- -- IF `M` reduces to `TRUE` and `N` is SN, then `IF M N O` is SN.
-- sn-IF-TRUE : ∀ {C M N O} → M ⤇* TRUE → ∙ ⊢ M ⦂ 𝔹 → SN N C → ∙ ⊢ O ⦂ C
--                          → SN (IF M N O) C
-- sn-IF-TRUE {𝟙}     M⤇*TRUE 𝒟 (ℰ , N⇓)     ℱ = if 𝒟 ℰ ℱ , halt-IF-TRUE M⤇*TRUE N⇓
-- sn-IF-TRUE {𝔹}     M⤇*TRUE 𝒟 (ℰ , N⇓)     ℱ = if 𝒟 ℰ ℱ , halt-IF-TRUE M⤇*TRUE N⇓
-- sn-IF-TRUE {A ⊃ B} M⤇*TRUE 𝒟 (ℰ , N⇓ , f) ℱ = if 𝒟 ℰ ℱ , halt-IF-TRUE M⤇*TRUE N⇓ , (\ s →
--                                                  snpr⤇* (congs-APP (congs-IF-TRUE M⤇*TRUE done)) (app (if 𝒟 ℰ ℱ) (derp s)) (f s))


-- -- IF `M` reduces to `FALSE` and `O` is SN, then `IF M N O` is SN.
-- sn-IF-FALSE : ∀ {C M N O} → M ⤇* FALSE → ∙ ⊢ M ⦂ 𝔹 → ∙ ⊢ N ⦂ C → SN O C
--                           → SN (IF M N O) C
-- sn-IF-FALSE {𝟙}     M⤇*FALSE 𝒟 ℰ (ℱ , O⇓)     = if 𝒟 ℰ ℱ , halt-IF-FALSE M⤇*FALSE O⇓
-- sn-IF-FALSE {𝔹}     M⤇*FALSE 𝒟 ℰ (ℱ , O⇓)     = if 𝒟 ℰ ℱ , halt-IF-FALSE M⤇*FALSE O⇓
-- sn-IF-FALSE {A ⊃ B} M⤇*FALSE 𝒟 ℰ (ℱ , O⇓ , f) = if 𝒟 ℰ ℱ , halt-IF-FALSE M⤇*FALSE O⇓ , (\ s →
--                                                    snpr⤇* (congs-APP (congs-IF-FALSE M⤇*FALSE done)) (app (if 𝒟 ℰ ℱ) (derp s)) (f s))


-- --------------------------------------------------------------------------------


-- -- Small-step reduction preserves SN.
-- snp⤇ : ∀ {A M M′} → M ⤇ M′ → ∙ ⊢ M ⦂ A → SN M A
--                    → SN M′ A
-- snp⤇ {𝟙}     M⤇M′ 𝒟 (_ , M⇓)     = tp⤇ M⤇M′ 𝒟 , hp⤇ M⤇M′ M⇓
-- snp⤇ {𝔹}     M⤇M′ 𝒟 (_ , M⇓)     = tp⤇ M⤇M′ 𝒟 , hp⤇ M⤇M′ M⇓
-- snp⤇ {A ⊃ B} M⤇M′ 𝒟 (_ , M⇓ , f) = tp⤇ M⤇M′ 𝒟 , hp⤇ M⤇M′ M⇓ , (\ s →
--                                        snp⤇ (cong-APP M⤇M′) (app 𝒟 (derp s)) (f s))


-- -- Iterated small-step reduction preserves SN.
-- snp⤇* : ∀ {A M M′} → M ⤇* M′ → ∙ ⊢ M ⦂ A → SN M A
--                     → SN M′ A
-- snp⤇* done                 𝒟 s = s
-- snp⤇* (step M⤇M″ M″⤇*M′) 𝒟 s = snp⤇* M″⤇*M′ (tp⤇ M⤇M″ 𝒟) (snp⤇ M⤇M″ 𝒟 s)


-- -- Big-step reduction preserves SN.
-- snp⇓ : ∀ {A M M′} → M ⇓ M′ → ∙ ⊢ M ⦂ A → SN M A
--                   → SN M′ A
-- snp⇓ (M⤇*M′ , VM′) 𝒟 s = snp⤇* M⤇*M′ 𝒟 s


-- --------------------------------------------------------------------------------


-- -- `SNs Γ` is the strong normalisation predicate on substitutions at all types `Γ`.
-- SNs : ∀ {g} → (τ : Terms 0 g) → Types g → Set
-- SNs τ Γ = All (\ { (M , A) → SN M A }) (zip τ Γ)


-- -- Every SN substitution is well-typed.
-- derps : ∀ {g} → {τ : Terms 0 g} {Γ : Types g}
--               → SNs τ Γ
--               → ∙ ⊢ τ ⦂ Γ all
-- derps σ = maps derp σ


-- --------------------------------------------------------------------------------


-- -- TODO
-- red-APP-LAM-SUB : ∀ {g M N} → {τ : Terms 0 g} → {{_ : Val N}}
--                             → APP (LAM (SUB (LIFTS τ) M)) N ⤇ SUB (τ , N) M
-- red-APP-LAM-SUB {M = M} {N} {τ} rewrite simp-CUT-SUB N τ M ⁻¹ = do red-APP-LAM


-- -- TODO
-- big-red-APP-LAM-SUB : ∀ {g M M′ N} → {τ : Terms 0 g} → {{_ : Vals τ}} {{_ : Val N}}
--                                    → SUB (τ , N) M ⇓ M′
--                                    → APP (LAM (SUB (LIFTS τ) M)) N ⇓ M′
-- big-red-APP-LAM-SUB {M = M} (SUB-M⤇*M′ , VM′) = step (red-APP-LAM-SUB {M = M}) SUB-M⤇*M′ , VM′


-- -- TODO
-- halt-APP-LAM-SUB : ∀ {g M N} → {τ : Terms 0 g} → {{_ : Vals τ}} {{_ : Val N}}
--                              → SUB (τ , N) M ⇓
--                              → APP (LAM (SUB (LIFTS τ) M)) N ⇓
-- halt-APP-LAM-SUB {M = M} (M′ , SUB-M⇓M′) = M′ , big-red-APP-LAM-SUB {M = M} SUB-M⇓M′


-- -- TODO
-- sn-APP-LAM-SUB : ∀ {B g M N A} → {τ : Terms 0 g} → {{_ : Vals τ}} {{_ : Val N}}
--                                → ∙ ⊢ SUB τ (LAM M) ⦂ A ⊃ B → ∙ ⊢ N ⦂ A → SN (SUB (τ , N) M) B
--                                → SN (APP (LAM (SUB (LIFTS τ) M)) N) B
-- sn-APP-LAM-SUB {𝟙}       {M = M} 𝒟 ℰ (𝒟′ , SUB-M⇓)     = app 𝒟 ℰ , halt-APP-LAM-SUB {M = M} SUB-M⇓
-- sn-APP-LAM-SUB {𝔹}       {M = M} 𝒟 ℰ (𝒟′ , SUB-M⇓)     = app 𝒟 ℰ , halt-APP-LAM-SUB {M = M} SUB-M⇓
-- sn-APP-LAM-SUB {B₁ ⊃ B₂} {M = M} 𝒟 ℰ (𝒟′ , SUB-M⇓ , f) = app 𝒟 ℰ , halt-APP-LAM-SUB {M = M} SUB-M⇓ , (\ s →
--                                                            snpr⤇ (cong-APP (red-APP-LAM-SUB {M = M})) (app (app 𝒟 ℰ) (derp s)) (f s))


-- --------------------------------------------------------------------------------


-- -- TODO
-- frob : ∀ {A M} → SN M A
--                → Σ (Term 0) (\ M′ → ∙ ⊢ M ⦂ A × M ⇓ M′ × SN M′ A)
-- frob {𝟙}     s@(𝒟 , (M′ , M⇓M′))     = M′ , (𝒟 , M⇓M′ , snp⇓ M⇓M′ 𝒟 s)
-- frob {𝔹}     s@(𝒟 , (M′ , M⇓M′))     = M′ , (𝒟 , M⇓M′ , snp⇓ M⇓M′ 𝒟 s)
-- frob {A ⊃ B} s@(𝒟 , (M′ , M⇓M′) , f) = M′ , (𝒟 , M⇓M′ , snp⇓ M⇓M′ 𝒟 s)


-- -- TODO
-- sn-SUB : ∀ {g M A} → {τ : Terms 0 g} {Γ : Types g} → {{_ : Vals τ}}
--                    → SNs τ Γ → Γ ⊢ M ⦂ A
--                    → SN (SUB τ M) A
-- sn-SUB σ (var i)    = get σ (zip∋₂ i)
-- sn-SUB {{Vτ}} σ (lam {A} {M = M} 𝒟) = let 𝒟′ = sub (derps σ) (lam 𝒟) in
--                                         𝒟′ , (LAM _ , done , VLAM) , (\ s →
--                                           case frob {A} s of (\ { (N′ , ℰ , (N⤇*N′ , VN′) , s′) →
--                                             snpr⤇* (congs-APP-LAM N⤇*N′)
--                                                     (app 𝒟′ ℰ)
--                                                     (sn-APP-LAM-SUB {M = M} {{Vτ}} {{VN′}} 𝒟′
--                                                                     (derp s′)
--                                                                     (sn-SUB {{Vτ , VN′}} (σ , s′) 𝒟)) }))
-- sn-SUB σ (app 𝒟 ℰ)  with sn-SUB σ 𝒟
-- sn-SUB σ (app 𝒟 ℰ)  | 𝒟′ , M′⇓ , f = f (sn-SUB σ ℰ)
-- sn-SUB σ unit       = unit  , UNIT  , done , VUNIT
-- sn-SUB σ true       = true  , TRUE  , done , VTRUE
-- sn-SUB σ false      = false , FALSE , done , VFALSE
-- sn-SUB σ (if 𝒟 ℰ ℱ) with sn-SUB σ 𝒟
-- sn-SUB σ (if 𝒟 ℰ ℱ) | 𝒟′ , M′    , SUB-M⤇*M′    , VM′    with tp⤇* SUB-M⤇*M′ 𝒟′
-- sn-SUB σ (if 𝒟 ℰ ℱ) | 𝒟′ , LAM _ , _             , VLAM   | ()
-- sn-SUB σ (if 𝒟 ℰ ℱ) | 𝒟′ , UNIT  , _             , VUNIT  | ()
-- sn-SUB σ (if 𝒟 ℰ ℱ) | 𝒟′ , TRUE  , SUB-M⤇*TRUE  , VTRUE  | true  = sn-IF-TRUE SUB-M⤇*TRUE 𝒟′ (sn-SUB σ ℰ) (sub (derps σ) ℱ)
-- sn-SUB σ (if 𝒟 ℰ ℱ) | 𝒟′ , FALSE , SUB-M⤇*FALSE , VFALSE | false = sn-IF-FALSE SUB-M⤇*FALSE 𝒟′ (sub (derps σ) ℰ) (sn-SUB σ ℱ)


-- --------------------------------------------------------------------------------


-- -- Every well-typed term is SN.
-- sn : ∀ {A M} → ∙ ⊢ M ⦂ A
--              → SN M A
-- sn {A} {M} 𝒟 = subst (\ M′ → SN M′ A) (id-SUB M) (sn-SUB ∙ 𝒟)


-- -- Every SN term terminates.
-- herp : ∀ {A M} → SN M A
--                → M ⇓
-- herp {𝟙}     (𝒟 , M⇓)     = M⇓
-- herp {𝔹}     (𝒟 , M⇓)     = M⇓
-- herp {A ⊃ B} (𝒟 , M⇓ , f) = M⇓


-- -- Every well-typed term terminates.
-- halt : ∀ {A M} → ∙ ⊢ M ⦂ A
--                → M ⇓
-- halt {A} 𝒟 = herp {A} (sn 𝒟)


-- --------------------------------------------------------------------------------
