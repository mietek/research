{-# OPTIONS --rewriting #-}

module A201802.WIP.LR3-Mutual where

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
-- mutual
--   SN : Term 0 → Type → Set
--   SN M A = ∙ ⊢ M ⦂ A × M ⇓ × SN! M A

--   SN! : Term 0 → Type → Set
--   SN! M 𝔹       = ⊤
--   SN! M 𝟙       = ⊤
--   SN! M (A ∧ B) = ⊤
--   SN! M (A ⊃ B) = ∀ {N} → SN N A → SN (APP M N) B


-- -- Every SN term is well-typed.
-- derp : ∀ {A M} → SN M A
--                → ∙ ⊢ M ⦂ A
-- derp (𝒟 , M⇓ , s!) = 𝒟


-- -- Every SN term terminates.
-- herp : ∀ {A M} → SN M A
--                → M ⇓
-- herp (𝒟 , M⇓ , s!) = M⇓


-- --------------------------------------------------------------------------------


-- -- Small-step reduction IN REVERSE preserves SN.
-- mutual
--   snpr⤇ : ∀ {A M M′} → M ⤇ M′ → ∙ ⊢ M ⦂ A → SN M′ A
--                       → SN M A
--   snpr⤇ M⤇M′ 𝒟 (𝒟′ , M′⇓ , s!′) = 𝒟 , hpr⤇ M⤇M′ M′⇓ , sn!pr⤇ M⤇M′ 𝒟 s!′

--   sn!pr⤇ : ∀ {A M M′} → M ⤇ M′ → ∙ ⊢ M ⦂ A → SN! M′ A
--                        → SN! M A
--   sn!pr⤇ {𝔹}     M⤇M′ 𝒟 ∙   = ∙
--   sn!pr⤇ {𝟙}     M⤇M′ 𝒟 ∙   = ∙
--   sn!pr⤇ {A ∧ B} M⤇M′ 𝒟 ∙   = ∙
--   sn!pr⤇ {A ⊃ B} M⤇M′ 𝒟 f s = snpr⤇ (cong-APP M⤇M′) (app 𝒟 (derp s)) (f s)


-- -- Iterated small-step reduction IN REVERSE preserves SN.
-- snpr⤇* : ∀ {A M M′} → M ⤇* M′ → ∙ ⊢ M ⦂ A → SN M′ A
--                      → SN M A
-- snpr⤇* done                 𝒟 s = s
-- snpr⤇* (step M⤇M″ M″⤇*M′) 𝒟 s = snpr⤇ M⤇M″ 𝒟 (snpr⤇* M″⤇*M′ (tp⤇ M⤇M″ 𝒟) s)


-- -- Big-step reduction IN REVERSE preserves SN.
-- snpr⇓ : ∀ {A M M′} → M ⇓ M′ → ∙ ⊢ M ⦂ A → SN M′ A
--                    → SN M A
-- snpr⇓ (M⤇*M′ , VM′) 𝒟 s = snpr⤇* M⤇*M′ 𝒟 s


-- -- If `M` is SN and `N` is SN, then `PAIR M N` is SN.
-- sn-PAIR : ∀ {A B M N} → SN M A → SN N B
--                       → SN (PAIR M N) (A ∧ B)
-- sn-PAIR (𝒟 , M⇓ , s!₁) (ℰ , N⇓ , s!₂) = pair 𝒟 ℰ , halt-PAIR M⇓ N⇓ , ∙


-- -- ???
-- mutual
--   sn-FST-PAIR : ∀ {A B M M′ N′} → {{_ : Val M′}} {{_ : Val N′}}
--                                 → M ⤇* PAIR M′ N′ → ∙ ⊢ M ⦂ A ∧ B
--                                 → SN (FST M) A
--   sn-FST-PAIR M⤇*PAIR 𝒟 = fst 𝒟 , halt-FST-PAIR M⤇*PAIR , sn!-FST-PAIR M⤇*PAIR 𝒟

--   sn!-FST-PAIR : ∀ {A B M M′ N′} → {{_ : Val M′}} {{_ : Val N′}}
--                                  → M ⤇* PAIR M′ N′ → ∙ ⊢ M ⦂ A ∧ B
--                                  → SN! (FST M) A
--   sn!-FST-PAIR {𝔹}       M⤇*PAIR 𝒟   = ∙
--   sn!-FST-PAIR {𝟙}       M⤇*PAIR 𝒟   = ∙
--   sn!-FST-PAIR {A₁ ∧ A₂} M⤇*PAIR 𝒟   = ∙
--   sn!-FST-PAIR {A₁ ⊃ A₂} M⤇*PAIR 𝒟 s = {!!}
--   -- snpr⤇* (congs-APP (reds-FST-PAIR M⤇*PAIR)) (app (fst 𝒟) (derp s)) ?


-- -- ???
-- mutual
--   sn-SND-PAIR : ∀ {A B M M′ N′} → {{_ : Val M′}} {{_ : Val N′}}
--                                 → M ⤇* PAIR M′ N′ → ∙ ⊢ M ⦂ A ∧ B
--                                 → SN (SND M) B
--   sn-SND-PAIR M⤇*PAIR 𝒟 = snd 𝒟 , halt-SND-PAIR M⤇*PAIR , sn!-SND-PAIR M⤇*PAIR 𝒟

--   sn!-SND-PAIR : ∀ {B A M M′ N′} → {{_ : Val M′}} {{_ : Val N′}}
--                                  → M ⤇* PAIR M′ N′ → ∙ ⊢ M ⦂ A ∧ B
--                                  → SN! (SND M) B
--   sn!-SND-PAIR {𝔹}       M⤇*PAIR 𝒟   = ∙
--   sn!-SND-PAIR {𝟙}       M⤇*PAIR 𝒟   = ∙
--   sn!-SND-PAIR {B₁ ∧ B₂} M⤇*PAIR 𝒟   = ∙
--   sn!-SND-PAIR {B₁ ⊃ B₂} M⤇*PAIR 𝒟 s = {!!}
--   -- snpr⤇* (congs-APP (reds-SND-PAIR M⤇*PAIR)) (app (snd 𝒟) (derp s)) ?


-- -- If `M` reduces to `TRUE` and `N` is SN, then `IF M N O` is SN.
-- mutual
--   sn-IF-TRUE : ∀ {C M N O} → M ⤇* TRUE → ∙ ⊢ M ⦂ 𝔹 → SN N C → ∙ ⊢ O ⦂ C
--                            → SN (IF M N O) C
--   sn-IF-TRUE M⤇*TRUE 𝒟 (ℰ , N⇓ , s!) ℱ = if 𝒟 ℰ ℱ , halt-IF-TRUE M⤇*TRUE N⇓ , sn!-IF-TRUE M⤇*TRUE 𝒟 ℰ ℱ s!

--   sn!-IF-TRUE : ∀ {C M N O} → M ⤇* TRUE → ∙ ⊢ M ⦂ 𝔹 → ∙ ⊢ N ⦂ C → ∙ ⊢ O ⦂ C → SN! N C
--                             → SN! (IF M N O) C
--   sn!-IF-TRUE {𝔹}     M⤇*TRUE 𝒟 ℰ ℱ ∙   = ∙
--   sn!-IF-TRUE {𝟙}     M⤇*TRUE 𝒟 ℰ ℱ ∙   = ∙
--   sn!-IF-TRUE {A ∧ B} M⤇*TRUE 𝒟 ℰ ℱ ∙   = ∙
--   sn!-IF-TRUE {A ⊃ B} M⤇*TRUE 𝒟 ℰ ℱ f s = snpr⤇* (congs-APP (reds-IF-TRUE M⤇*TRUE done)) (app (if 𝒟 ℰ ℱ) (derp s)) (f s)


-- -- If `M` reduces to `FALSE` and `O` is SN, then `IF M N O` is SN.
-- mutual
--   sn-IF-FALSE : ∀ {C M N O} → M ⤇* FALSE → ∙ ⊢ M ⦂ 𝔹 → ∙ ⊢ N ⦂ C → SN O C
--                             → SN (IF M N O) C
--   sn-IF-FALSE M⤇*FALSE 𝒟 ℰ (ℱ , N⇓ , s!) = if 𝒟 ℰ ℱ , halt-IF-FALSE M⤇*FALSE N⇓ , sn!-IF-FALSE M⤇*FALSE 𝒟 ℰ ℱ s!

--   sn!-IF-FALSE : ∀ {C M N O} → M ⤇* FALSE → ∙ ⊢ M ⦂ 𝔹 → ∙ ⊢ N ⦂ C → ∙ ⊢ O ⦂ C → SN! O C
--                              → SN! (IF M N O) C
--   sn!-IF-FALSE {𝔹}     M⤇*FALSE 𝒟 ℰ ℱ ∙   = ∙
--   sn!-IF-FALSE {𝟙}     M⤇*FALSE 𝒟 ℰ ℱ ∙   = ∙
--   sn!-IF-FALSE {A ∧ B} M⤇*FALSE 𝒟 ℰ ℱ ∙   = ∙
--   sn!-IF-FALSE {A ⊃ B} M⤇*FALSE 𝒟 ℰ ℱ f s = snpr⤇* (congs-APP (reds-IF-FALSE M⤇*FALSE done)) (app (if 𝒟 ℰ ℱ) (derp s)) (f s)


-- --------------------------------------------------------------------------------


-- -- Small-step reduction preserves SN.
-- mutual
--   snp⤇ : ∀ {A M M′} → M ⤇ M′ → ∙ ⊢ M ⦂ A → SN M A
--                      → SN M′ A
--   snp⤇ M⤇M′ 𝒟 (_ , M⇓ , s!) = tp⤇ M⤇M′ 𝒟 , hp⤇ M⤇M′ M⇓ , sn!p⤇ M⤇M′ 𝒟 s!

--   sn!p⤇ : ∀ {A M M′} → M ⤇ M′ → ∙ ⊢ M ⦂ A → SN! M A
--                       → SN! M′ A
--   sn!p⤇ {𝔹}     M⤇M′ 𝒟 ∙   = ∙
--   sn!p⤇ {𝟙}     M⤇M′ 𝒟 ∙   = ∙
--   sn!p⤇ {A ∧ B} M⤇M′ 𝒟 ∙   = ∙
--   sn!p⤇ {A ⊃ B} M⤇M′ 𝒟 f s = snp⤇ (cong-APP M⤇M′) (app 𝒟 (derp s)) (f s)


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
-- red-APP-LAM-SUB {M = M} {N} {τ} rewrite simp-CUT-SUB N τ M ⁻¹ = red APP-LAM


-- -- TODO
-- big-red-APP-LAM-SUB : ∀ {g M M′ N} → {τ : Terms 0 g} → {{_ : Vals τ}} {{_ : Val N}}
--                                    → SUB (τ , N) M ⇓ M′
--                                    → APP (LAM (SUB (LIFTS τ) M)) N ⇓ M′
-- big-red-APP-LAM-SUB {M = M} (SUB⤇*M′ , VM′) = step (red-APP-LAM-SUB {M = M}) SUB⤇*M′ , VM′


-- -- TODO
-- halt-APP-LAM-SUB : ∀ {g M N} → {τ : Terms 0 g} → {{_ : Vals τ}} {{_ : Val N}}
--                              → SUB (τ , N) M ⇓
--                              → APP (LAM (SUB (LIFTS τ) M)) N ⇓
-- halt-APP-LAM-SUB {M = M} (M′ , SUB⇓M′) = M′ , big-red-APP-LAM-SUB {M = M} SUB⇓M′


-- -- TODO
-- mutual
--   sn-APP-LAM-SUB : ∀ {B g M N A} → {τ : Terms 0 g} → {{_ : Vals τ}} {{_ : Val N}}
--                                  → ∙ ⊢ SUB τ (LAM M) ⦂ A ⊃ B → ∙ ⊢ N ⦂ A → SN (SUB (τ , N) M) B
--                                  → SN (APP (LAM (SUB (LIFTS τ) M)) N) B
--   sn-APP-LAM-SUB {M = M} 𝒟 ℰ (𝒟′ , SUB⇓ , s!) = app 𝒟 ℰ , halt-APP-LAM-SUB {M = M} SUB⇓ , sn!-APP-LAM-SUB {M = M} 𝒟 ℰ s!

--   sn!-APP-LAM-SUB : ∀ {B g M N A} → {τ : Terms 0 g} → {{_ : Vals τ}} {{_ : Val N}}
--                                   → ∙ ⊢ SUB τ (LAM M) ⦂ A ⊃ B → ∙ ⊢ N ⦂ A → SN! (SUB (τ , N) M) B
--                                   → SN! (APP (LAM (SUB (LIFTS τ) M)) N) B
--   sn!-APP-LAM-SUB {𝔹}       {M = M} 𝒟 ℰ ∙   = ∙
--   sn!-APP-LAM-SUB {𝟙}       {M = M} 𝒟 ℰ ∙   = ∙
--   sn!-APP-LAM-SUB {B₁ ∧ B₂} {M = M} 𝒟 ℰ ∙   = ∙
--   sn!-APP-LAM-SUB {B₁ ⊃ B₂} {M = M} 𝒟 ℰ f s = snpr⤇ (cong-APP (red-APP-LAM-SUB {M = M})) (app (app 𝒟 ℰ) (derp s)) (f s)


-- --------------------------------------------------------------------------------


-- mutual
--   sn-SUB : ∀ {g M A} → {τ : Terms 0 g} {Γ : Types g} → {{_ : Vals τ}}
--                      → SNs τ Γ → Γ ⊢ M ⦂ A
--                      → SN (SUB τ M) A
--   sn-SUB σ (var i)    = get σ (zip∋₂ i)
--   sn-SUB σ (lam 𝒟)    = let 𝒟′ = sub (derps σ) (lam 𝒟) in
--                           𝒟′ , (LAM _ , done , VLAM) , sn-SUB-LAM σ 𝒟 𝒟′
--   sn-SUB σ (app 𝒟 ℰ)  with sn-SUB σ 𝒟
--   sn-SUB σ (app 𝒟 ℰ)  | 𝒟′ , M′⇓ , f = f (sn-SUB σ ℰ)
--   sn-SUB σ (pair 𝒟 ℰ) = sn-PAIR (sn-SUB σ 𝒟) (sn-SUB σ ℰ)
--   sn-SUB σ (fst 𝒟)    with sn-SUB σ 𝒟
--   sn-SUB σ (fst 𝒟)    | 𝒟′ , (M′       , SUB⤇*M′   , VM′)    , ∙ with tp⤇* SUB⤇*M′ 𝒟′
--   sn-SUB σ (fst 𝒟)    | 𝒟′ , (LAM _    , _          , VLAM)   , ∙ | ()
--   sn-SUB σ (fst 𝒟)    | 𝒟′ , (UNIT     , _          , VUNIT)  , ∙ | ()
--   sn-SUB σ (fst 𝒟)    | 𝒟′ , (PAIR _ _ , SUB⤇*PAIR , VPAIR)  , ∙ | pair _ _ = sn-FST-PAIR SUB⤇*PAIR 𝒟′
--   sn-SUB σ (fst 𝒟)    | 𝒟′ , (TRUE     , _          , VTRUE)  , ∙ | ()
--   sn-SUB σ (fst 𝒟)    | 𝒟′ , (FALSE    , _          , VFALSE) , ∙ | ()
--   sn-SUB σ (snd 𝒟)    with sn-SUB σ 𝒟
--   sn-SUB σ (snd 𝒟)    | 𝒟′ , (M′       , SUB⤇*M′   , VM′)    , ∙ with tp⤇* SUB⤇*M′ 𝒟′
--   sn-SUB σ (snd 𝒟)    | 𝒟′ , (LAM _    , _          , VLAM)   , ∙ | ()
--   sn-SUB σ (snd 𝒟)    | 𝒟′ , (UNIT     , _          , VUNIT)  , ∙ | ()
--   sn-SUB σ (snd 𝒟)    | 𝒟′ , (PAIR _ _ , SUB⤇*PAIR , VPAIR)  , ∙ | pair _ _ = sn-SND-PAIR SUB⤇*PAIR 𝒟′
--   sn-SUB σ (snd 𝒟)    | 𝒟′ , (TRUE     , _          , VTRUE)  , ∙ | ()
--   sn-SUB σ (snd 𝒟)    | 𝒟′ , (FALSE    , _          , VFALSE) , ∙ | ()
--   sn-SUB σ unit       = unit  , (UNIT  , done , VUNIT)  , ∙
--   sn-SUB σ true       = true  , (TRUE  , done , VTRUE)  , ∙
--   sn-SUB σ false      = false , (FALSE , done , VFALSE) , ∙
--   sn-SUB σ (if 𝒟 ℰ ℱ) with sn-SUB σ 𝒟
--   sn-SUB σ (if 𝒟 ℰ ℱ) | 𝒟′ , (M′       , SUB⤇*M′    , VM′)    , ∙ with tp⤇* SUB⤇*M′ 𝒟′
--   sn-SUB σ (if 𝒟 ℰ ℱ) | 𝒟′ , (LAM _    , _           , VLAM)   , ∙ | ()
--   sn-SUB σ (if 𝒟 ℰ ℱ) | 𝒟′ , (UNIT     , _           , VUNIT)  , ∙ | ()
--   sn-SUB σ (if 𝒟 ℰ ℱ) | 𝒟′ , (PAIR _ _ , _           , VPAIR)  , ∙ | ()
--   sn-SUB σ (if 𝒟 ℰ ℱ) | 𝒟′ , (TRUE     , SUB⤇*TRUE  , VTRUE)  , ∙ | true  = sn-IF-TRUE SUB⤇*TRUE 𝒟′ (sn-SUB σ ℰ) (sub (derps σ) ℱ)
--   sn-SUB σ (if 𝒟 ℰ ℱ) | 𝒟′ , (FALSE    , SUB⤇*FALSE , VFALSE) , ∙ | false = sn-IF-FALSE SUB⤇*FALSE 𝒟′ (sub (derps σ) ℰ) (sn-SUB σ ℱ)

--   sn-SUB-LAM : ∀ {g M N A B} → {τ : Terms 0 g} {Γ : Types g} → {{_ : Vals τ}}
--                              → SNs τ Γ → Γ , A ⊢ M ⦂ B → ∙ ⊢ LAM (SUB (LIFTS τ) M) ⦂ A ⊃ B → SN N A
--                              → SN (APP (LAM (SUB (LIFTS τ) M)) N) B
--   sn-SUB-LAM {M = M} {{Vτ}} σ 𝒟 𝒟′ s@(ℰ , (N′ , N⇓N′@(N⤇*N′ , VN′)) , s!)
--     = let s′ = snp⇓ N⇓N′ ℰ s in
--         snpr⤇* (congs-APP-LAM N⤇*N′) (app 𝒟′ ℰ) (sn-APP-LAM-SUB {M = M} {{Vτ}} {{VN′}} 𝒟′ (derp s′) (sn-SUB {{Vτ , VN′}} (σ , s′) 𝒟))


-- --------------------------------------------------------------------------------


-- -- Every well-typed term is SN.
-- sn : ∀ {A M} → ∙ ⊢ M ⦂ A
--              → SN M A
-- sn {A} {M} 𝒟 = subst (\ M′ → SN M′ A) (id-SUB M) (sn-SUB ∙ 𝒟)


-- -- Every well-typed term terminates.
-- halt : ∀ {A M} → ∙ ⊢ M ⦂ A
--                → M ⇓
-- halt {A} 𝒟 = herp {A} (sn 𝒟)


-- --------------------------------------------------------------------------------
