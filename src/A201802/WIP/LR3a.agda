{-# OPTIONS --rewriting #-}

module A201802.WIP.LR3a where

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


-- SN : ∀ {M A} → ∙ ⊢ M ⦂ A → Set
-- SN {M} {𝔹}     𝒟 = M ⇓
-- SN {M} {A ⊃ B} 𝒟 = M ⇓ × (∀ {N} → {ℰ : ∙ ⊢ N ⦂ A} → SN ℰ → SN (app 𝒟 ℰ))


-- -- sn-if-true : ∀ {C M N O} → {𝒟 : ∙ ⊢ M ⦂ 𝔹} {ℰ : ∙ ⊢ N ⦂ C} {ℱ : ∙ ⊢ O ⦂ C}
-- --                          → M ⤅ TRUE → SN ℰ
-- --                          → SN (if 𝒟 ℰ ℱ)
-- -- sn-if-true {𝔹}     M⤅TRUE N⇓       = halt-IF-TRUE M⤅TRUE N⇓
-- -- sn-if-true {A ⊃ B} M⤅TRUE (N⇓ , f) = halt-IF-TRUE M⤅TRUE N⇓ , (\ sn𝒢 → {!!}) -- SN (app (if 𝒟 ℰ ℱ) 𝒢)


-- -- sn-if-false : ∀ {C M N O} → {𝒟 : ∙ ⊢ M ⦂ 𝔹} {ℰ : ∙ ⊢ N ⦂ C} {ℱ : ∙ ⊢ O ⦂ C}
-- --                           → M ⤅ FALSE → SN ℱ
-- --                           → SN (if 𝒟 ℰ ℱ)
-- -- sn-if-false {𝔹}     M⤅FALSE O⇓       = halt-IF-FALSE M⤅FALSE O⇓
-- -- sn-if-false {A ⊃ B} M⤅FALSE (O⇓ , f) = halt-IF-FALSE M⤅FALSE O⇓ , (\ sn𝒢 → {!!}) -- SN (app (if 𝒟 ℰ ℱ) 𝒢)


-- -- sn : ∀ {M A} → (𝒟 : ∙ ⊢ M ⦂ A)
-- --              → SN 𝒟
-- -- sn (var ())
-- -- sn (lam 𝒟)    = val (LAM _) , done , (\ snℰ → {!!}) -- SN (app (lam 𝒟) ℰ)
-- -- sn (app 𝒟 ℰ)  = {!!} -- SN (app 𝒟 ℰ)
-- -- sn true       = val TRUE , done
-- -- sn false      = val FALSE , done
-- -- sn (if 𝒟 ℰ ℱ) with sn 𝒟
-- -- sn (if 𝒟 ℰ ℱ) | M′ , M⤅M′ with tp⤅ M⤅M′ 𝒟
-- -- sn (if 𝒟 ℰ ℱ) | val (LAM M″) {{iv-LAM}}   , M⤅LAM-M″ | ()
-- -- sn (if 𝒟 ℰ ℱ) | val TRUE     {{iv-TRUE}}  , M⤅TRUE   | true  = sn-if-true {𝒟 = 𝒟} {ℰ} {ℱ} M⤅TRUE (sn ℰ)
-- -- sn (if 𝒟 ℰ ℱ) | val FALSE    {{iv-FALSE}} , M⤅FALSE  | false = sn-if-false {𝒟 = 𝒟} {ℰ} {ℱ} M⤅FALSE (sn ℱ)


-- -- halt-sn : ∀ {A M} → (𝒟 : ∙ ⊢ M ⦂ A) → SN 𝒟
-- --                   → M ⇓
-- -- halt-sn {𝔹}     𝒟 M⇓       = M⇓
-- -- halt-sn {A ⊃ B} 𝒟 (M⇓ , f) = M⇓


-- -- halt : ∀ {M A} → ∙ ⊢ M ⦂ A
-- --                → M ⇓
-- -- halt 𝒟 = halt-sn 𝒟 (sn 𝒟)


-- --------------------------------------------------------------------------------


-- SNs : ∀ {g} → {τ : Terms 0 g} {Γ : Types g} → ∙ ⊢ τ ⦂ Γ all → Set
-- SNs {τ = τ} {Γ} γ = {!All ? γ!}

-- -- SNs {Γ = ∙}     {vals ∙}                       ∙       = ⊤
-- -- SNs {Γ = Γ , A} {vals (τ , M) {{av-τ , iv-M}}} (γ , 𝒟) = SNs {τ = vals τ {{av-τ}}} γ × SN 𝒟


-- -- sn-sub : ∀ {g M A} → {τ : Vals 0 g} {Γ : Types g} {γ : ∙ ⊢ Vals.terms τ ⦂ Γ all}
-- --                    → SNs γ → (𝒟 : Γ ⊢ M ⦂ A)
-- --                    → SN (sub γ 𝒟)
-- -- sn-sub σ 𝒟 = {!!}


-- -- --------------------------------------------------------------------------------
