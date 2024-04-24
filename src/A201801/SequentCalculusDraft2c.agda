{-# OPTIONS --allow-unsolved-metas #-}

module A201801.SequentCalculusDraft2c where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.FullIPLPropositions
open import A201801.FullIPLDerivations hiding (cut)
open import A201801.SequentCalculusDraft
open import A201801.SequentCalculusDraft2a


--------------------------------------------------------------------------------


-- TODO: unfinished
-- -- {-# TERMINATING #-}
-- wub : ∀ {Γ Ξ A} → Γ ⟹ Ξ all → Ξ ⟹ A
--                 → Γ ⟹ A
-- wub ξ (⊃R ℰ)       = ⊃R (wub (liftsₛ ξ) ℰ)
-- wub ξ (∧R ℰ₁ ℰ₂)   = ∧R (wub ξ ℰ₁) (wub ξ ℰ₂)
-- wub ξ 𝟙R           = 𝟙R
-- wub ξ (∨R₁ ℰ)      = ∨R₁ (wub ξ ℰ)
-- wub ξ (∨R₂ ℰ)      = ∨R₂ (wub ξ ℰ)
-- wub ξ (var j)      = get ξ j

-- wub ∙ ℰ = renₛ bot⊒ ℰ

-- wub (ξ , ⊃R 𝒟)     ℰ = {!!}
-- wub (ξ , ∧R 𝒟₁ 𝒟₂) ℰ = {!!}

-- wub (ξ , 𝟙R) (⊃L j ℰ₁ ℰ₂) = {!!}
-- wub (ξ , 𝟙R) (∧L₁ j ℰ)    = {!!}
-- wub (ξ , 𝟙R) (∧L₂ j ℰ)    = {!!}
-- wub (ξ , 𝟙R) (𝟘L j)       = 𝟘L {!j!}
-- wub (ξ , 𝟙R) (∨L j ℰ₁ ℰ₂) = {!!}

-- wub (ξ , ∨R₁ 𝒟)    ℰ = {!!}
-- wub (ξ , ∨R₂ 𝒟)    ℰ = {!!}

-- wub (ξ , var i) ℰ = {!!}

-- wub (ξ , ⊃L i 𝒟₁ 𝒟₂) ℰ = {!!}
-- wub (ξ , ∧L₁ i 𝒟) ℰ = {!!}
-- wub (ξ , ∧L₂ i 𝒟) ℰ = {!!}
-- wub (ξ , 𝟘L i) ℰ = {!!}
-- wub (ξ , ∨L i 𝒟₁ 𝒟₂) ℰ = {!!}
-- -- wub ξ (⊃L j ℰ₁ ℰ₂) = {!!}
-- -- wub ξ (∧L₁ j ℰ)    = {!!}
-- -- wub ξ (∧L₂ j ℰ)    = {!!}
-- -- wub ξ (𝟘L j)       = {!!}
-- -- wub ξ (∨L j ℰ₁ ℰ₂) = {!!}


-- --------------------------------------------------------------------------------


-- -- TODO: unfinished
-- -- {-# TERMINATING #-}
-- -- wut : ∀ {A C Γ} → (i : Γ ∋ A) → Γ - i ⟹ A → Γ ⟹ C
-- --                 → Γ - i ⟹ C

-- -- wut i 𝒟 (⊃R ℰ)     = ⊃R (wut (suc i) (wkₛ 𝒟) ℰ)
-- -- wut i 𝒟 (∧R ℰ₁ ℰ₂) = ∧R (wut i 𝒟 ℰ₁) (wut i 𝒟 ℰ₂)
-- -- wut i 𝒟 𝟙R         = 𝟙R
-- -- wut i 𝒟 (∨R₁ ℰ)    = ∨R₁ (wut i 𝒟 ℰ)
-- -- wut i 𝒟 (∨R₂ ℰ)    = ∨R₂ (wut i 𝒟 ℰ)

-- -- wut i 𝒟 (var  k) with i ≟∋ k
-- -- wut i 𝒟 (var .i) | same .i   = 𝒟
-- -- wut i 𝒟 (var ._) | diff .i k = var k

-- -- wut i (var j) ℰ = renₛ (delred⊒ i j) ℰ

-- -- wut i (⊃L j 𝒟₁ 𝒟₂) ℰ = ⊃L j 𝒟₁ (wut (suc i) 𝒟₂ (wkₛ ℰ))
-- -- wut i (∧L₁ j 𝒟)    ℰ = ∧L₁ j (wut (suc i) 𝒟 (wkₛ ℰ))
-- -- wut i (∧L₂ j 𝒟)    ℰ = ∧L₂ j (wut (suc i) 𝒟 (wkₛ ℰ))
-- -- wut i (𝟘L j)       ℰ = 𝟘L j
-- -- wut i (∨L j 𝒟₁ 𝒟₂) ℰ = ∨L j (wut (suc i) 𝒟₁ (wkₛ ℰ)) (wut (suc i) 𝒟₂ (wkₛ ℰ))

-- -- wut i 𝒟 (⊃L  k ℰ₁ ℰ₂) with i ≟∋ k
-- -- wut i 𝒟 (⊃L .i ℰ₁ ℰ₂) | same .i   = {!!}
-- -- wut i 𝒟 (⊃L ._ ℰ₁ ℰ₂) | diff .i k = ⊃L k (wut i 𝒟 ℰ₁) (wut (suc i) (wkₛ 𝒟) ℰ₂)

-- -- wut i 𝒟 (∧L₁  k ℰ) with i ≟∋ k
-- -- wut i 𝒟 (∧L₁ .i ℰ) | same .i   = {!!}
-- -- wut i 𝒟 (∧L₁ ._ ℰ) | diff .i k = ∧L₁ k (wut (suc i) (wkₛ 𝒟) ℰ)

-- -- wut i 𝒟 (∧L₂  k ℰ) with i ≟∋ k
-- -- wut i 𝒟 (∧L₂ .i ℰ) | same .i = {!!}
-- -- wut i 𝒟 (∧L₂ ._ ℰ) | diff .i k = ∧L₂ k (wut (suc i) (wkₛ 𝒟) ℰ)

-- -- wut     i 𝒟 (𝟘L  k) with i ≟∋ k
-- -- wut {A} i 𝒟 (𝟘L .i) | same .i   = {!!}
-- -- wut     i 𝒟 (𝟘L ._) | diff .i k = 𝟘L k

-- -- wut i 𝒟 (∨L  k ℰ₁ ℰ₂) with i ≟∋ k
-- -- wut i 𝒟 (∨L .i ℰ₁ ℰ₂) | same .i   = {!!}
-- -- wut i 𝒟 (∨L ._ ℰ₁ ℰ₂) | diff .i k = ∨L k (wut (suc i) (wkₛ 𝒟) ℰ₁) (wut (suc i) (wkₛ 𝒟) ℰ₂)


-- -- --------------------------------------------------------------------------------
