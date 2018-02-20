{-# OPTIONS --allow-unsolved-metas #-}

module SequentCalculusDraft2c where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import FullIPLPropositions
open import FullIPLDerivations hiding (cut)
open import SequentCalculusDraft
open import SequentCalculusDraft2a


--------------------------------------------------------------------------------


{-# TERMINATING #-}
wub : ∀ {Γ Ξ A} → Γ ⟹ Ξ all → Ξ ⟹ A
                → Γ ⟹ A
wub ξ (⊃R ℰ)       = ⊃R (wub (liftsₛ ξ) ℰ)
wub ξ (∧R ℰ₁ ℰ₂)   = ∧R (wub ξ ℰ₁) (wub ξ ℰ₂)
wub ξ 𝟏R           = 𝟏R
wub ξ (∨R₁ ℰ)      = ∨R₁ (wub ξ ℰ)
wub ξ (∨R₂ ℰ)      = ∨R₂ (wub ξ ℰ)
wub ξ (var j)      = get ξ j
wub ξ (⊃L j ℰ₁ ℰ₂) = wub (ξ , get ξ j) (⊃L zero (wkₛ ℰ₁) (exₛ (wkₛ ℰ₂)))
wub ξ (∧L₁ j ℰ)    = wub (ξ , get ξ j) (∧L₁ zero (exₛ (wkₛ ℰ)))
wub ξ (∧L₂ j ℰ)    = wub (ξ , get ξ j) (∧L₂ zero (exₛ (wkₛ ℰ)))
wub ξ (𝟎L j)       = wub (ξ , get ξ j) (𝟎L zero)
wub ξ (∨L j ℰ₁ ℰ₂) = wub (ξ , get ξ j) (∨L zero (exₛ (wkₛ ℰ₁)) (exₛ (wkₛ ℰ₂)))


--------------------------------------------------------------------------------


{-# TERMINATING #-}
wut : ∀ {A C Γ} → (i : Γ ∋ A) → Γ - i ⟹ A → Γ ⟹ C
                → Γ - i ⟹ C

wut i 𝒟 (⊃R ℰ)     = ⊃R (wut (suc i) (wkₛ 𝒟) ℰ)
wut i 𝒟 (∧R ℰ₁ ℰ₂) = ∧R (wut i 𝒟 ℰ₁) (wut i 𝒟 ℰ₂)
wut i 𝒟 𝟏R         = 𝟏R
wut i 𝒟 (∨R₁ ℰ)    = ∨R₁ (wut i 𝒟 ℰ)
wut i 𝒟 (∨R₂ ℰ)    = ∨R₂ (wut i 𝒟 ℰ)

wut i 𝒟 (var  k) with i ≟∋ k
wut i 𝒟 (var .i) | same .i   = 𝒟
wut i 𝒟 (var ._) | diff .i k = var k

wut i (var j) ℰ = renₛ (delred⊒ i j) ℰ

wut i (⊃L j 𝒟₁ 𝒟₂) ℰ = ⊃L j 𝒟₁ (wut (suc i) 𝒟₂ (wkₛ ℰ))
wut i (∧L₁ j 𝒟)    ℰ = ∧L₁ j (wut (suc i) 𝒟 (wkₛ ℰ))
wut i (∧L₂ j 𝒟)    ℰ = ∧L₂ j (wut (suc i) 𝒟 (wkₛ ℰ))
wut i (𝟎L j)       ℰ = 𝟎L j
wut i (∨L j 𝒟₁ 𝒟₂) ℰ = ∨L j (wut (suc i) 𝒟₁ (wkₛ ℰ)) (wut (suc i) 𝒟₂ (wkₛ ℰ))

wut i 𝒟 (⊃L  k ℰ₁ ℰ₂) with i ≟∋ k
wut i 𝒟 (⊃L .i ℰ₁ ℰ₂) | same .i   = {!!}
wut i 𝒟 (⊃L ._ ℰ₁ ℰ₂) | diff .i k = ⊃L k (wut i 𝒟 ℰ₁) (wut (suc i) (wkₛ 𝒟) ℰ₂)

wut i 𝒟 (∧L₁  k ℰ) with i ≟∋ k
wut i 𝒟 (∧L₁ .i ℰ) | same .i   = {!!}
wut i 𝒟 (∧L₁ ._ ℰ) | diff .i k = ∧L₁ k (wut (suc i) (wkₛ 𝒟) ℰ)

wut i 𝒟 (∧L₂  k ℰ) with i ≟∋ k
wut i 𝒟 (∧L₂ .i ℰ) | same .i = {!!}
wut i 𝒟 (∧L₂ ._ ℰ) | diff .i k = ∧L₂ k (wut (suc i) (wkₛ 𝒟) ℰ)

wut     i 𝒟 (𝟎L  k) with i ≟∋ k
wut {A} i 𝒟 (𝟎L .i) | same .i   = {!!}
wut     i 𝒟 (𝟎L ._) | diff .i k = 𝟎L k

wut i 𝒟 (∨L  k ℰ₁ ℰ₂) with i ≟∋ k
wut i 𝒟 (∨L .i ℰ₁ ℰ₂) | same .i   = {!!}
wut i 𝒟 (∨L ._ ℰ₁ ℰ₂) | diff .i k = ∨L k (wut (suc i) (wkₛ 𝒟) ℰ₁) (wut (suc i) (wkₛ 𝒟) ℰ₂)


--------------------------------------------------------------------------------
