{-# OPTIONS --rewriting #-}

module A201801.S4StandardBidirectionalDerivations-NormalNeutral where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.S4Propositions
open import A201801.S4StandardDerivations


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢_normal[_]
  data _⊢_normal[_] : List Assert → Form → List Form → Set
    where
      lam : ∀ {A B Δ Γ} → Δ ⊢ B normal[ Γ , A ]
                        → Δ ⊢ A ⊃ B normal[ Γ ]

      box : ∀ {A Δ Γ} → Δ ⊢ A valid[ ∙ ]
                      → Δ ⊢ □ A normal[ Γ ]

      letbox : ∀ {A B Δ Γ} → Δ ⊢ □ A neutral[ Γ ] → Δ , ⟪⊫ A ⟫ ⊢ B normal[ Γ ]
                           → Δ ⊢ B normal[ Γ ]

      use : ∀ {P Δ Γ} → Δ ⊢ ι P neutral[ Γ ]
                      → Δ ⊢ ι P normal[ Γ ]

  infix 3 _⊢_neutral[_]
  data _⊢_neutral[_] : List Assert → Form → List Form → Set
    where
      var : ∀ {A Δ Γ} → Γ ∋ A
                      → Δ ⊢ A neutral[ Γ ]

      app : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B neutral[ Γ ] → Δ ⊢ A normal[ Γ ]
                        → Δ ⊢ B neutral[ Γ ]

      mvar : ∀ {A Δ Γ} → Δ ∋ ⟪⊫ A ⟫
                       → Δ ⊢ A neutral[ Γ ]


--------------------------------------------------------------------------------


mutual
  renₗ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⊢ A normal[ Γ ]
                      → Δ ⊢ A normal[ Γ′ ]
  renₗ η (lam 𝒟)      = lam (renₗ (keep η) 𝒟)
  renₗ η (box 𝒟)      = box 𝒟
  renₗ η (letbox 𝒟 ℰ) = letbox (renᵣ η 𝒟) (renₗ η ℰ)
  renₗ η (use 𝒟)      = use (renᵣ η 𝒟)

  renᵣ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⊢ A neutral[ Γ ]
                      → Δ ⊢ A neutral[ Γ′ ]
  renᵣ η (var i)   = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₗ η ℰ)
  renᵣ η (mvar i)  = mvar i


--------------------------------------------------------------------------------


wkᵣ : ∀ {B Δ Γ A} → Δ ⊢ A neutral[ Γ ]
                  → Δ ⊢ A neutral[ Γ , B ]
wkᵣ 𝒟 = renᵣ (drop id⊇) 𝒟


vzᵣ : ∀ {Δ Γ A} → Δ ⊢ A neutral[ Γ , A ]
vzᵣ = var zero


--------------------------------------------------------------------------------


mutual
  mrenₗ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⊢ A normal[ Γ ]
                       → Δ′ ⊢ A normal[ Γ ]
  mrenₗ η (lam 𝒟)      = lam (mrenₗ η 𝒟)
  mrenₗ η (box 𝒟)      = box (mren η 𝒟)
  mrenₗ η (letbox 𝒟 ℰ) = letbox (mrenᵣ η 𝒟) (mrenₗ (keep η) ℰ)
  mrenₗ η (use 𝒟)      = use (mrenᵣ η 𝒟)

  mrenᵣ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⊢ A neutral[ Γ ]
                       → Δ′ ⊢ A neutral[ Γ ]
  mrenᵣ η (var i)   = var i
  mrenᵣ η (app 𝒟 ℰ) = app (mrenᵣ η 𝒟) (mrenₗ η ℰ)
  mrenᵣ η (mvar i)  = mvar (ren∋ η i)


mwkᵣ : ∀ {B A Δ Γ} → Δ ⊢ A neutral[ Γ ]
                   → Δ , B ⊢ A neutral[ Γ ]
mwkᵣ 𝒟 = mrenᵣ (drop id⊇) 𝒟


mvzᵣ : ∀ {Δ Γ A} → Δ , ⟪⊫ A ⟫ ⊢ A neutral[ Γ ]
mvzᵣ = mvar zero


--------------------------------------------------------------------------------


mutual
  denmₗ : ∀ {Δ Γ A} → Δ ⊢ A normal[ Γ ]
                    → Δ ⊢ A valid[ Γ ]
  denmₗ (lam 𝒟)      = lam (denmₗ 𝒟)
  denmₗ (box 𝒟)      = box 𝒟
  denmₗ (letbox 𝒟 ℰ) = letbox (denmᵣ 𝒟) (denmₗ ℰ)
  denmₗ (use 𝒟)      = denmᵣ 𝒟

  denmᵣ : ∀ {Δ Γ A} → Δ ⊢ A neutral[ Γ ]
                    → Δ ⊢ A valid[ Γ ]
  denmᵣ (var i)   = var i
  denmᵣ (app 𝒟 ℰ) = app (denmᵣ 𝒟) (denmₗ ℰ)
  denmᵣ (mvar i)  = mvar i


--------------------------------------------------------------------------------
