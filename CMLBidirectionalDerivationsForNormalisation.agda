module CMLBidirectionalDerivationsForNormalisation where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import CMLPropositions
open import CMLDerivations


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢_normal[_]
  data _⊢_normal[_] : List Assert → Prop → List Prop → Set
    where
      lam : ∀ {A B Δ Γ} → Δ ⊢ B normal[ Γ , A ]
                        → Δ ⊢ A ⊃ B normal[ Γ ]

      box : ∀ {A Ψ Δ Γ} → Δ ⊢ A valid[ Ψ ]
                        → Δ ⊢ [ Ψ ] A normal[ Γ ]

      letbox : ∀ {A B Ψ Δ Γ} → Δ ⊢ [ Ψ ] A neutral[ Γ ] → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ B normal[ Γ ]
                             → Δ ⊢ B normal[ Γ ]

      use : ∀ {P Δ Γ} → Δ ⊢ ι P neutral[ Γ ]
                      → Δ ⊢ ι P normal[ Γ ]

  infix 3 _⊢_neutral[_]
  data _⊢_neutral[_] : List Assert → Prop → List Prop → Set
    where
      var : ∀ {A Δ Γ} → Γ ∋ A
                      → Δ ⊢ A neutral[ Γ ]

      app : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B neutral[ Γ ] → Δ ⊢ A normal[ Γ ]
                        → Δ ⊢ B neutral[ Γ ]

      mvar : ∀ {A Ψ Δ Γ} → Δ ∋ ⟪ Ψ ⊫ A ⟫ → Δ ⊢ Ψ allnormal[ Γ ]
                         → Δ ⊢ A neutral[ Γ ]

  infix 3 _⊢_allnormal[_]
  _⊢_allnormal[_] : List Assert → List Prop → List Prop → Set
  Δ ⊢ Ξ allnormal[ Γ ] = All (\ A → Δ ⊢ A normal[ Γ ]) Ξ


--------------------------------------------------------------------------------


mutual
  renₗ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⊢ A normal[ Γ ]
                      → Δ ⊢ A normal[ Γ′ ]
  renₗ η (lam 𝒟)      = lam (renₗ (keep η) 𝒟)
  renₗ η (box 𝒟)      = box 𝒟
  renₗ η (letbox 𝒟 ℰ) = letbox (renᵣ η 𝒟) (renₗ η ℰ)
  renₗ η (use 𝒟)      = use (renᵣ η 𝒟)

  rensₗ : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⊢ Ξ allnormal[ Γ ]
                       → Δ ⊢ Ξ allnormal[ Γ′ ]
  rensₗ η ∙       = ∙
  rensₗ η (ξ , 𝒟) = rensₗ η ξ , renₗ η 𝒟

  renᵣ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⊢ A neutral[ Γ ]
                      → Δ ⊢ A neutral[ Γ′ ]
  renᵣ η (var i)    = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ)  = app (renᵣ η 𝒟) (renₗ η ℰ)
  renᵣ η (mvar i ψ) = mvar i (rensₗ η ψ)


wkᵣ : ∀ {B A Δ Γ} → Δ ⊢ A neutral[ Γ ]
                  → Δ ⊢ A neutral[ Γ , B ]
wkᵣ 𝒟 = renᵣ (drop id⊇) 𝒟


vzᵣ : ∀ {A Δ Γ} → Δ ⊢ A neutral[ Γ , A ]
vzᵣ = var zero


--------------------------------------------------------------------------------


mutual
  mrenₗ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⊢ A normal[ Γ ]
                       → Δ′ ⊢ A normal[ Γ ]
  mrenₗ η (lam 𝒟)      = lam (mrenₗ η 𝒟)
  mrenₗ η (box 𝒟)      = box (mren η 𝒟)
  mrenₗ η (letbox 𝒟 ℰ) = letbox (mrenᵣ η 𝒟) (mrenₗ (keep η) ℰ)
  mrenₗ η (use 𝒟)      = use (mrenᵣ η 𝒟)

  mrensₗ : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⊢ Ξ allnormal[ Γ ]
                        → Δ′ ⊢ Ξ allnormal[ Γ ]
  mrensₗ η ∙       = ∙
  mrensₗ η (ξ , 𝒟) = mrensₗ η ξ , mrenₗ η 𝒟

  mrenᵣ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⊢ A neutral[ Γ ]
                       → Δ′ ⊢ A neutral[ Γ ]
  mrenᵣ η (var i)    = var i
  mrenᵣ η (app 𝒟 ℰ)  = app (mrenᵣ η 𝒟) (mrenₗ η ℰ)
  mrenᵣ η (mvar i ψ) = mvar (ren∋ η i) (mrensₗ η ψ)


mwkₗ : ∀ {B A Δ Γ} → Δ ⊢ A normal[ Γ ]
                   → Δ , B ⊢ A normal[ Γ ]
mwkₗ 𝒟 = mrenₗ (drop id⊇) 𝒟


mwksₗ : ∀ {A Δ Γ Ξ} → Δ ⊢ Ξ allnormal[ Γ ]
                    → Δ , A ⊢ Ξ allnormal[ Γ ]
mwksₗ ξ = maps mwkₗ ξ


mwkᵣ : ∀ {B A Δ Γ} → Δ ⊢ A neutral[ Γ ]
                   → Δ , B ⊢ A neutral[ Γ ]
mwkᵣ 𝒟 = mrenᵣ (drop id⊇) 𝒟


mvzᵣ : ∀ {A Ψ Δ Γ} → Δ ⊢ Ψ allnormal[ Γ ]
                   → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ A neutral[ Γ ]
mvzᵣ ψ = mvar zero (mwksₗ ψ)


xmvzᵣ : ∀ {A Ψ Δ Δ′ Γ} → Δ′ ⊇ Δ , ⟪ Ψ ⊫ A ⟫ → Δ′ ⊢ Ψ allnormal[ Γ ]
                       → Δ′ ⊢ A neutral[ Γ ]
xmvzᵣ η ψ = mvar (ren∋ η zero) ψ


--------------------------------------------------------------------------------


mutual
  denmₗ : ∀ {Δ Γ A} → Δ ⊢ A normal[ Γ ]
                    → Δ ⊢ A valid[ Γ ]
  denmₗ (lam 𝒟)      = lam (denmₗ 𝒟)
  denmₗ (box 𝒟)      = box 𝒟
  denmₗ (letbox 𝒟 ℰ) = letbox (denmᵣ 𝒟) (denmₗ ℰ)
  denmₗ (use 𝒟)      = denmᵣ 𝒟

  denmsₗ : ∀ {Δ Γ Ξ} → Δ ⊢ Ξ allnormal[ Γ ]
                     → Δ ⊢ Ξ allvalid[ Γ ]
  denmsₗ ∙       = ∙
  denmsₗ (ξ , 𝒟) = denmsₗ ξ , denmₗ 𝒟

  denmᵣ : ∀ {Δ Γ A} → Δ ⊢ A neutral[ Γ ]
                    → Δ ⊢ A valid[ Γ ]
  denmᵣ (var i)    = var i
  denmᵣ (app 𝒟 ℰ)  = app (denmᵣ 𝒟) (denmₗ ℰ)
  denmᵣ (mvar i ψ) = mvar i (denmsₗ ψ)


--------------------------------------------------------------------------------
