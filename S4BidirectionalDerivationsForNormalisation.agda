module S4BidirectionalDerivationsForNormalisation where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions
open import S4Derivations


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢_checkable[_]
  data _⊢_checkable[_] : List Assert → Prop → List Prop → Set
    where
      lam : ∀ {A B Δ Γ} → Δ ⊢ B checkable[ Γ , A ]
                        → Δ ⊢ A ⊃ B checkable[ Γ ]

      box : ∀ {A Δ Γ} → Δ ⊢ A valid[ ∙ ]
                      → Δ ⊢ □ A checkable[ Γ ]

      letbox : ∀ {A B Δ Γ} → Δ ⊢ □ A usable[ Γ ] → Δ , ⟪⊫ A ⟫ ⊢ B checkable[ Γ ]
                           → Δ ⊢ B checkable[ Γ ]

      use : ∀ {P Δ Γ} → Δ ⊢ ι P usable[ Γ ]
                      → Δ ⊢ ι P checkable[ Γ ]

  infix 3 _⊢_usable[_]
  data _⊢_usable[_] : List Assert → Prop → List Prop → Set
    where
      var : ∀ {A Δ Γ} → Γ ∋ A
                      → Δ ⊢ A usable[ Γ ]

      app : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B usable[ Γ ] → Δ ⊢ A checkable[ Γ ]
                        → Δ ⊢ B usable[ Γ ]

      mvar : ∀ {A Δ Γ} → Δ ∋ ⟪⊫ A ⟫
                       → Δ ⊢ A usable[ Γ ]


--------------------------------------------------------------------------------


mutual
  renₗ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⊢ A checkable[ Γ ]
                      → Δ ⊢ A checkable[ Γ′ ]
  renₗ η (lam 𝒟)      = lam (renₗ (keep η) 𝒟)
  renₗ η (box 𝒟)      = box 𝒟
  renₗ η (letbox 𝒟 ℰ) = letbox (renᵣ η 𝒟) (renₗ η ℰ)
  renₗ η (use 𝒟)      = use (renᵣ η 𝒟)

  renᵣ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⊢ A usable[ Γ ]
                      → Δ ⊢ A usable[ Γ′ ]
  renᵣ η (var i)   = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₗ η ℰ)
  renᵣ η (mvar i)  = mvar i


wkᵣ : ∀ {B A Δ Γ} → Δ ⊢ A usable[ Γ ]
                  → Δ ⊢ A usable[ Γ , B ]
wkᵣ 𝒟 = renᵣ (drop id⊇) 𝒟


vzᵣ : ∀ {A Δ Γ} → Δ ⊢ A usable[ Γ , A ]
vzᵣ = var zero


--------------------------------------------------------------------------------


mutual
  mrenₗ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⊢ A checkable[ Γ ]
                       → Δ′ ⊢ A checkable[ Γ ]
  mrenₗ η (lam 𝒟)      = lam (mrenₗ η 𝒟)
  mrenₗ η (box 𝒟)      = box (mren η 𝒟)
  mrenₗ η (letbox 𝒟 ℰ) = letbox (mrenᵣ η 𝒟) (mrenₗ (keep η) ℰ)
  mrenₗ η (use 𝒟)      = use (mrenᵣ η 𝒟)

  mrenᵣ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⊢ A usable[ Γ ]
                       → Δ′ ⊢ A usable[ Γ ]
  mrenᵣ η (var i)   = var i
  mrenᵣ η (app 𝒟 ℰ) = app (mrenᵣ η 𝒟) (mrenₗ η ℰ)
  mrenᵣ η (mvar i)  = mvar (ren∋ η i)


mwkᵣ : ∀ {B A Δ Γ} → Δ ⊢ A usable[ Γ ]
                   → Δ , B ⊢ A usable[ Γ ]
mwkᵣ 𝒟 = mrenᵣ (drop id⊇) 𝒟


mvzᵣ : ∀ {A Δ Γ} → Δ , ⟪⊫ A ⟫ ⊢ A usable[ Γ ]
mvzᵣ = mvar zero


--------------------------------------------------------------------------------


mutual
  denmₗ : ∀ {Δ Γ A} → Δ ⊢ A checkable[ Γ ]
                    → Δ ⊢ A valid[ Γ ]
  denmₗ (lam 𝒟)      = lam (denmₗ 𝒟)
  denmₗ (box 𝒟)      = box 𝒟
  denmₗ (letbox 𝒟 ℰ) = letbox (denmᵣ 𝒟) (denmₗ ℰ)
  denmₗ (use 𝒟)      = denmᵣ 𝒟

  denmᵣ : ∀ {Δ Γ A} → Δ ⊢ A usable[ Γ ]
                    → Δ ⊢ A valid[ Γ ]
  denmᵣ (var i)   = var i
  denmᵣ (app 𝒟 ℰ) = app (denmᵣ 𝒟) (denmₗ ℰ)
  denmᵣ (mvar i)  = mvar i


--------------------------------------------------------------------------------
