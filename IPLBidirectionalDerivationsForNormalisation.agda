module IPLBidirectionalDerivationsForNormalisation where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import IPLPropositions
open import IPLDerivations


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢_normal
  data _⊢_normal : List Prop → Prop → Set
    where
      lam : ∀ {A B Γ} → Γ , A ⊢ B normal
                      → Γ ⊢ A ⊃ B normal

      use : ∀ {P Γ} → Γ ⊢ ι P neutral
                    → Γ ⊢ ι P normal

  infix 3 _⊢_neutral
  data _⊢_neutral : List Prop → Prop → Set
    where
      var : ∀ {A Γ} → Γ ∋ A
                    → Γ ⊢ A neutral

      app : ∀ {A B Γ} → Γ ⊢ A ⊃ B neutral → Γ ⊢ A normal
                      → Γ ⊢ B neutral


--------------------------------------------------------------------------------


mutual
  renₗ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A normal
                    → Γ′ ⊢ A normal
  renₗ η (lam 𝒟) = lam (renₗ (keep η) 𝒟)
  renₗ η (use 𝒟) = use (renᵣ η 𝒟)

  renᵣ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A neutral
                    → Γ′ ⊢ A neutral
  renᵣ η (var i)   = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₗ η ℰ)


--------------------------------------------------------------------------------


wkᵣ : ∀ {B A Γ} → Γ ⊢ A neutral
                → Γ , B ⊢ A neutral
wkᵣ 𝒟 = renᵣ (drop id) 𝒟


vzᵣ : ∀ {A Γ} → Γ , A ⊢ A neutral
vzᵣ = var zero


--------------------------------------------------------------------------------


mutual
  denmₗ : ∀ {Γ A} → Γ ⊢ A normal
                  → Γ ⊢ A true
  denmₗ (lam 𝒟) = lam (denmₗ 𝒟)
  denmₗ (use 𝒟) = denmᵣ 𝒟

  denmᵣ : ∀ {Γ A} → Γ ⊢ A neutral
                  → Γ ⊢ A true
  denmᵣ (var i)   = var i
  denmᵣ (app 𝒟 ℰ) = app (denmᵣ 𝒟) (denmₗ ℰ)


--------------------------------------------------------------------------------
