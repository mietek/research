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
  infix 3 _⊢_checkable
  data _⊢_checkable : List Prop → Prop → Set
    where
      lam : ∀ {A B Γ} → Γ , A ⊢ B checkable
                      → Γ ⊢ A ⊃ B checkable

      use : ∀ {P Γ} → Γ ⊢ ι P inferrable
                    → Γ ⊢ ι P checkable

  infix 3 _⊢_inferrable
  data _⊢_inferrable : List Prop → Prop → Set
    where
      var : ∀ {A Γ} → Γ ∋ A
                    → Γ ⊢ A inferrable

      app : ∀ {A B Γ} → Γ ⊢ A ⊃ B inferrable → Γ ⊢ A checkable
                      → Γ ⊢ B inferrable


--------------------------------------------------------------------------------


mutual
  renₗ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A checkable
                    → Γ′ ⊢ A checkable
  renₗ η (lam 𝒟) = lam (renₗ (keep η) 𝒟)
  renₗ η (use 𝒟) = use (renᵣ η 𝒟)

  renᵣ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A inferrable
                    → Γ′ ⊢ A inferrable
  renᵣ η (var i)   = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₗ η ℰ)


--------------------------------------------------------------------------------


wkᵣ : ∀ {B A Γ} → Γ ⊢ A inferrable
                → Γ , B ⊢ A inferrable
wkᵣ 𝒟 = renᵣ (drop id) 𝒟


vzᵣ : ∀ {A Γ} → Γ , A ⊢ A inferrable
vzᵣ = var zero


--------------------------------------------------------------------------------


mutual
  denmₗ : ∀ {Γ A} → Γ ⊢ A checkable
                  → Γ ⊢ A true
  denmₗ (lam 𝒟) = lam (denmₗ 𝒟)
  denmₗ (use 𝒟) = denmᵣ 𝒟

  denmᵣ : ∀ {Γ A} → Γ ⊢ A inferrable
                  → Γ ⊢ A true
  denmᵣ (var i)   = var i
  denmᵣ (app 𝒟 ℰ) = app (denmᵣ 𝒟) (denmₗ ℰ)


--------------------------------------------------------------------------------
