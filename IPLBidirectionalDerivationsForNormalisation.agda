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
  infix 3 _⊢_verifiable
  data _⊢_verifiable : List Prop → Prop → Set
    where
      lam : ∀ {A B Γ} → Γ , A ⊢ B verifiable
                      → Γ ⊢ A ⊃ B verifiable

      use : ∀ {P Γ} → Γ ⊢ ι P usable
                    → Γ ⊢ ι P verifiable

  infix 3 _⊢_usable
  data _⊢_usable : List Prop → Prop → Set
    where
      var : ∀ {A Γ} → Γ ∋ A
                    → Γ ⊢ A usable

      app : ∀ {A B Γ} → Γ ⊢ A ⊃ B usable → Γ ⊢ A verifiable
                      → Γ ⊢ B usable


--------------------------------------------------------------------------------


mutual
  renₗ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A verifiable
                    → Γ′ ⊢ A verifiable
  renₗ η (lam 𝒟) = lam (renₗ (keep η) 𝒟)
  renₗ η (use 𝒟) = use (renᵣ η 𝒟)

  renᵣ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A usable
                    → Γ′ ⊢ A usable
  renᵣ η (var i)   = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₗ η ℰ)


--------------------------------------------------------------------------------


wkᵣ : ∀ {B A Γ} → Γ ⊢ A usable
                → Γ , B ⊢ A usable
wkᵣ 𝒟 = renᵣ (drop id) 𝒟


vzᵣ : ∀ {A Γ} → Γ , A ⊢ A usable
vzᵣ = var zero


--------------------------------------------------------------------------------


mutual
  denmₗ : ∀ {Γ A} → Γ ⊢ A verifiable
                  → Γ ⊢ A true
  denmₗ (lam 𝒟) = lam (denmₗ 𝒟)
  denmₗ (use 𝒟) = denmᵣ 𝒟

  denmᵣ : ∀ {Γ A} → Γ ⊢ A usable
                  → Γ ⊢ A true
  denmᵣ (var i)   = var i
  denmᵣ (app 𝒟 ℰ) = app (denmᵣ 𝒟) (denmₗ ℰ)


--------------------------------------------------------------------------------
