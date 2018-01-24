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
  forgetₗ : ∀ {Γ A} → Γ ⊢ A verifiable
                    → Γ ⊢ A true
  forgetₗ (lam 𝒟) = lam (forgetₗ 𝒟)
  forgetₗ (use 𝒟) = forgetᵣ 𝒟

  forgetᵣ : ∀ {Γ A} → Γ ⊢ A usable
                    → Γ ⊢ A true
  forgetᵣ (var i)   = var i
  forgetᵣ (app 𝒟 ℰ) = app (forgetᵣ 𝒟) (forgetₗ ℰ)


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


wkᵣ : ∀ {B A Γ} → Γ ⊢ A usable
                → Γ , B ⊢ A usable
wkᵣ 𝒟 = renᵣ (drop id) 𝒟


vzᵣ : ∀ {A Γ} → Γ , A ⊢ A usable
vzᵣ = var zero


--------------------------------------------------------------------------------
