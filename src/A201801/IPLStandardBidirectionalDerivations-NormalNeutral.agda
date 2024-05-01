module A201801.IPLStandardBidirectionalDerivations-NormalNeutral where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.IPLPropositions
open import A201801.IPLStandardDerivations


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢_normal
  data _⊢_normal : List Form → Form → Set
    where
      lam : ∀ {A B Γ} → Γ , A ⊢ B normal
                      → Γ ⊢ A ⊃ B normal

      neu : ∀ {P Γ} → Γ ⊢ ι P neutral
                    → Γ ⊢ ι P normal

  infix 3 _⊢_neutral
  data _⊢_neutral : List Form → Form → Set
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
  renₗ η (neu 𝒟) = neu (renᵣ η 𝒟)

  renᵣ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A neutral
                    → Γ′ ⊢ A neutral
  renᵣ η (var i)   = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₗ η ℰ)


--------------------------------------------------------------------------------


wkᵣ : ∀ {B Γ A} → Γ ⊢ A neutral
                → Γ , B ⊢ A neutral
wkᵣ 𝒟 = renᵣ (drop id) 𝒟


vzᵣ : ∀ {Γ A} → Γ , A ⊢ A neutral
vzᵣ = var zero


--------------------------------------------------------------------------------


mutual
  denmₗ : ∀ {Γ A} → Γ ⊢ A normal
                  → Γ ⊢ A true
  denmₗ (lam 𝒟) = lam (denmₗ 𝒟)
  denmₗ (neu 𝒟) = denmᵣ 𝒟

  denmᵣ : ∀ {Γ A} → Γ ⊢ A neutral
                  → Γ ⊢ A true
  denmᵣ (var i)   = var i
  denmᵣ (app 𝒟 ℰ) = app (denmᵣ 𝒟) (denmₗ ℰ)


--------------------------------------------------------------------------------
