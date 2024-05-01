module FullIPLBidirectionalDerivationsForNormalisation where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import FullIPLPropositions
open import FullIPLDerivations


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢_normal
  data _⊢_normal : List Form → Form → Set
    where
      lam : ∀ {A B Γ} → Γ , A ⊢ B normal
                      → Γ ⊢ A ⊃ B normal

      pair : ∀ {A B Γ} → Γ ⊢ A normal → Γ ⊢ B normal
                       → Γ ⊢ A ∧ B normal

      unit : ∀ {Γ} → Γ ⊢ 𝟏 normal

      abort : ∀ {A Γ} → Γ ⊢ 𝟎 neutral
                      → Γ ⊢ A normal

      inl : ∀ {A B Γ} → Γ ⊢ A normal
                      → Γ ⊢ A ∨ B normal

      inr : ∀ {A B Γ} → Γ ⊢ B normal
                      → Γ ⊢ A ∨ B normal

      case : ∀ {A B C Γ} → Γ ⊢ A ∨ B neutral → Γ , A ⊢ C normal → Γ , B ⊢ C normal
                         → Γ ⊢ C normal

      use : ∀ {P Γ} → Γ ⊢ ι P neutral
                    → Γ ⊢ ι P normal

  infix 3 _⊢_neutral
  data _⊢_neutral : List Form → Form → Set
    where
      var : ∀ {A Γ} → Γ ∋ A
                    → Γ ⊢ A neutral

      app : ∀ {A B Γ} → Γ ⊢ A ⊃ B neutral → Γ ⊢ A normal
                      → Γ ⊢ B neutral

      fst : ∀ {A B Γ} → Γ ⊢ A ∧ B neutral
                      → Γ ⊢ A neutral

      snd : ∀ {A B Γ} → Γ ⊢ A ∧ B neutral
                      → Γ ⊢ B neutral


--------------------------------------------------------------------------------


mutual
  renᵣ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A normal
                    → Γ′ ⊢ A normal
  renᵣ η (lam 𝒟)      = lam (renᵣ (keep η) 𝒟)
  renᵣ η (pair 𝒟 ℰ)   = pair (renᵣ η 𝒟) (renᵣ η ℰ)
  renᵣ η unit         = unit
  renᵣ η (abort 𝒟)    = abort (renₗ η 𝒟)
  renᵣ η (inl 𝒟)      = inl (renᵣ η 𝒟)
  renᵣ η (inr 𝒟)      = inr (renᵣ η 𝒟)
  renᵣ η (case 𝒟 ℰ ℱ) = case (renₗ η 𝒟) (renᵣ (keep η) ℰ) (renᵣ (keep η) ℱ)
  renᵣ η (use 𝒟)      = use (renₗ η 𝒟)

  renₗ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A neutral
                    → Γ′ ⊢ A neutral
  renₗ η (var i)   = var (ren∋ η i)
  renₗ η (app 𝒟 ℰ) = app (renₗ η 𝒟) (renᵣ η ℰ)
  renₗ η (fst 𝒟)   = fst (renₗ η 𝒟)
  renₗ η (snd 𝒟)   = snd (renₗ η 𝒟)


--------------------------------------------------------------------------------


wkₗ : ∀ {B Γ A} → Γ ⊢ A neutral
                → Γ , B ⊢ A neutral
wkₗ 𝒟 = renₗ (drop id) 𝒟


vzₗ : ∀ {Γ A} → Γ , A ⊢ A neutral
vzₗ = var zero


--------------------------------------------------------------------------------


mutual
  denmᵣ : ∀ {Γ A} → Γ ⊢ A normal
                  → Γ ⊢ A true
  denmᵣ (lam 𝒟)      = lam (denmᵣ 𝒟)
  denmᵣ (pair 𝒟 ℰ)   = pair (denmᵣ 𝒟) (denmᵣ ℰ)
  denmᵣ unit         = unit
  denmᵣ (abort 𝒟)    = abort (denmₗ 𝒟)
  denmᵣ (inl 𝒟)      = inl (denmᵣ 𝒟)
  denmᵣ (inr 𝒟)      = inr (denmᵣ 𝒟)
  denmᵣ (case 𝒟 ℰ ℱ) = case (denmₗ 𝒟) (denmᵣ ℰ) (denmᵣ ℱ)
  denmᵣ (use 𝒟)      = denmₗ 𝒟

  denmₗ : ∀ {Γ A} → Γ ⊢ A neutral
                  → Γ ⊢ A true
  denmₗ (var i)   = var i
  denmₗ (app 𝒟 ℰ) = app (denmₗ 𝒟) (denmᵣ ℰ)
  denmₗ (fst 𝒟)   = fst (denmₗ 𝒟)
  denmₗ (snd 𝒟)   = snd (denmₗ 𝒟)


--------------------------------------------------------------------------------
