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
  data _⊢_normal : List Prop → Prop → Set
    where
      lam : ∀ {A B Γ} → Γ , A ⊢ B normal
                      → Γ ⊢ A ⊃ B normal

      pair : ∀ {A B Γ} → Γ ⊢ A normal → Γ ⊢ B normal
                       → Γ ⊢ A ∧ B normal

      unit : ∀ {Γ} → Γ ⊢ ⊤ normal

      abort : ∀ {A Γ} → Γ ⊢ ⊥ neutral
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
  data _⊢_neutral : List Prop → Prop → Set
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
  renₗ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A normal
                    → Γ′ ⊢ A normal
  renₗ η (lam 𝒟)      = lam (renₗ (keep η) 𝒟)
  renₗ η (pair 𝒟 ℰ)   = pair (renₗ η 𝒟) (renₗ η ℰ)
  renₗ η unit         = unit
  renₗ η (abort 𝒟)    = abort (renᵣ η 𝒟)
  renₗ η (inl 𝒟)      = inl (renₗ η 𝒟)
  renₗ η (inr 𝒟)      = inr (renₗ η 𝒟)
  renₗ η (case 𝒟 ℰ ℱ) = case (renᵣ η 𝒟) (renₗ (keep η) ℰ) (renₗ (keep η) ℱ)
  renₗ η (use 𝒟)      = use (renᵣ η 𝒟)

  renᵣ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A neutral
                    → Γ′ ⊢ A neutral
  renᵣ η (var i)   = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₗ η ℰ)
  renᵣ η (fst 𝒟)   = fst (renᵣ η 𝒟)
  renᵣ η (snd 𝒟)   = snd (renᵣ η 𝒟)


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
  denmₗ (lam 𝒟)      = lam (denmₗ 𝒟)
  denmₗ (pair 𝒟 ℰ)   = pair (denmₗ 𝒟) (denmₗ ℰ)
  denmₗ unit         = unit
  denmₗ (abort 𝒟)    = abort (denmᵣ 𝒟)
  denmₗ (inl 𝒟)      = inl (denmₗ 𝒟)
  denmₗ (inr 𝒟)      = inr (denmₗ 𝒟)
  denmₗ (case 𝒟 ℰ ℱ) = case (denmᵣ 𝒟) (denmₗ ℰ) (denmₗ ℱ)
  denmₗ (use 𝒟)      = denmᵣ 𝒟

  denmᵣ : ∀ {Γ A} → Γ ⊢ A neutral
                  → Γ ⊢ A true
  denmᵣ (var i)   = var i
  denmᵣ (app 𝒟 ℰ) = app (denmᵣ 𝒟) (denmₗ ℰ)
  denmᵣ (fst 𝒟)   = fst (denmᵣ 𝒟)
  denmᵣ (snd 𝒟)   = snd (denmᵣ 𝒟)


--------------------------------------------------------------------------------
