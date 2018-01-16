module SimpleIPLVerifications where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import IPLPropositions
open import SimpleIPLDerivations


--------------------------------------------------------------------------------


-- We read “A₁, …, Aₙ ⊢ₗ A” as “from the assumptions that A₁ may be used …,
-- and that Aₙ may be used, we deduce that A has a verification”.
--
-- We read “A₁, …, Aₙ ⊢ᵣ A” as “from the assumptions that A₁ may be used …,
-- and that Aₙ may be used, we deduce that A may be used”.

mutual
  infix 3 _⊢ₗ_
  data _⊢ₗ_ : List Truth → Truth → Set
    where
      lam : ∀ {A B Γ} → Γ , A true ⊢ₗ B true
                      → Γ ⊢ₗ A ⊃ B true

      use : ∀ {Γ} → Γ ⊢ᵣ BASE true
                  → Γ ⊢ₗ BASE true

  infix 3 _⊢ᵣ_
  data _⊢ᵣ_ : List Truth → Truth → Set
    where
      var : ∀ {A Γ} → Γ ∋ A true
                    → Γ ⊢ᵣ A true

      app : ∀ {A B Γ} → Γ ⊢ᵣ A ⊃ B true → Γ ⊢ₗ A true
                      → Γ ⊢ᵣ B true


--------------------------------------------------------------------------------


mutual
  recoverL : ∀ {Γ A} → Γ ⊢ₗ A true
                 → Γ ⊢ A true
  recoverL (lam 𝒟) = lam (recoverL 𝒟)
  recoverL (use 𝒟) = recoverR 𝒟

  recoverR : ∀ {Γ A} → Γ ⊢ᵣ A true
                 → Γ ⊢ A true
  recoverR (var i)   = var i
  recoverR (app 𝒟 ℰ) = app (recoverR 𝒟) (recoverL ℰ)


--------------------------------------------------------------------------------


mutual
  renL : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ₗ A true
                    → Γ′ ⊢ₗ A true
  renL η (lam 𝒟) = lam (renL (keep η) 𝒟)
  renL η (use 𝒟) = use (renR η 𝒟)

  renR : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ᵣ A true
                    → Γ′ ⊢ᵣ A true
  renR η (var i)   = var (ren∋ η i)
  renR η (app 𝒟 ℰ) = app (renR η 𝒟) (renL η ℰ)


wkR : ∀ {B A Γ} → Γ ⊢ᵣ A true
                → Γ , B ⊢ᵣ A true
wkR 𝒟 = renR (drop id) 𝒟


vzR : ∀ {A Γ} → Γ , A true ⊢ᵣ A true
vzR = var zero


--------------------------------------------------------------------------------
