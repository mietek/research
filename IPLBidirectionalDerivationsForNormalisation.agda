module IPLBidirectionalDerivationsForNormalisation where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import IPLPropositions
open import IPLDerivations


--------------------------------------------------------------------------------


-- We read “A₁, …, Aₙ ⊢ₗ A” as “from the assumptions that A₁ may be used …,
-- and that Aₙ may be used, we deduce that A has a verification”.
--
-- We read “A₁, …, Aₙ ⊢ᵣ A” as “from the assumptions that A₁ may be used …,
-- and that Aₙ may be used, we deduce that A may be used”.

-- TODO: Explicit judgments

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
  forgetₗ : ∀ {Γ A} → Γ ⊢ₗ A true
                    → Γ ⊢ A true
  forgetₗ (lam 𝒟) = lam (forgetₗ 𝒟)
  forgetₗ (use 𝒟) = forgetᵣ 𝒟

  forgetᵣ : ∀ {Γ A} → Γ ⊢ᵣ A true
                    → Γ ⊢ A true
  forgetᵣ (var i)   = var i
  forgetᵣ (app 𝒟 ℰ) = app (forgetᵣ 𝒟) (forgetₗ ℰ)


--------------------------------------------------------------------------------


mutual
  renₗ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ₗ A true
                    → Γ′ ⊢ₗ A true
  renₗ η (lam 𝒟) = lam (renₗ (keep η) 𝒟)
  renₗ η (use 𝒟) = use (renᵣ η 𝒟)

  renᵣ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ᵣ A true
                    → Γ′ ⊢ᵣ A true
  renᵣ η (var i)   = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₗ η ℰ)


wkᵣ : ∀ {B A Γ} → Γ ⊢ᵣ A true
                → Γ , B ⊢ᵣ A true
wkᵣ 𝒟 = renᵣ (drop id) 𝒟


vzᵣ : ∀ {A Γ} → Γ , A true ⊢ᵣ A true
vzᵣ = var zero


--------------------------------------------------------------------------------
