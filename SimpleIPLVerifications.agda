module SimpleIPLVerifications where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import IPLPropositions
open import SimpleIPLDerivations


--------------------------------------------------------------------------------


-- We read “A₁, …, Aₙ ⊢ᵥ A” as “from the assumptions that A₁ may be used …,
-- and that Aₙ may be used, we deduce that A has a verification”.
--
-- We read “A₁, …, Aₙ ⊢ᵤ A” as “from the assumptions that A₁ may be used …,
-- and that Aₙ may be used, we deduce that A may be used”.

mutual
  infix 3 _⊢ᵥ_
  data _⊢ᵥ_ : List Truth → Truth → Set
    where
      lam : ∀ {A B Γ} → Γ , A true ⊢ᵥ B true
                      → Γ ⊢ᵥ A ⊃ B true

      use : ∀ {Γ} → Γ ⊢ᵤ BASE true
                  → Γ ⊢ᵥ BASE true

  infix 3 _⊢ᵤ_
  data _⊢ᵤ_ : List Truth → Truth → Set
    where
      var : ∀ {A Γ} → Γ ∋ A true
                    → Γ ⊢ᵤ A true

      app : ∀ {A B Γ} → Γ ⊢ᵤ A ⊃ B true → Γ ⊢ᵥ A true
                      → Γ ⊢ᵤ B true


--------------------------------------------------------------------------------


mutual
  recV : ∀ {Γ A} → Γ ⊢ᵥ A true
                 → Γ ⊢ A true
  recV (lam 𝒟) = lam (recV 𝒟)
  recV (use 𝒟) = recU 𝒟

  recU : ∀ {Γ A} → Γ ⊢ᵤ A true
                 → Γ ⊢ A true
  recU (var i)   = var i
  recU (app 𝒟 ℰ) = app (recU 𝒟) (recV ℰ)


--------------------------------------------------------------------------------


mutual
  renV : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ᵥ A true
                    → Γ′ ⊢ᵥ A true
  renV η (lam 𝒟) = lam (renV (keep η) 𝒟)
  renV η (use 𝒟) = use (renU η 𝒟)

  renU : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ᵤ A true
                    → Γ′ ⊢ᵤ A true
  renU η (var i)   = var (ren∋ η i)
  renU η (app 𝒟 ℰ) = app (renU η 𝒟) (renV η ℰ)


wkU : ∀ {B A Γ} → Γ ⊢ᵤ A true
                → Γ , B ⊢ᵤ A true
wkU 𝒟 = renU (drop id) 𝒟


vzU : ∀ {A Γ} → Γ , A true ⊢ᵤ A true
vzU = var zero


--------------------------------------------------------------------------------
