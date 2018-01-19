module S4BidirectionalDerivationsForNormalisation where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions
open import S4Derivations


--------------------------------------------------------------------------------


mutual
  infix 3 _⨾_⊢ₗ_
  data _⨾_⊢ₗ_ : List Validity → List Truth → Truth → Set
    where
      lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A true ⊢ₗ B true
                        → Δ ⨾ Γ ⊢ₗ A ⊃ B true

      box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                      → Δ ⨾ Γ ⊢ₗ □ A true

      letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ᵣ □ A true → Δ , A valid ⨾ Γ ⊢ₗ B true
                           → Δ ⨾ Γ ⊢ₗ B true

      use : ∀ {Δ Γ} → Δ ⨾ Γ ⊢ᵣ BASE true
                    → Δ ⨾ Γ ⊢ₗ BASE true

  infix 3 _⨾_⊢ᵣ_
  data _⨾_⊢ᵣ_ : List Validity → List Truth → Truth → Set
    where
      var : ∀ {A Δ Γ} → Γ ∋ A true
                      → Δ ⨾ Γ ⊢ᵣ A true

      app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ᵣ A ⊃ B true → Δ ⨾ Γ ⊢ₗ A true
                        → Δ ⨾ Γ ⊢ᵣ B true

      mvar : ∀ {A Δ Γ} → Δ ∋ A valid
                       → Δ ⨾ Γ ⊢ᵣ A true


--------------------------------------------------------------------------------


mutual
  recoverL : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ₗ A true
                   → Δ ⨾ Γ ⊢ A true
  recoverL (lam 𝒟)      = lam (recoverL 𝒟)
  recoverL (box 𝒟)      = box 𝒟
  recoverL (letbox 𝒟 ℰ) = letbox (recoverR 𝒟) (recoverL ℰ)
  recoverL (use 𝒟)      = recoverR 𝒟

  recoverR : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ᵣ A true
                   → Δ ⨾ Γ ⊢ A true
  recoverR (var i)   = var i
  recoverR (app 𝒟 ℰ) = app (recoverR 𝒟) (recoverL ℰ)
  recoverR (mvar i)  = mvar i


--------------------------------------------------------------------------------


mutual
  renL : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ₗ A true
                      → Δ ⨾ Γ′ ⊢ₗ A true
  renL η (lam 𝒟)      = lam (renL (keep η) 𝒟)
  renL η (box 𝒟)      = box 𝒟
  renL η (letbox 𝒟 ℰ) = letbox (renR η 𝒟) (renL η ℰ)
  renL η (use 𝒟)      = use (renR η 𝒟)

  renR : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ᵣ A true
                      → Δ ⨾ Γ′ ⊢ᵣ A true
  renR η (var i)   = var (ren∋ η i)
  renR η (app 𝒟 ℰ) = app (renR η 𝒟) (renL η ℰ)
  renR η (mvar i)  = mvar i


wkR : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ᵣ A true
                  → Δ ⨾ Γ , B true ⊢ᵣ A true
wkR 𝒟 = renR (drop id⊇) 𝒟


vzR : ∀ {A Δ Γ} → Δ ⨾ Γ , A true ⊢ᵣ A true
vzR = var zero


--------------------------------------------------------------------------------


mutual
  mrenL : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ₗ A true
                       → Δ′ ⨾ Γ ⊢ₗ A true
  mrenL η (lam 𝒟)      = lam (mrenL η 𝒟)
  mrenL η (box 𝒟)      = box (mren η 𝒟)
  mrenL η (letbox 𝒟 ℰ) = letbox (mrenR η 𝒟) (mrenL (keep η) ℰ)
  mrenL η (use 𝒟)      = use (mrenR η 𝒟)

  mrenR : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ᵣ A true
                       → Δ′ ⨾ Γ ⊢ᵣ A true
  mrenR η (var i)   = var i
  mrenR η (app 𝒟 ℰ) = app (mrenR η 𝒟) (mrenL η ℰ)
  mrenR η (mvar i)  = mvar (ren∋ η i)


mwkR : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ᵣ A true
                   → Δ , B valid ⨾ Γ ⊢ᵣ A true
mwkR 𝒟 = mrenR (drop id⊇) 𝒟


mvzR : ∀ {A Δ Γ} → Δ , A valid ⨾ Γ ⊢ᵣ A true
mvzR = mvar zero


--------------------------------------------------------------------------------
