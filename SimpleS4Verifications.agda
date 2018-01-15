module SimpleS4Verifications where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions
open import SimpleS4Derivations


--------------------------------------------------------------------------------


mutual
  infix 3 _⨾_⊢ᵥ_
  data _⨾_⊢ᵥ_ : List Validity → List Truth → Truth → Set
    where
      lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A true ⊢ᵥ B true
                        → Δ ⨾ Γ ⊢ᵥ A ⊃ B true

      box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                      → Δ ⨾ Γ ⊢ᵥ □ A true

      letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ᵤ □ A true → Δ , A valid ⨾ Γ ⊢ᵥ B true
                           → Δ ⨾ Γ ⊢ᵥ B true

      use : ∀ {Δ Γ} → Δ ⨾ Γ ⊢ᵤ BASE true
                    → Δ ⨾ Γ ⊢ᵥ BASE true

  infix 3 _⨾_⊢ᵤ_
  data _⨾_⊢ᵤ_ : List Validity → List Truth → Truth → Set
    where
      var : ∀ {A Δ Γ} → Γ ∋ A true
                      → Δ ⨾ Γ ⊢ᵤ A true

      app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ᵤ A ⊃ B true → Δ ⨾ Γ ⊢ᵥ A true
                        → Δ ⨾ Γ ⊢ᵤ B true

      mvar : ∀ {A Δ Γ} → Δ ∋ A valid
                       → Δ ⨾ Γ ⊢ᵤ A true


--------------------------------------------------------------------------------


mutual
  recV : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ᵥ A true
                   → Δ ⨾ Γ ⊢ A true
  recV (lam 𝒟)      = lam (recV 𝒟)
  recV (box 𝒟)      = box 𝒟
  recV (letbox 𝒟 ℰ) = letbox (recU 𝒟) (recV ℰ)
  recV (use 𝒟)      = recU 𝒟

  recU : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ᵤ A true
                   → Δ ⨾ Γ ⊢ A true
  recU (var i)   = var i
  recU (app 𝒟 ℰ) = app (recU 𝒟) (recV ℰ)
  recU (mvar i)  = mvar i


--------------------------------------------------------------------------------


mutual
  renV : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ᵥ A true
                      → Δ ⨾ Γ′ ⊢ᵥ A true
  renV η (lam 𝒟)      = lam (renV (keep η) 𝒟)
  renV η (box 𝒟)      = box 𝒟
  renV η (letbox 𝒟 ℰ) = letbox (renU η 𝒟) (renV η ℰ)
  renV η (use 𝒟)      = use (renU η 𝒟)

  renU : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ᵤ A true
                      → Δ ⨾ Γ′ ⊢ᵤ A true
  renU η (var i)   = var (ren∋ η i)
  renU η (app 𝒟 ℰ) = app (renU η 𝒟) (renV η ℰ)
  renU η (mvar i)  = mvar i


wkU : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ᵤ A true
                  → Δ ⨾ Γ , B true ⊢ᵤ A true
wkU 𝒟 = renU (drop id⊇) 𝒟


vzU : ∀ {A Δ Γ} → Δ ⨾ Γ , A true ⊢ᵤ A true
vzU = var zero


--------------------------------------------------------------------------------


mutual
  mrenV : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ᵥ A true
                       → Δ′ ⨾ Γ ⊢ᵥ A true
  mrenV η (lam 𝒟)      = lam (mrenV η 𝒟)
  mrenV η (box 𝒟)      = box (mren η 𝒟)
  mrenV η (letbox 𝒟 ℰ) = letbox (mrenU η 𝒟) (mrenV (keep η) ℰ)
  mrenV η (use 𝒟)      = use (mrenU η 𝒟)

  mrenU : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ᵤ A true
                       → Δ′ ⨾ Γ ⊢ᵤ A true
  mrenU η (var i)   = var i
  mrenU η (app 𝒟 ℰ) = app (mrenU η 𝒟) (mrenV η ℰ)
  mrenU η (mvar i)  = mvar (ren∋ η i)


mwkU : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ᵤ A true
                   → Δ , B valid ⨾ Γ ⊢ᵤ A true
mwkU 𝒟 = mrenU (drop id⊇) 𝒟


mvzU : ∀ {A Δ Γ} → Δ , A valid ⨾ Γ ⊢ᵤ A true
mvzU = mvar zero


--------------------------------------------------------------------------------
