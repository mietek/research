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
  infix 3 _⨾_⊢_verifiable
  data _⨾_⊢_verifiable : List Prop → List Prop → Prop → Set
    where
      lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A ⊢ B verifiable
                        → Δ ⨾ Γ ⊢ A ⊃ B verifiable

      box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                      → Δ ⨾ Γ ⊢ □ A verifiable

      letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ □ A usable → Δ , A ⨾ Γ ⊢ B verifiable
                           → Δ ⨾ Γ ⊢ B verifiable

      use : ∀ {Δ Γ} → Δ ⨾ Γ ⊢ BASE usable
                    → Δ ⨾ Γ ⊢  BASE verifiable

  infix 3 _⨾_⊢_usable
  data _⨾_⊢_usable : List Prop → List Prop → Prop → Set
    where
      var : ∀ {A Δ Γ} → Γ ∋ A
                      → Δ ⨾ Γ ⊢ A usable

      app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B usable → Δ ⨾ Γ ⊢ A verifiable
                        → Δ ⨾ Γ ⊢ B usable

      mvar : ∀ {A Δ Γ} → Δ ∋ A
                       → Δ ⨾ Γ ⊢ A usable


--------------------------------------------------------------------------------


mutual
  forgetₗ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A verifiable
                      → Δ ⨾ Γ ⊢ A true
  forgetₗ (lam 𝒟)      = lam (forgetₗ 𝒟)
  forgetₗ (box 𝒟)      = box 𝒟
  forgetₗ (letbox 𝒟 ℰ) = letbox (forgetᵣ 𝒟) (forgetₗ ℰ)
  forgetₗ (use 𝒟)      = forgetᵣ 𝒟

  forgetᵣ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A usable
                      → Δ ⨾ Γ ⊢ A true
  forgetᵣ (var i)   = var i
  forgetᵣ (app 𝒟 ℰ) = app (forgetᵣ 𝒟) (forgetₗ ℰ)
  forgetᵣ (mvar i)  = mvar i


--------------------------------------------------------------------------------


mutual
  renₗ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ A verifiable
                      → Δ ⨾ Γ′ ⊢ A verifiable
  renₗ η (lam 𝒟)      = lam (renₗ (keep η) 𝒟)
  renₗ η (box 𝒟)      = box 𝒟
  renₗ η (letbox 𝒟 ℰ) = letbox (renᵣ η 𝒟) (renₗ η ℰ)
  renₗ η (use 𝒟)      = use (renᵣ η 𝒟)

  renᵣ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ A usable
                      → Δ ⨾ Γ′ ⊢ A usable
  renᵣ η (var i)   = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₗ η ℰ)
  renᵣ η (mvar i)  = mvar i


wkᵣ : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ A usable
                  → Δ ⨾ Γ , B ⊢ A usable
wkᵣ 𝒟 = renᵣ (drop id⊇) 𝒟


vzᵣ : ∀ {A Δ Γ} → Δ ⨾ Γ , A ⊢ A usable
vzᵣ = var zero


--------------------------------------------------------------------------------


mutual
  mrenₗ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ A verifiable
                       → Δ′ ⨾ Γ ⊢ A verifiable
  mrenₗ η (lam 𝒟)      = lam (mrenₗ η 𝒟)
  mrenₗ η (box 𝒟)      = box (mren η 𝒟)
  mrenₗ η (letbox 𝒟 ℰ) = letbox (mrenᵣ η 𝒟) (mrenₗ (keep η) ℰ)
  mrenₗ η (use 𝒟)      = use (mrenᵣ η 𝒟)

  mrenᵣ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ A usable
                       → Δ′ ⨾ Γ ⊢ A usable
  mrenᵣ η (var i)   = var i
  mrenᵣ η (app 𝒟 ℰ) = app (mrenᵣ η 𝒟) (mrenₗ η ℰ)
  mrenᵣ η (mvar i)  = mvar (ren∋ η i)


mwkᵣ : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ A usable
                   → Δ , B ⨾ Γ ⊢ A usable
mwkᵣ 𝒟 = mrenᵣ (drop id⊇) 𝒟


mvzᵣ : ∀ {A Δ Γ} → Δ , A ⨾ Γ ⊢ A usable
mvzᵣ = mvar zero


--------------------------------------------------------------------------------
