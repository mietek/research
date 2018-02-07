module CMLStandardDerivations-Traditional where

open import Prelude
open import Category
open import List
open import ListLemmas
open import ListConcatenation
open import AllList
open import CMLPropositions
import CMLStandardDerivations as CML


--------------------------------------------------------------------------------


mutual
  infix 3 _⨾_⊢_true
  data _⨾_⊢_true : List Assert → List Prop → Prop → Set
    where
      var : ∀ {A Δ Γ} → Γ ∋ A
                      → Δ ⨾ Γ ⊢ A true

      lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A ⊢ B true
                        → Δ ⨾ Γ ⊢ A ⊃ B true

      app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true → Δ ⨾ Γ ⊢ A true
                        → Δ ⨾ Γ ⊢ B true

      mvar : ∀ {A Ψ Δ Γ} → Δ ∋ ⟪ Ψ ⊫ A ⟫ → Δ ⨾ Γ ⊢ Ψ alltrue
                         → Δ ⨾ Γ ⊢ A true

      box : ∀ {A Ψ Δ Γ} → Δ ⨾ Ψ ⊢ A true
                        → Δ ⨾ Γ ⊢ [ Ψ ] A true

      letbox : ∀ {A B Ψ Δ Γ} → Δ ⨾ Γ ⊢ [ Ψ ] A true → Δ , ⟪ Ψ ⊫ A ⟫ ⨾ Γ ⊢ B true
                             → Δ ⨾ Γ ⊢ B true

  infix 3 _⨾_⊢_alltrue
  _⨾_⊢_alltrue : List Assert → List Prop → List Prop → Set
  Δ ⨾ Γ ⊢ Ξ alltrue = All (\ A → Δ ⨾ Γ ⊢ A true) Ξ


--------------------------------------------------------------------------------


mutual
  ↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
                → Δ CML.⊢ A valid[ Γ ]
  ↓ (var i)      = CML.var i
  ↓ (lam 𝒟)      = CML.lam (↓ 𝒟)
  ↓ (app 𝒟 ℰ)    = CML.app (↓ 𝒟) (↓ ℰ)
  ↓ (mvar i ψ)   = CML.mvar i (↓ⁿ ψ)
  ↓ (box 𝒟)      = CML.box (↓ 𝒟)
  ↓ (letbox 𝒟 ℰ) = CML.letbox (↓ 𝒟) (↓ ℰ)

  ↓ⁿ : ∀ {Δ Γ Ξ} → Δ ⨾ Γ ⊢ Ξ alltrue
                 → Δ CML.⊢ Ξ allvalid[ Γ ]
  ↓ⁿ ∙       = ∙
  ↓ⁿ (ξ , 𝒟) = ↓ⁿ ξ , ↓ 𝒟


mutual
  ↑ : ∀ {Δ Γ A} → Δ CML.⊢ A valid[ Γ ]
                → Δ ⨾ Γ ⊢ A true
  ↑ (CML.var i)      = var i
  ↑ (CML.lam 𝒟)      = lam (↑ 𝒟)
  ↑ (CML.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
  ↑ (CML.mvar i ψ)   = mvar i (↑ⁿ ψ)
  ↑ (CML.box 𝒟)      = box (↑ 𝒟)
  ↑ (CML.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)

  ↑ⁿ : ∀ {Δ Γ Ξ} → Δ CML.⊢ Ξ allvalid[ Γ ]
                 → Δ ⨾ Γ ⊢ Ξ alltrue
  ↑ⁿ ∙       = ∙
  ↑ⁿ (ξ , 𝒟) = ↑ⁿ ξ , ↑ 𝒟


mutual
  id↓↑ : ∀ {Δ Γ A} → (𝒟 : Δ CML.⊢ A valid[ Γ ])
                   → (↓ ∘ ↑) 𝒟 ≡ 𝒟
  id↓↑ (CML.var i)      = refl
  id↓↑ (CML.lam 𝒟)      = CML.lam & id↓↑ 𝒟
  id↓↑ (CML.app 𝒟 ℰ)    = CML.app & id↓↑ 𝒟 ⊗ id↓↑ ℰ
  id↓↑ (CML.mvar i ψ)   = CML.mvar i & id↓ⁿ↑ⁿ ψ
  id↓↑ (CML.box 𝒟)      = CML.box & id↓↑ 𝒟
  id↓↑ (CML.letbox 𝒟 ℰ) = CML.letbox & id↓↑ 𝒟 ⊗ id↓↑ ℰ

  id↓ⁿ↑ⁿ : ∀ {Δ Γ Ξ} → (ξ : Δ CML.⊢ Ξ allvalid[ Γ ])
                     → (↓ⁿ ∘ ↑ⁿ) ξ ≡ ξ
  id↓ⁿ↑ⁿ ∙       = refl
  id↓ⁿ↑ⁿ (ξ , 𝒟) = _,_ & id↓ⁿ↑ⁿ ξ ⊗ id↓↑ 𝒟


mutual
  id↑↓ : ∀ {Δ Γ A} → (𝒟 : Δ ⨾ Γ ⊢ A true)
                   → (↑ ∘ ↓) 𝒟 ≡ 𝒟
  id↑↓ (var i)      = refl
  id↑↓ (lam 𝒟)      = lam & id↑↓ 𝒟
  id↑↓ (app 𝒟 ℰ)    = app & id↑↓ 𝒟 ⊗ id↑↓ ℰ
  id↑↓ (mvar i ψ)   = mvar i & id↑ⁿ↓ⁿ ψ
  id↑↓ (box 𝒟)      = box & id↑↓ 𝒟
  id↑↓ (letbox 𝒟 ℰ) = letbox & id↑↓ 𝒟 ⊗ id↑↓ ℰ

  id↑ⁿ↓ⁿ : ∀ {Δ Γ Ξ} → (ξ : Δ ⨾ Γ ⊢ Ξ alltrue)
                     → (↑ⁿ ∘ ↓ⁿ) ξ ≡ ξ
  id↑ⁿ↓ⁿ ∙       = refl
  id↑ⁿ↓ⁿ (ξ , 𝒟) = _,_ & id↑ⁿ↓ⁿ ξ ⊗ id↑↓ 𝒟


--------------------------------------------------------------------------------
