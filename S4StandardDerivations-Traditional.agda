module S4StandardDerivations-Traditional where

open import Prelude
open import Category
open import List
open import ListLemmas
open import ListConcatenation
open import AllList
open import S4Propositions
import S4StandardDerivations as S4


--------------------------------------------------------------------------------


infix 3 _⨾_⊢_true
data _⨾_⊢_true : List Assert → List Form → Form → Set
  where
    var : ∀ {A Δ Γ} → Γ ∋ A
                    → Δ ⨾ Γ ⊢ A true

    lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A ⊢ B true
                      → Δ ⨾ Γ ⊢ A ⊃ B true

    app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true → Δ ⨾ Γ ⊢ A true
                      → Δ ⨾ Γ ⊢ B true

    mvar : ∀ {A Δ Γ} → Δ ∋ ⟪⊫ A ⟫
                     → Δ ⨾ Γ ⊢ A true

    box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                    → Δ ⨾ Γ ⊢ □ A true

    letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ □ A true → Δ , ⟪⊫ A ⟫ ⨾ Γ ⊢ B true
                         → Δ ⨾ Γ ⊢ B true


--------------------------------------------------------------------------------


↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
              → Δ S4.⊢ A valid[ Γ ]
↓ (var i)      = S4.var i
↓ (lam 𝒟)      = S4.lam (↓ 𝒟)
↓ (app 𝒟 ℰ)    = S4.app (↓ 𝒟) (↓ ℰ)
↓ (mvar i)     = S4.mvar i
↓ (box 𝒟)      = S4.box (↓ 𝒟)
↓ (letbox 𝒟 ℰ) = S4.letbox (↓ 𝒟) (↓ ℰ)


↑ : ∀ {Δ Γ A} → Δ S4.⊢ A valid[ Γ ]
              → Δ ⨾ Γ ⊢ A true
↑ (S4.var i)      = var i
↑ (S4.lam 𝒟)      = lam (↑ 𝒟)
↑ (S4.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
↑ (S4.mvar i)     = mvar i
↑ (S4.box 𝒟)      = box (↑ 𝒟)
↑ (S4.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)


id↓↑ : ∀ {Δ Γ A} → (𝒟 : Δ S4.⊢ A valid[ Γ ])
                 → (↓ ∘ ↑) 𝒟 ≡ 𝒟
id↓↑ (S4.var i)      = refl
id↓↑ (S4.lam 𝒟)      = S4.lam & id↓↑ 𝒟
id↓↑ (S4.app 𝒟 ℰ)    = S4.app & id↓↑ 𝒟 ⊗ id↓↑ ℰ
id↓↑ (S4.mvar i)     = refl
id↓↑ (S4.box 𝒟)      = S4.box & id↓↑ 𝒟
id↓↑ (S4.letbox 𝒟 ℰ) = S4.letbox & id↓↑ 𝒟 ⊗ id↓↑ ℰ


id↑↓ : ∀ {Δ Γ A} → (𝒟 : Δ ⨾ Γ ⊢ A true)
                 → (↑ ∘ ↓) 𝒟 ≡ 𝒟
id↑↓ (var i)      = refl
id↑↓ (lam 𝒟)      = lam & id↑↓ 𝒟
id↑↓ (app 𝒟 ℰ)    = app & id↑↓ 𝒟 ⊗ id↑↓ ℰ
id↑↓ (mvar i)     = refl
id↑↓ (box 𝒟)      = box & id↑↓ 𝒟
id↑↓ (letbox 𝒟 ℰ) = letbox & id↑↓ 𝒟 ⊗ id↑↓ ℰ


--------------------------------------------------------------------------------
