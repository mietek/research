module ExperimentalS4Derivations0a where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions
import SimpleS4Derivations as S4


--------------------------------------------------------------------------------


infix 3 _⊢_
data _⊢_ : List Validity → ContextualValidity → Set
  where
    var : ∀ {A Δ Γ} → Γ ∋ A true
                    → Δ ⊢ A valid[ Γ ]

    lam : ∀ {A B Δ Γ} → Δ ⊢ B valid[ Γ , A true ]
                      → Δ ⊢ A ⊃ B valid[ Γ ]

    app : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B valid[ Γ ] → Δ ⊢ A valid[ Γ ]
                      → Δ ⊢ B valid[ Γ ]

    mvar : ∀ {A Δ Γ} → Δ ∋ A valid
                     → Δ ⊢ A valid[ Γ ]

    box : ∀ {A Δ Γ} → Δ ⊢ A valid[ ∙ ]
                    → Δ ⊢ □ A valid[ Γ ]

    letbox : ∀ {A B Δ Γ} → Δ ⊢ □ A valid[ Γ ] → Δ , A valid ⊢ B valid[ Γ ]
                         → Δ ⊢ B valid[ Γ ]


--------------------------------------------------------------------------------


↓ : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
              → Δ S4.⨾ Γ ⊢ A true
↓ (var i)      = S4.var i
↓ (lam 𝒟)      = S4.lam (↓ 𝒟)
↓ (app 𝒟 ℰ)    = S4.app (↓ 𝒟) (↓ ℰ)
↓ (mvar i)     = S4.mvar i
↓ (box 𝒟)      = S4.box (↓ 𝒟)
↓ (letbox 𝒟 ℰ) = S4.letbox (↓ 𝒟) (↓ ℰ)


↑ : ∀ {Δ Γ A} → Δ S4.⨾ Γ ⊢ A true
              → Δ ⊢ A valid[ Γ ]
↑ (S4.var i)      = var i
↑ (S4.lam 𝒟)      = lam (↑ 𝒟)
↑ (S4.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
↑ (S4.mvar i)     = mvar i
↑ (S4.box 𝒟)      = box (↑ 𝒟)
↑ (S4.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)


--------------------------------------------------------------------------------
