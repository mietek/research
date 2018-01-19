module S4ExperimentalDerivations1a where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions
import S4ExperimentalDerivations1 as S4


--------------------------------------------------------------------------------


infix 3 _⊢_
data _⊢_ : List Validity → ContextualValidity → Set
  where
    vz : ∀ {A Δ Γ} → Δ ⊢ A valid[ Γ , A true ]

    wk : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ]
                     → Δ ⊢ A valid[ Γ , B true ]

    lam : ∀ {A B Δ Γ} → Δ ⊢ B valid[ Γ , A true ]
                      → Δ ⊢ A ⊃ B valid[ Γ ]

    app : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B valid[ Γ ] → Δ ⊢ A valid[ Γ ]
                      → Δ ⊢ B valid[ Γ ]

    mvz : ∀ {A Δ Γ} → Δ , A valid ⊢ A valid[ Γ ]

    mwk : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ]
                      → Δ , B valid ⊢ A valid[ Γ ]

    box : ∀ {A Δ Γ} → Δ ⊢ A valid[ ∙ ]
                    → Δ ⊢ □ A valid[ Γ ]

    letbox : ∀ {A B Δ Γ} → Δ ⊢ □ A valid[ Γ ] → Δ , A valid ⊢ B valid[ Γ ]
                         → Δ ⊢ B valid[ Γ ]


--------------------------------------------------------------------------------


↓ : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
              → Δ S4.⨾ Γ ⊢ A true
↓ vz           = S4.vz
↓ (wk 𝒟)       = S4.wk (↓ 𝒟)
↓ (lam 𝒟)      = S4.lam (↓ 𝒟)
↓ (app 𝒟 ℰ)    = S4.app (↓ 𝒟) (↓ ℰ)
↓ mvz          = S4.mvz
↓ (mwk 𝒟)      = S4.mwk (↓ 𝒟)
↓ (box 𝒟)      = S4.box (↓ 𝒟)
↓ (letbox 𝒟 ℰ) = S4.letbox (↓ 𝒟) (↓ ℰ)


↑ : ∀ {Δ Γ A} → Δ S4.⨾ Γ ⊢ A true
              → Δ ⊢ A valid[ Γ ]
↑ S4.vz           = vz
↑ (S4.wk 𝒟)       = wk (↑ 𝒟)
↑ (S4.lam 𝒟)      = lam (↑ 𝒟)
↑ (S4.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
↑ S4.mvz          = mvz
↑ (S4.mwk 𝒟)      = mwk (↑ 𝒟)
↑ (S4.box 𝒟)      = box (↑ 𝒟)
↑ (S4.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)


--------------------------------------------------------------------------------
