module ExperimentalS4Derivations3a where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions
import ExperimentalS4Derivations3 as S4


--------------------------------------------------------------------------------


infix 3 _⊢_
data _⊢_ : List Validity → ContextualValidity → Set
  where
    vz : ∀ {A Δ Γ} → Δ ⊢ A valid[ Γ , A true ]

    wk : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ]
                     → Δ ⊢ A valid[ Γ , B true ]

    cut : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ] → Δ ⊢ B valid[ Γ , A true ]
                      → Δ ⊢ B valid[ Γ ]

    lam : ∀ {A B Δ Γ} → Δ ⊢ B valid[ Γ , A true ]
                      → Δ ⊢ A ⊃ B valid[ Γ ]

    unlam : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B valid[ Γ ]
                        → Δ ⊢ B valid[ Γ , A true ]

    mvz : ∀ {A Δ Γ} → Δ , A valid ⊢ A valid[ Γ ]

    mwk : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ]
                      → Δ , B valid ⊢ A valid[ Γ ]

    mcut : ∀ {A B Δ Γ} → Δ ⊢ A valid[ ∙ ] → Δ , A valid ⊢ B valid[ Γ ]
                       → Δ ⊢ B valid[ Γ ]

    vau : ∀ {A B Δ Γ} → Δ , A valid ⊢ B valid[ Γ ]
                      → Δ ⊢ B valid[ Γ , □ A true ]

    unvau : ∀ {A B Δ Γ} → Δ ⊢ B valid[ Γ , □ A true ]
                        → Δ , A valid ⊢ B valid[ Γ ]


--------------------------------------------------------------------------------


↓ : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
              → Δ S4.⨾ Γ ⊢ A true
↓ vz         = S4.vz
↓ (wk 𝒟)     = S4.wk (↓ 𝒟)
↓ (cut 𝒟 ℰ)  = S4.cut (↓ 𝒟) (↓ ℰ)
↓ (lam 𝒟)    = S4.lam (↓ 𝒟)
↓ (unlam 𝒟)  = S4.unlam (↓ 𝒟)
↓ mvz        = S4.mvz
↓ (mwk 𝒟)    = S4.mwk (↓ 𝒟)
↓ (mcut 𝒟 ℰ) = S4.mcut (↓ 𝒟) (↓ ℰ)
↓ (vau 𝒟)    = S4.vau (↓ 𝒟)
↓ (unvau 𝒟)  = S4.unvau (↓ 𝒟)


↑ : ∀ {Δ Γ A} → Δ S4.⨾ Γ ⊢ A true
              → Δ ⊢ A valid[ Γ ]
↑ S4.vz         = vz
↑ (S4.wk 𝒟)     = wk (↑ 𝒟)
↑ (S4.cut 𝒟 ℰ)  = cut (↑ 𝒟) (↑ ℰ)
↑ (S4.lam 𝒟)    = lam (↑ 𝒟)
↑ (S4.unlam 𝒟)  = unlam (↑ 𝒟)
↑ S4.mvz        = mvz
↑ (S4.mwk 𝒟)    = mwk (↑ 𝒟)
↑ (S4.mcut 𝒟 ℰ) = mcut (↑ 𝒟) (↑ ℰ)
↑ (S4.vau 𝒟)    = vau (↑ 𝒟)
↑ (S4.unvau 𝒟)  = unvau (↑ 𝒟)


--------------------------------------------------------------------------------
