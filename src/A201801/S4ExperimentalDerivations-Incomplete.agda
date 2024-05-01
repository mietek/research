module A201801.S4ExperimentalDerivations-Incomplete where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.S4Propositions
import A201801.S4StandardDerivations as S4


--------------------------------------------------------------------------------


infix 3 _⊢_valid[_]
data _⊢_valid[_] : List Assert → Form → List Form → Set
  where
    vz : ∀ {A Δ Γ} → Δ ⊢ A valid[ Γ , A ]

    wk : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ]
                     → Δ ⊢ A valid[ Γ , B ]

    cut : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ] → Δ ⊢ B valid[ Γ , A ]
                      → Δ ⊢ B valid[ Γ ]

    lam : ∀ {A B Δ Γ} → Δ ⊢ B valid[ Γ , A ]
                      → Δ ⊢ A ⊃ B valid[ Γ ]

    unlam : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B valid[ Γ ]
                        → Δ ⊢ B valid[ Γ , A ]

    mvz : ∀ {A Δ Γ} → Δ , ⟪⊫ A ⟫ ⊢ A valid[ Γ ]

    mwk : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ]
                      → Δ , ⟪⊫ B ⟫ ⊢ A valid[ Γ ]

    mcut : ∀ {Δ Γ A B} → Δ ⊢ A valid[ ∙ ] → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]
                       → Δ ⊢ B valid[ Γ ]

    box : ∀ {A Δ Γ} → Δ ⊢ A valid[ ∙ ]
                    → Δ ⊢ □ A valid[ Γ ]

    unbox : ∀ {A Δ Γ} → Δ ⊢ □ A valid[ Γ ]
                      → Δ ⊢ A valid[ Γ ]


--------------------------------------------------------------------------------


var : ∀ {Δ Γ A} → Γ ∋ A
                → Δ ⊢ A valid[ Γ ]
var zero    = vz
var (suc i) = wk (var i)


app : ∀ {Δ Γ A B} → Δ ⊢ A ⊃ B valid[ Γ ] → Δ ⊢ A valid[ Γ ]
                  → Δ ⊢ B valid[ Γ ]
app 𝒟 ℰ = cut ℰ (unlam 𝒟)


mvar : ∀ {Δ Γ A} → Δ ∋ ⟪⊫ A ⟫
                 → Δ ⊢ A valid[ Γ ]
mvar zero    = mvz
mvar (suc i) = mwk (mvar i)


-- NOTE: Problematic

-- letbox : ∀ {Δ Γ A B} → Δ ⊢ □ A valid[ Γ ] → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]
--                      → Δ ⊢ B valid[ Γ ]
-- letbox 𝒟 ℰ = {!!}


-- NOTE: Local completeness of □; problematic

-- rebox : ∀ {Δ Γ A} → Δ ⊢ □ A valid[ Γ ]
--                   → Δ ⊢ □ A valid[ Γ ]
-- rebox 𝒟 = letbox 𝒟 (box mvz)


-- NOTE: Local soundness of □; problematic

-- pseudomcut : ∀ {Δ Γ A B} → Δ ⊢ A valid[ ∙ ] → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]
--                          → Δ ⊢ B valid[ Γ ]
-- pseudomcut 𝒟 ℰ = letbox (box 𝒟) ℰ


--------------------------------------------------------------------------------


↓ : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
              → Δ S4.⊢ A valid[ Γ ]
↓ vz         = S4.vz
↓ (wk 𝒟)     = S4.wk (↓ 𝒟)
↓ (cut 𝒟 ℰ)  = S4.cut (↓ 𝒟) (↓ ℰ)
↓ (lam 𝒟)    = S4.lam (↓ 𝒟)
↓ (unlam 𝒟)  = S4.unlam (↓ 𝒟)
↓ mvz        = S4.mvz
↓ (mwk 𝒟)    = S4.mwk (↓ 𝒟)
↓ (mcut 𝒟 ℰ) = S4.mcut (↓ 𝒟) (↓ ℰ)
↓ (box 𝒟)    = S4.box (↓ 𝒟)
↓ (unbox 𝒟)  = S4.unbox (↓ 𝒟)


-- NOTE: Problematic

-- ↑ : ∀ {Δ Γ A} → Δ S4.⊢ A valid[ Γ ]
--               → Δ ⊢ A valid[ Γ ]
-- ↑ (S4.var i)      = var i
-- ↑ (S4.lam 𝒟)      = lam (↑ 𝒟)
-- ↑ (S4.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
-- ↑ (S4.mvar i)     = mvar i
-- ↑ (S4.box 𝒟)      = box (↑ 𝒟)
-- ↑ (S4.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)


--------------------------------------------------------------------------------
