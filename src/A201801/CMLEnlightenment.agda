{-# OPTIONS --rewriting #-}

module A201801.CMLEnlightenment where


open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.ListConcatenation
open import A201801.AllList
open import A201801.CMLPropositions
import A201801.CMLStandardDerivations as CML


--------------------------------------------------------------------------------


infix 3 _⊢_valid[_]
data _⊢_valid[_] : List Assert → Form → List Form → Set
  where
    vz : ∀ {A Δ Γ} → Δ ⊢ A valid[ Γ , A ]

    wk : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ]
                     → Δ ⊢ A valid[ Γ , B ]

    lam : ∀ {A B Δ Γ} → Δ ⊢ B valid[ Γ , A ]
                      → Δ ⊢ A ⊃ B valid[ Γ ]

    app : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B valid[ Γ ] → Δ ⊢ A valid[ Γ ]
                      → Δ ⊢ B valid[ Γ ]

    mvz! : ∀ {A Ψ Δ} →  Δ , ⟪ Ψ ⊫ A ⟫ ⊢ A valid[ Ψ ]

    mwk : ∀ {B Ψ A Δ Γ} → Δ ⊢ A valid[ Γ ]
                        → Δ , ⟪ Ψ ⊫ B ⟫ ⊢ A valid[ Γ ]

    box : ∀ {A Ψ Δ Γ} → Δ ⊢ A valid[ Ψ ]
                      → Δ ⊢ [ Ψ ] A valid[ Γ ]

    letbox : ∀ {A B Ψ Δ Γ} → Δ ⊢ [ Ψ ] A valid[ Γ ] → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ B valid[ Γ ]
                           → Δ ⊢ B valid[ Γ ]


infix 3 _⊢_allvalid[_]
_⊢_allvalid[_] : List Assert → List Form → List Form → Set
Δ ⊢ Ξ allvalid[ Γ ] = All (\ A → Δ ⊢ A valid[ Γ ]) Ξ


infix 3 _⊢_allvalid*
_⊢_allvalid* : List Assert → List Assert → Set
Δ ⊢ Ξ allvalid* = All (\ { ⟪ Γ ⊫ A ⟫ → Δ ⊢ A valid[ Γ ] }) Ξ


--------------------------------------------------------------------------------


wks : ∀ {A Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                  → Δ ⊢ Ξ allvalid[ Γ , A ]
wks ξ = maps wk ξ


lifts : ∀ {A Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                    → Δ ⊢ Ξ , A allvalid[ Γ , A ]
lifts ξ = wks ξ , vz


vars : ∀ {Δ Γ Γ′} → Γ′ ⊇ Γ
                  → Δ ⊢ Γ allvalid[ Γ′ ]
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {Δ Γ} → Δ ⊢ Γ allvalid[ Γ ]
ids = vars id


--------------------------------------------------------------------------------


mwks : ∀ {A Ψ Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                     → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ Ξ allvalid[ Γ ]
mwks ξ = maps mwk ξ


--------------------------------------------------------------------------------


lams : ∀ {Δ Γ A} → (Ξ : List Form) → Δ ⊢ A valid[ Γ ⧺ Ξ ]
                 → Δ ⊢ Ξ ⊃⋯⊃ A valid[ Γ ]
lams ∙       𝒟 = 𝒟
lams (Ξ , B) 𝒟 = lams Ξ (lam 𝒟)


unlam : ∀ {Δ Γ A B} → Δ ⊢ A ⊃ B valid[ Γ ]
                    → Δ ⊢ B valid[ Γ , A ]
unlam 𝒟 = app (wk 𝒟) vz


unlams : ∀ {Δ Γ A} → (Ξ : List Form) → Δ ⊢ Ξ ⊃⋯⊃ A valid[ Γ ]
                   → Δ ⊢ A valid[ Γ ⧺ Ξ ]
unlams ∙       𝒟 = 𝒟
unlams (Ξ , B) 𝒟 = unlam (unlams Ξ 𝒟)


apps : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ ⊃⋯⊃ A valid[ Γ ] → Δ ⊢ Ξ allvalid[ Γ ]
                   → Δ ⊢ A valid[ Γ ]
apps 𝒟 ∙       = 𝒟
apps 𝒟 (ξ , ℰ) = app (apps 𝒟 ξ) ℰ


blam : ∀ {Δ Γ Ψ A B} → Δ ⊢ [ Ψ , A ] B valid[ Γ ]
                     → Δ ⊢ [ Ψ ] (A ⊃ B) valid[ Γ ]
blam 𝒟 = letbox 𝒟 (box (lam mvz!))


unblam : ∀ {Δ Γ Ψ A B} → Δ ⊢ [ Ψ ] (A ⊃ B) valid[ Γ ]
                       → Δ ⊢ [ Ψ , A ] B valid[ Γ ]
unblam 𝒟 = letbox 𝒟 (box (unlam mvz!))


blams : ∀ {Δ Γ Ψ A} → (Ξ : List Form) → Δ ⊢ [ Ψ ⧺ Ξ ] A valid[ Γ ]
                    → Δ ⊢ [ Ψ ] (Ξ ⊃⋯⊃ A) valid[ Γ ]
blams ∙       𝒟 = 𝒟
blams (Ξ , B) 𝒟 = blams Ξ (blam 𝒟)


unblams : ∀ {Δ Γ Ψ A} → (Ξ : List Form) → Δ ⊢ [ Ψ ] (Ξ ⊃⋯⊃ A) valid[ Γ ]
                      → Δ ⊢ [ Ψ ⧺ Ξ ] A valid[ Γ ]
unblams ∙       𝒟 = 𝒟
unblams (Ξ , B) 𝒟 = unblam (unblams Ξ 𝒟)


--------------------------------------------------------------------------------


var : ∀ {Δ Γ A} → Γ ∋ A
                → Δ ⊢ A valid[ Γ ]
var zero    = vz
var (suc i) = wk (var i)


vau : ∀ {Δ Γ Ψ A B} → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ B valid[ Γ ]
                    → Δ ⊢ B valid[ Γ , [ Ψ ] A ]
vau 𝒟 = letbox vz (wk 𝒟)


unvau : ∀ {Δ Γ Ψ A B} → Δ ⊢ B valid[ Γ , [ Ψ ] A ]
                      → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ B valid[ Γ ]
unvau 𝒟 = app (lam (mwk 𝒟)) (box mvz!)


vaus : ∀ {Δ Γ Ψ Ξ A} → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ Ξ allvalid[ Γ ]
                     → Δ ⊢ Ξ allvalid[ Γ , [ Ψ ] A ]
vaus 𝒟 = maps vau 𝒟


mvar! : ∀ {Δ Ψ A} → Δ ∋ ⟪ Ψ ⊫ A ⟫
                  → Δ ⊢ A valid[ Ψ ]
mvar! zero    = mvz!
mvar! (suc i) = mwk (mvar! i)


-- TODO: unfinished
-- mvar : ∀ {A Ψ Δ Γ} → Δ ∋ ⟪ Ψ ⊫ A ⟫ → Δ ⊢ Ψ allvalid[ Γ ]
--                    → Δ ⊢ A valid[ Γ ]
-- mvar {Ψ = Ψ} i ψ = {!mvar! i!}


unbox : ∀ {Δ Ψ A} → Δ ⊢ [ Ψ ] A valid[ Ψ ]
                  → Δ ⊢ A valid[ Ψ ]
unbox 𝒟 = letbox 𝒟 mvz!


-- TODO: unfinished
-- sub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid[ Γ ] → Δ ⊢ A valid[ Ξ ]
--                   → Δ ⊢ A valid[ Γ ]
-- sub (ξ , 𝒞) vz           = 𝒞
-- sub (ξ , 𝒞) (wk 𝒟)       = sub ξ 𝒟
-- sub ξ       (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
-- sub ξ       (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
-- sub ξ       mvz!         = {!unbox (unvau vz)!}
-- sub ξ       (mwk 𝒟)      = unvau (sub (vaus ξ) 𝒟)
-- sub ξ       (box 𝒟)      = box 𝒟
-- sub ξ       (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)


--------------------------------------------------------------------------------


⟦_⟧ : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
                → Δ CML.⊢ A valid[ Γ ]
⟦ vz ⟧         = CML.vz
⟦ wk 𝒟 ⟧       = CML.wk ⟦ 𝒟 ⟧
⟦ lam 𝒟 ⟧      = CML.lam ⟦ 𝒟 ⟧
⟦ app 𝒟 ℰ ⟧    = CML.app ⟦ 𝒟 ⟧ ⟦ ℰ ⟧
-- ⟦ mvar i ⟧     = CML.mvar i CML.ids
⟦ mvz! ⟧       = CML.mvz CML.ids
⟦ mwk 𝒟 ⟧      = CML.mwk ⟦ 𝒟 ⟧
⟦ box 𝒟 ⟧      = CML.box ⟦ 𝒟 ⟧
⟦ letbox 𝒟 ℰ ⟧ = CML.letbox ⟦ 𝒟 ⟧ ⟦ ℰ ⟧


-- TODO: unfinished
-- mutual
--   ↓ : ∀ {Δ Γ A} → Δ CML.⊢ A valid[ Γ ]
--                 → Δ ⊢ A valid[ Γ ]
--   ↓ (CML.var i)      = var i
--   ↓ (CML.lam 𝒟)      = lam (↓ 𝒟)
--   ↓ (CML.app 𝒟 ℰ)    = app (↓ 𝒟) (↓ ℰ)
--   ↓ (CML.mvar i ψ)   = sub (↓ⁿ ψ) (mvar! i)
--   ↓ (CML.box 𝒟)      = box (↓ 𝒟)
--   ↓ (CML.letbox 𝒟 ℰ) = letbox (↓ 𝒟) (↓ ℰ)
--
--   ↓ⁿ : ∀ {Δ Γ Ξ} → Δ CML.⊢ Ξ allvalid[ Γ ]
--                  → Δ ⊢ Ξ allvalid[ Γ ]
--   ↓ⁿ ∙       = ∙
--   ↓ⁿ (ξ , 𝒟) = ↓ⁿ ξ , ↓ 𝒟


--------------------------------------------------------------------------------
