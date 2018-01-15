module ExperimentalS4Derivations5 where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions
import SimpleS4Derivations as S4


--------------------------------------------------------------------------------


infix 3 _⨾_⊢_
data _⨾_⊢_ : List Validity → List Truth → Truth → Set
  where
    vz : ∀ {A Δ Γ} → Δ ⨾ Γ , A true ⊢ A true

    wk : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true
                     → Δ ⨾ Γ , B true ⊢ A true

    cut : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true → Δ ⨾ Γ , A true ⊢ B true
                      → Δ ⨾ Γ ⊢ B true

    lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A true ⊢ B true
                      → Δ ⨾ Γ ⊢ A ⊃ B true

    unlam : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true
                        → Δ ⨾ Γ , A true ⊢ B true

    mvz : ∀ {A Δ Γ} → Δ , A valid ⨾ Γ ⊢ A true

    mwk : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true
                      → Δ , B valid ⨾ Γ ⊢ A true

    mcut : ∀ {A B Δ Γ} → Δ ⨾ ∙ ⊢ A true → Δ , A valid ⨾ Γ ⊢ B true
                       → Δ ⨾ Γ ⊢ B true

    box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                    → Δ ⨾ Γ ⊢ □ A true

    unbox : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ □ A true
                      → Δ ⨾ Γ ⊢ A true
                        

--------------------------------------------------------------------------------


var : ∀ {A Δ Γ} → Γ ∋ A true
                → Δ ⨾ Γ ⊢ A true
var zero    = vz
var (suc i) = wk (var i)


app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true → Δ ⨾ Γ ⊢ A true
                  → Δ ⨾ Γ ⊢ B true
app 𝒟 ℰ = cut ℰ (unlam 𝒟)


--------------------------------------------------------------------------------


mvar : ∀ {A Δ Γ} → Δ ∋ A valid
                 → Δ ⨾ Γ ⊢ A true
mvar zero    = mvz
mvar (suc i) = mwk (mvar i)


vau : ∀ {Δ Γ A B} → Δ , A valid ⨾ Γ ⊢ B true
                  → Δ ⨾ Γ , □ A true ⊢ B true
vau 𝒟 = {!mcut ? (wk 𝒟)!}


letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ □ A true → Δ , A valid ⨾ Γ ⊢ B true
                     → Δ ⨾ Γ ⊢ B true
letbox 𝒟 ℰ = cut 𝒟 (vau ℰ)


--------------------------------------------------------------------------------


↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
              → Δ S4.⨾ Γ ⊢ A true
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


↑ : ∀ {Δ Γ A} → Δ S4.⨾ Γ ⊢ A true
              → Δ ⨾ Γ ⊢ A true
↑ (S4.var i)      = var i
↑ (S4.lam 𝒟)      = lam (↑ 𝒟)
↑ (S4.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
↑ (S4.mvar i)     = mvar i
↑ (S4.box 𝒟)      = box (↑ 𝒟)
↑ (S4.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)


--------------------------------------------------------------------------------
