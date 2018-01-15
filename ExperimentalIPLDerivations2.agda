module ExperimentalIPLDerivations2 where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import IPLPropositions
import SimpleIPLDerivations as IPL


--------------------------------------------------------------------------------


infix 3 _⊢_
data _⊢_ : List Truth → Truth → Set
  where
    vz : ∀ {A Γ} → Γ , A true ⊢ A true

    wk : ∀ {A B Γ} → Γ ⊢ A true
                   → Γ , B true ⊢ A true

    cut : ∀ {A B Γ} → Γ ⊢ A true → Γ , A true ⊢ B true
                    → Γ ⊢ B true

    lam : ∀ {A B Γ} → Γ , A true ⊢ B true
                    → Γ ⊢ A ⊃ B true

    unlam : ∀ {A B Γ} → Γ ⊢ A ⊃ B true
                      → Γ , A true ⊢ B true


--------------------------------------------------------------------------------


ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A true
                 → Γ′ ⊢ A true
ren (drop η) vz        = wk (ren η vz)
ren (keep η) vz        = vz
ren (drop η) (wk 𝒟)    = wk (ren η (wk 𝒟))
ren (keep η) (wk 𝒟)    = wk (ren η 𝒟)
ren η        (cut 𝒟 ℰ) = cut (ren η 𝒟) (ren (keep η) ℰ)
ren η        (lam 𝒟)   = lam (ren (keep η) 𝒟)
ren (drop η) (unlam 𝒟) = wk (ren η (unlam 𝒟))
ren (keep η) (unlam 𝒟) = unlam (ren η 𝒟)


--------------------------------------------------------------------------------


var : ∀ {Γ A} → Γ ∋ A true
              → Γ ⊢ A true
var zero    = vz
var (suc i) = wk (var i)


app : ∀ {A B Γ} → Γ ⊢ A ⊃ B true → Γ ⊢ A true
                → Γ ⊢ B true
app 𝒟 ℰ = cut ℰ (unlam 𝒟)


--------------------------------------------------------------------------------


↓ : ∀ {Γ A} → Γ ⊢ A true
            → Γ IPL.⊢ A true
↓ vz        = IPL.vz
↓ (wk 𝒟)    = IPL.wk (↓ 𝒟)
↓ (cut 𝒟 ℰ) = IPL.cut (↓ 𝒟) (↓ ℰ)
↓ (lam 𝒟)   = IPL.lam (↓ 𝒟)
↓ (unlam 𝒟) = IPL.unlam (↓ 𝒟)


↑ : ∀ {Γ A} → Γ IPL.⊢ A true
            → Γ ⊢ A true
↑ (IPL.var i)   = var i
↑ (IPL.lam 𝒟)   = lam (↑ 𝒟)
↑ (IPL.app 𝒟 ℰ) = app (↑ 𝒟) (↑ ℰ)


--------------------------------------------------------------------------------
