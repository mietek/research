module ExperimentalIPLDerivations3 where

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
    var : ∀ {A Γ} → Γ ∋ A true
                  → Γ ⊢ A true

    cut : ∀ {A B Γ} → Γ ⊢ A true → Γ , A true ⊢ B true
                    → Γ ⊢ B true

    lam : ∀ {A B Γ} → Γ , A true ⊢ B true
                    → Γ ⊢ A ⊃ B true

    unlam : ∀ {A B Γ} → Γ ⊢ A ⊃ B true
                      → Γ , A true ⊢ B true


infix 3 _⊢⋆_
_⊢⋆_ : List Truth → List Truth → Set
Γ ⊢⋆ Ξ = All (Γ ⊢_) Ξ


--------------------------------------------------------------------------------


ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A true
                 → Γ′ ⊢ A true
ren η (var i)   = var (ren∋ η i)
ren η (cut 𝒟 ℰ) = cut (ren η 𝒟) (ren (keep η) ℰ)
ren η (lam 𝒟)   = lam (ren (keep η) 𝒟)
ren η (unlam {A} {B} 𝒟) = {!!}


rens : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢⋆ Ξ
                  → Γ′ ⊢⋆ Ξ
rens η ξ = maps (ren η) ξ


--------------------------------------------------------------------------------
