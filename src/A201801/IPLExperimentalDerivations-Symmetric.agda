{-# OPTIONS --rewriting #-}

module A201801.IPLExperimentalDerivations-Symmetric where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.IPLPropositions


--------------------------------------------------------------------------------


infix 3 _⊢_true
data _⊢_true : List Form → Form → Set
  where
    var : ∀ {A Γ} → Γ ∋ A
                  → Γ ⊢ A true

    cut : ∀ {A B Γ} → Γ ⊢ A true → Γ , A ⊢ B true
                    → Γ ⊢ B true

    lam : ∀ {A B Γ} → Γ , A ⊢ B true
                    → Γ ⊢ A ⊃ B true

    unlam : ∀ {A B Γ} → Γ ⊢ A ⊃ B true
                      → Γ , A ⊢ B true


--------------------------------------------------------------------------------


-- NOTE: Problematic

-- ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A true
--                  → Γ′ ⊢ A true
-- ren η (var i)   = var (ren∋ η i)
-- ren η (cut 𝒟 ℰ) = cut (ren η 𝒟) (ren (keep η) ℰ)
-- ren η (lam 𝒟)   = lam (ren (keep η) 𝒟)
-- ren η (unlam 𝒟) = {!!} -- Γ′ ⊢ B true


--------------------------------------------------------------------------------
