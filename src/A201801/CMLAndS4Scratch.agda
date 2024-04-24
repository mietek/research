{-# OPTIONS --rewriting #-}

module A201801.CMLAndS4Scratch where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.ListConcatenation
open import A201801.AllList
open import A201801.CMLPropositions
-- open import CMLDerivations
import A201801.S4Propositions as S4
-- import S4Derivations as S4


--------------------------------------------------------------------------------


-- lams : ∀ {Δ Γ A} → (Ξ : List Prop) → Δ ⊢ A valid[ Γ ⧺ Ξ ]
--                  → Δ ⊢ Ξ ⊃⋯⊃ A valid[ Γ ]
-- lams ∙       𝒟 = 𝒟
-- lams (Ξ , B) 𝒟 = lams Ξ (lam 𝒟)


-- unlams : ∀ {Δ Γ A} → (Ξ : List Prop) → Δ ⊢ Ξ ⊃⋯⊃ A valid[ Γ ]
--                    → Δ ⊢ A valid[ Γ ⧺ Ξ ]
-- unlams ∙       𝒟 = 𝒟
-- unlams (Ξ , B) 𝒟 = unlam (unlams Ξ 𝒟)


-- apps : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ ⊃⋯⊃ A valid[ Γ ] → Δ ⊢ Ξ allvalid[ Γ ]
--                    → Δ ⊢ A valid[ Γ ]
-- apps 𝒟 ∙       = 𝒟
-- apps 𝒟 (ξ , ℰ) = app (apps 𝒟 ξ) ℰ


-- blam : ∀ {Δ Γ Ψ A B} → Δ ⊢ [ Ψ , A ] B valid[ Γ ]
--                      → Δ ⊢ [ Ψ ] (A ⊃ B) valid[ Γ ]
-- blam 𝒟 = letbox 𝒟 (box (lam (mvz ids)))


-- unblam : ∀ {Δ Γ Ψ A B} → Δ ⊢ [ Ψ ] (A ⊃ B) valid[ Γ ]
--                        → Δ ⊢ [ Ψ , A ] B valid[ Γ ]
-- unblam 𝒟 = letbox 𝒟 (box (unlam (mvz ids)))


-- blams : ∀ {Δ Γ Ψ A} → (Ξ : List Prop) → Δ ⊢ [ Ψ ⧺ Ξ ] A valid[ Γ ]
--                     → Δ ⊢ [ Ψ ] (Ξ ⊃⋯⊃ A) valid[ Γ ]
-- blams ∙       𝒟 = 𝒟
-- blams (Ξ , B) 𝒟 = blams Ξ (blam 𝒟)


-- unblams : ∀ {Δ Γ Ψ A} → (Ξ : List Prop) → Δ ⊢ [ Ψ ] (Ξ ⊃⋯⊃ A) valid[ Γ ]
--                       → Δ ⊢ [ Ψ ⧺ Ξ ] A valid[ Γ ]
-- unblams ∙       𝒟 = 𝒟
-- unblams (Ξ , B) 𝒟 = unblam (unblams Ξ 𝒟)
