{-# OPTIONS --rewriting #-}

module S4AndCMLScratch where

open import Prelude
open import Category
open import List
open import ListLemmas
open import ListConcatenation
open import AllList
open import S4Propositions
open import S4StandardDerivations
import CMLPropositions as CML
import CMLStandardDerivations as CML


--------------------------------------------------------------------------------


[_]_ : List Form → Form → Form
[ Γ ] A = □ (Γ ⊃⋯⊃ A)


⟪_⊫_⟫ : List Form → Form → Assert
⟪ Γ ⊫ A ⟫ = ⟪⊫ Γ ⊃⋯⊃ A ⟫


-- TODO: unfinished
-- mvar₊ : ∀ {A Ψ Δ Γ} → Δ ∋ ⟪ Ψ ⊫ A ⟫ → Δ ⊢ Ψ allvalid[ Γ ]
--                     → Δ ⊢ A valid[ Γ ]
-- mvar₊ i ψ = {!apps (mvar i) ψ!}
--
--
-- box₊ : ∀ {A Ψ Δ Γ} → Δ ⊢ A valid[ Ψ ]
--                    → Δ ⊢ [ Ψ ] A valid[ Γ ]
-- box₊ {Ψ = Ψ} 𝒟 = {!box (lams Ψ 𝒟)!}


blam : ∀ {Δ Γ Ψ A B} → Δ ⊢ [ Ψ , A ] B valid[ Γ ]
                     → Δ ⊢ [ Ψ ] (A ⊃ B) valid[ Γ ]
blam 𝒟 = 𝒟


unblam : ∀ {Δ Γ Ψ A B} → Δ ⊢ [ Ψ ] (A ⊃ B) valid[ Γ ]
                       → Δ ⊢ [ Ψ , A ] B valid[ Γ ]
unblam 𝒟 = 𝒟
