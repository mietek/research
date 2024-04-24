{-# OPTIONS --rewriting #-}

module A201801.S4AndCMLScratch where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.ListConcatenation
open import A201801.AllList
open import A201801.S4Propositions
-- open import S4Derivations
import A201801.CMLPropositions as CML
-- import CMLDerivations as CML


--------------------------------------------------------------------------------


[_]_ : List Form → Form → Form
[ Γ ] A = □ (Γ ⊃⋯⊃ A)


⟪_⊫_⟫ : List Form → Form → Assert
⟪ Γ ⊫ A ⟫ = ⟪⊫ Γ ⊃⋯⊃ A ⟫


-- mvar₊ : ∀ {A Ψ Δ Γ} → Δ ∋ ⟪ Ψ ⊫ A ⟫ → Δ ⊢ Ψ allvalid[ Γ ]
--                     → Δ ⊢ A valid[ Γ ]
-- mvar₊ i ψ = apps (mvar i) ψ


-- box₊ : ∀ {A Ψ Δ Γ} → Δ ⊢ A valid[ Ψ ]
--                    → Δ ⊢ [ Ψ ] A valid[ Γ ]
-- box₊ {Ψ = Ψ} 𝒟 = box (lams Ψ 𝒟)


-- blam : ∀ {Δ Γ Ψ A B} → Δ ⊢ [ Ψ , A ] B valid[ Γ ]
--                      → Δ ⊢ [ Ψ ] (A ⊃ B) valid[ Γ ]
-- blam 𝒟 = 𝒟


-- unblam : ∀ {Δ Γ Ψ A B} → Δ ⊢ [ Ψ ] (A ⊃ B) valid[ Γ ]
--                        → Δ ⊢ [ Ψ , A ] B valid[ Γ ]
-- unblam 𝒟 = 𝒟
