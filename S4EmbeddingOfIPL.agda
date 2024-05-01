module S4EmbeddingOfIPL where

open import Prelude
open import List
open import ListConcatenation
open import S4Propositions
open import S4StandardDerivations
import IPLPropositions as IPL
import IPLStandardDerivations as IPL


--------------------------------------------------------------------------------


↑ₚ : IPL.Form → Form
↑ₚ (IPL.ι P)   = ι P
↑ₚ (A IPL.⊃ B) = ↑ₚ A ⊃ ↑ₚ B


↑ₐ : IPL.Form → Assert
↑ₐ A = ⟪⊫ ↑ₚ A ⟫


↑ₚₛ : List IPL.Form → List Form
↑ₚₛ Γ = map ↑ₚ Γ


↑ₐₛ : List IPL.Form → List Assert
↑ₐₛ Γ = map ↑ₐ Γ


↑∋ₚ : ∀ {Γ A} → Γ ∋ A
              → ↑ₚₛ Γ ∋ ↑ₚ A
↑∋ₚ zero    = zero
↑∋ₚ (suc i) = suc (↑∋ₚ i)


↑∋ₐ : ∀ {Δ A} → Δ ∋ A
              → ↑ₐₛ Δ ∋ ↑ₐ A
↑∋ₐ zero    = zero
↑∋ₐ (suc i) = suc (↑∋ₐ i)


↑ : ∀ {Δ Γ A} → Γ IPL.⊢ A true
              → Δ ⊢ ↑ₚ A valid[ ↑ₚₛ Γ ]
↑ (IPL.var i)   = var (↑∋ₚ i)
↑ (IPL.lam 𝒟)   = lam (↑ 𝒟)
↑ (IPL.app 𝒟 ℰ) = app (↑ 𝒟) (↑ ℰ)


--------------------------------------------------------------------------------


lem-var : ∀ {X A} → (Ξ Ψ : List X)
                  → Ξ ⧺ Ψ ∋ A
                  → Ξ ∋ A ⊎ Ψ ∋ A
lem-var Ξ ∙       i       = inj₁ i
lem-var Ξ (Ψ , A) zero    = inj₂ zero
lem-var Ξ (Ψ , B) (suc i) with lem-var Ξ Ψ i
...                       | inj₁ i′ = inj₁ i′
...                       | inj₂ i′ = inj₂ (suc i′)


gen↑ : ∀ {Δ Γ A} → Δ ⧺ Γ IPL.⊢ A true
                 → ↑ₐₛ Δ ⊢ ↑ₚ A valid[ ↑ₚₛ Γ ]
gen↑ {Δ} {Γ} (IPL.var i)   with lem-var Δ Γ i
...                        | inj₁ i′ = mvar (↑∋ₐ i′)
...                        | inj₂ i′ = var (↑∋ₚ i′)
gen↑ {Δ} {Γ} (IPL.lam 𝒟)   = lam (gen↑ 𝒟)
gen↑ {Δ} {Γ} (IPL.app 𝒟 ℰ) = app (gen↑ 𝒟) (gen↑ ℰ)


--------------------------------------------------------------------------------


intern : ∀ {Δ A} → Δ IPL.⊢ A true
                 → ↑ₐₛ Δ ⊢ □ (↑ₚ A) valid[ ∙ ]
intern {∙}     𝒟 = box (↑ 𝒟)
intern {Γ , B} 𝒟 = unvau (boxapp (wk (intern (IPL.lam 𝒟))) vz)


--------------------------------------------------------------------------------
