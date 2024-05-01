module A201801.FullS4EmbeddingOfFullIPL where

open import A201801.Prelude
open import A201801.List
open import A201801.FullS4Propositions
open import A201801.FullS4StandardDerivations
import A201801.FullIPLPropositions as IPL
import A201801.FullIPLDerivations as IPL


--------------------------------------------------------------------------------


↑ₚ : IPL.Form → Form
↑ₚ (IPL.ι P)   = ι P
↑ₚ (A IPL.⊃ B) = ↑ₚ A ⊃ ↑ₚ B
↑ₚ (A IPL.∧ B) = ↑ₚ A ∧ ↑ₚ B
↑ₚ IPL.𝟏       = 𝟏
↑ₚ IPL.𝟎       = 𝟎
↑ₚ (A IPL.∨ B) = ↑ₚ A ∨ ↑ₚ B


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


↑∋ₐ : ∀ {Γ A} → Γ ∋ A
              → ↑ₐₛ Γ ∋ ↑ₐ A
↑∋ₐ zero    = zero
↑∋ₐ (suc i) = suc (↑∋ₐ i)


↑ : ∀ {Δ Γ A} → Γ IPL.⊢ A true
              → Δ ⊢ ↑ₚ A valid[ ↑ₚₛ Γ ]
↑ (IPL.var i)      = var (↑∋ₚ i)
↑ (IPL.lam 𝒟)      = lam (↑ 𝒟)
↑ (IPL.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
↑ (IPL.pair 𝒟 ℰ)   = pair (↑ 𝒟) (↑ ℰ)
↑ (IPL.fst 𝒟)      = fst (↑ 𝒟)
↑ (IPL.snd 𝒟)      = snd (↑ 𝒟)
↑ IPL.unit         = unit
↑ (IPL.abort 𝒟)    = abort (↑ 𝒟)
↑ (IPL.inl 𝒟)      = inl (↑ 𝒟)
↑ (IPL.inr 𝒟)      = inr (↑ 𝒟)
↑ (IPL.case 𝒟 ℰ ℱ) = case (↑ 𝒟) (↑ ℰ) (↑ ℱ)


--------------------------------------------------------------------------------


intern : ∀ {Γ A} → Γ IPL.⊢ A true
                 → ↑ₐₛ Γ ⊢ □ (↑ₚ A) valid[ ∙ ]
intern {∙}     𝒟 = box (↑ 𝒟)
intern {Γ , B} 𝒟 = unvau (boxapp (wk (intern (IPL.lam 𝒟))) vz)


--------------------------------------------------------------------------------
