module S4-IPLTranslation where

open import Prelude
open import List
open import ListConcatenation
open import S4Propositions
open import S4Derivations
import IPLPropositions as IPL
import IPLDerivations as IPL


--------------------------------------------------------------------------------


⌈_⌉ : IPL.Prop → Prop
⌈ IPL.BASE ⌉  = BASE
⌈ A IPL.⊃ B ⌉ = ⌈ A ⌉ ⊃ ⌈ B ⌉


⌈_⌉* : List IPL.Prop → List Prop
⌈ Γ ⌉* = map ⌈_⌉ Γ


↑∋ : ∀ {Γ A} → Γ ∋ A
             → ⌈ Γ ⌉* ∋ ⌈ A ⌉
↑∋ zero    = zero
↑∋ (suc i) = suc (↑∋ i)


↑ : ∀ {Δ Γ A} → Γ IPL.⊢ A true
              → Δ ⨾ ⌈ Γ ⌉* ⊢ ⌈ A ⌉ true
↑ (IPL.var i)   = var (↑∋ i)
↑ (IPL.lam 𝒟)   = lam (↑ 𝒟)
↑ (IPL.app 𝒟 ℰ) = app (↑ 𝒟) (↑ ℰ)


--------------------------------------------------------------------------------


⌊_⌋ : Prop → IPL.Prop
⌊ BASE ⌋  = IPL.BASE
⌊ A ⊃ B ⌋ = ⌊ A ⌋ IPL.⊃ ⌊ B ⌋
⌊ □ A ⌋   = ⌊ A ⌋


⌊_⌋* : List Prop → List IPL.Prop
⌊ Γ ⌋* = map ⌊_⌋ Γ


↓∋ : ∀ {Γ A} → Γ ∋ A
             → ⌊ Γ ⌋* ∋ ⌊ A ⌋
↓∋ zero    = zero
↓∋ (suc i) = suc (↓∋ i)


pull : ∀ {Δ A B} → (Γ : List IPL.Prop) → (Δ , A) ⧺ Γ IPL.⊢ B true
                 → Δ ⧺ (Γ , A) IPL.⊢ B true
pull Γ (IPL.var i)   = IPL.var (pull∋ Γ i )
pull Γ (IPL.lam 𝒟)   = IPL.lam (IPL.exch (pull (Γ , _) 𝒟))
pull Γ (IPL.app 𝒟 ℰ) = IPL.app (pull Γ 𝒟) (pull Γ ℰ)


↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
              → ⌊ Δ ⌋* ⧺ ⌊ Γ ⌋* IPL.⊢ ⌊ A ⌋ true
↓ {Δ = Δ} (var i)      = IPL.ren (ldrops ⌊ Δ ⌋* id⊇) (IPL.var (↓∋ i))
↓         (lam 𝒟)      = IPL.lam (↓ 𝒟)
↓         (app 𝒟 ℰ)    = IPL.app (↓ 𝒟) (↓ ℰ)
↓ {Γ = Γ} (mvar i)     = IPL.ren (rdrops ⌊ Γ ⌋* id⊇) (IPL.var (↓∋ i))
↓ {Γ = Γ} (box 𝒟)      = IPL.ren (rdrops ⌊ Γ ⌋* id⊇) (↓ 𝒟)
↓ {Γ = Γ} (letbox 𝒟 ℰ) = IPL.cut (↓ 𝒟) (pull ⌊ Γ ⌋* (↓ ℰ))

    
--------------------------------------------------------------------------------
