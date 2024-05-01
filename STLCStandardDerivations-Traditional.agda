module A201801.STLCStandardDerivations-Traditional where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.Vec
open import A201801.AllVec
open import A201801.STLCTypes
open import A201801.STLCStandardTerms
import A201801.STLCStandardDerivations as STLC


--------------------------------------------------------------------------------


infix 3 _⊢_⦂_true
data _⊢_⦂_true : ∀ {g} → Types g → Term g → Type → Set
  where
    var : ∀ {A g I} → {Γ : Types g}
                    → Γ ∋⟨ I ⟩ A
                    → Γ ⊢ VAR I ⦂ A true

    lam : ∀ {A B g M} → {Γ : Types g}
                      → Γ , A ⊢ M ⦂ B true
                      → Γ ⊢ LAM M ⦂ A ⊃ B true

    app : ∀ {A B g M N} → {Γ : Types g}
                        → Γ ⊢ M ⦂ A ⊃ B true → Γ ⊢ N ⦂ A true
                        → Γ ⊢ APP M N ⦂ B true


--------------------------------------------------------------------------------


↓ : ∀ {g M A} → {Γ : Types g}
              → Γ ⊢ M ⦂ A true
              → STLC.⊢ M ⦂ A valid[ Γ ]
↓ (var i)   = STLC.var i
↓ (lam 𝒟)   = STLC.lam (↓ 𝒟)
↓ (app 𝒟 ℰ) = STLC.app (↓ 𝒟) (↓ ℰ)


↑ : ∀ {g M A} → {Γ : Types g}
              → STLC.⊢ M ⦂ A valid[ Γ ]
              → Γ ⊢ M ⦂ A true
↑ (STLC.var i)   = var i
↑ (STLC.lam 𝒟)   = lam (↑ 𝒟)
↑ (STLC.app 𝒟 ℰ) = app (↑ 𝒟) (↑ ℰ)


id↓↑ : ∀ {g M A} → {Γ : Types g}
                 → (𝒟 : STLC.⊢ M ⦂ A valid[ Γ ])
                 → (↓ ∘ ↑) 𝒟 ≡ 𝒟
id↓↑ (STLC.var i)   = refl
id↓↑ (STLC.lam 𝒟)   = STLC.lam & id↓↑ 𝒟
id↓↑ (STLC.app 𝒟 ℰ) = STLC.app & id↓↑ 𝒟 ⊗ id↓↑ ℰ


id↑↓ : ∀ {g M A} → {Γ : Types g}
                 → (𝒟 : Γ ⊢ M ⦂ A true)
                 → (↑ ∘ ↓) 𝒟 ≡ 𝒟
id↑↓ (var i)   = refl
id↑↓ (lam 𝒟)   = lam & id↑↓ 𝒟
id↑↓ (app 𝒟 ℰ) = app & id↑↓ 𝒟 ⊗ id↑↓ ℰ


--------------------------------------------------------------------------------
