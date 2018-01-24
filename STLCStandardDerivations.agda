module STLCStandardDerivations where

open import Prelude
open import Category
open import Fin
open import Vec
open import AllVec
open import STLCTypes
open import STLCTerms
import STLCDerivations as STLC


--------------------------------------------------------------------------------


infix 3 _⊢_⦂_
data _⊢_⦂_ : ∀ {g} → Types g → Term g → Type → Set
  where
    var : ∀ {A g I} → {Γ : Types g}
                    → Γ ∋⟨ I ⟩ A
                    → Γ ⊢ VAR I ⦂ A

    lam : ∀ {A B g M} → {Γ : Types g}
                      → Γ , A ⊢ M ⦂ B
                      → Γ ⊢ LAM M ⦂ A ⊃ B

    app : ∀ {A B g M N} → {Γ : Types g}
                        → Γ ⊢ M ⦂ A ⊃ B → Γ ⊢ N ⦂ A
                        → Γ ⊢ APP M N ⦂ B


--------------------------------------------------------------------------------


↓ : ∀ {g M A} → {Γ : Types g}
              → Γ ⊢ M ⦂ A
              → STLC.⊢ M ⦂ A valid[ Γ ]
↓ (var i)   = STLC.var i
↓ (lam 𝒟)   = STLC.lam (↓ 𝒟)
↓ (app 𝒟 ℰ) = STLC.app (↓ 𝒟) (↓ ℰ)


↑ : ∀ {g M A} → {Γ : Types g}
              → STLC.⊢ M ⦂ A valid[ Γ ]
              → Γ ⊢ M ⦂ A
↑ (STLC.var i)   = var i
↑ (STLC.lam 𝒟)   = lam (↑ 𝒟)
↑ (STLC.app 𝒟 ℰ) = app (↑ 𝒟) (↑ ℰ)


--------------------------------------------------------------------------------


id↓↑ : ∀ {g M A} → {Γ : Types g}
                 → (𝒟 : STLC.⊢ M ⦂ A valid[ Γ ])
                 → (↓ ∘ ↑) 𝒟 ≡ 𝒟
id↓↑ (STLC.var i)   = refl
id↓↑ (STLC.lam 𝒟)   = STLC.lam & id↓↑ 𝒟
id↓↑ (STLC.app 𝒟 ℰ) = STLC.app & id↓↑ 𝒟 ⊗ id↓↑ ℰ


id↑↓ : ∀ {g M A} → {Γ : Types g}
                 → (𝒟 : Γ ⊢ M ⦂ A)
                 → (↑ ∘ ↓) 𝒟 ≡ 𝒟
id↑↓ (var i)   = refl
id↑↓ (lam 𝒟)   = lam & id↑↓ 𝒟
id↑↓ (app 𝒟 ℰ) = app & id↑↓ 𝒟 ⊗ id↑↓ ℰ


--------------------------------------------------------------------------------
