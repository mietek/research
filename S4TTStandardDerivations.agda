module S4TTStandardDerivations where

open import Prelude
open import Category
open import Fin
open import Vec
open import AllVec
open import S4TTTypes
open import S4TTTerms
import S4TTDerivations as S4TT


--------------------------------------------------------------------------------


infix 3 _⨾_⊢_⦂_true
data _⨾_⊢_⦂_true : ∀ {d g} → Asserts d → Types g → Term d g → Type → Set
  where
    var : ∀ {A d g i} → {Δ : Asserts d} {Γ : Types g}
                      → Γ ∋⟨ i ⟩ A
                      → Δ ⨾ Γ ⊢ VAR i ⦂ A true

    lam : ∀ {A B d g M} → {Δ : Asserts d} {Γ : Types g}
                        → Δ ⨾ Γ , A ⊢ M ⦂ B true
                        → Δ ⨾ Γ ⊢ LAM M ⦂ A ⊃ B true

    app : ∀ {A B d g M N} → {Δ : Asserts d} {Γ : Types g}
                          → Δ ⨾ Γ ⊢ M ⦂ A ⊃ B true → Δ ⨾ Γ ⊢ N ⦂ A true
                          → Δ ⨾ Γ ⊢ APP M N ⦂ B true

    mvar : ∀ {A d g i} → {Δ : Asserts d} {Γ : Types g}
                       → Δ ∋⟨ i ⟩ ⟪⊫ A ⟫
                       → Δ ⨾ Γ ⊢ MVAR i ⦂ A true

    box : ∀ {A d g M} → {Δ : Asserts d} {Γ : Types g}
                      → Δ ⨾ ∙ ⊢ M ⦂ A true
                      → Δ ⨾ Γ ⊢ BOX M ⦂ □ A true

    letbox : ∀ {A B d g M N} → {Δ : Asserts d} {Γ : Types g}
                             → Δ ⨾ Γ ⊢ M ⦂ □ A true → Δ , ⟪⊫ A ⟫ ⨾ Γ ⊢ N ⦂ B true
                             → Δ ⨾ Γ ⊢ LETBOX M N ⦂ B true


--------------------------------------------------------------------------------


↓ : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
                → Δ ⨾ Γ ⊢ M ⦂ A true
                → Δ S4TT.⊢ M ⦂ A valid[ Γ ]
↓ (var i)      = S4TT.var i
↓ (lam 𝒟)      = S4TT.lam (↓ 𝒟)
↓ (app 𝒟 ℰ)    = S4TT.app (↓ 𝒟) (↓ ℰ)
↓ (mvar i)     = S4TT.mvar i
↓ (box 𝒟)      = S4TT.box (↓ 𝒟)
↓ (letbox 𝒟 ℰ) = S4TT.letbox (↓ 𝒟) (↓ ℰ)


↑ : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
                → Δ S4TT.⊢ M ⦂ A valid[ Γ ]
                → Δ ⨾ Γ ⊢ M ⦂ A true
↑ (S4TT.var i)      = var i
↑ (S4TT.lam 𝒟)      = lam (↑ 𝒟)
↑ (S4TT.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
↑ (S4TT.mvar i)     = mvar i
↑ (S4TT.box 𝒟)      = box (↑ 𝒟)
↑ (S4TT.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)


id↓↑ : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
                   → (𝒟 : Δ S4TT.⊢ M ⦂ A valid[ Γ ])
                   → (↓ ∘ ↑) 𝒟 ≡ 𝒟
id↓↑ (S4TT.var i)      = refl
id↓↑ (S4TT.lam 𝒟)      = S4TT.lam & id↓↑ 𝒟
id↓↑ (S4TT.app 𝒟 ℰ)    = S4TT.app & id↓↑ 𝒟 ⊗ id↓↑ ℰ
id↓↑ (S4TT.mvar i)     = refl
id↓↑ (S4TT.box 𝒟)      = S4TT.box & id↓↑ 𝒟
id↓↑ (S4TT.letbox 𝒟 ℰ) = S4TT.letbox & id↓↑ 𝒟 ⊗ id↓↑ ℰ


id↑↓ : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
                   → (𝒟 : Δ ⨾ Γ ⊢ M ⦂ A true)
                   → (↑ ∘ ↓) 𝒟 ≡ 𝒟
id↑↓ (var i)      = refl
id↑↓ (lam 𝒟)      = lam & id↑↓ 𝒟
id↑↓ (app 𝒟 ℰ)    = app & id↑↓ 𝒟 ⊗ id↑↓ ℰ
id↑↓ (mvar i)     = refl
id↑↓ (box 𝒟)      = box & id↑↓ 𝒟
id↑↓ (letbox 𝒟 ℰ) = letbox & id↑↓ 𝒟 ⊗ id↑↓ ℰ


--------------------------------------------------------------------------------
