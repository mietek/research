module STLCTypeCheckingDerivations where

open import Prelude
open import Vec
open import STLCTypes
open import STLCTypeCheckingTerms
open import SimpleSTLCDerivations


--------------------------------------------------------------------------------


infix 4 _⊦_≪_
record TypeChecking : Set
  where
    constructor _⊦_≪_
    field
      {g} : Nat
      Γ   : Types g
      M   : TermL g
      A   : Type


infix 4 _⊦_≫_
record TypeInference : Set
  where
    constructor _⊦_≫_
    field
      {g} : Nat
      Γ   : Types g
      M   : TermR g
      A   : Type


--------------------------------------------------------------------------------


mutual
  infix 3 ⊢ₗ_
  data ⊢ₗ_ : TypeChecking → Set
    where
      lam : ∀ {A B g M} → {Γ : Types g}
                        → ⊢ₗ Γ , A ⊦ M ≪ B
                        → ⊢ₗ Γ ⊦ LAM M ≪ A ⊃ B

      infer : ∀ {A g M} → {Γ : Types g}
                        → ⊢ᵣ Γ ⊦ M ≫ A
                        → ⊢ₗ Γ ⊦ INFER M ≪ A

  infix 3 ⊢ᵣ_
  data ⊢ᵣ_ : TypeInference → Set
    where
      var : ∀ {A g I} → {Γ : Types g}
                      → Γ ∋⟨ I ⟩ A
                      → ⊢ᵣ Γ ⊦ VAR I ≫ A

      app : ∀ {A B g M N} → {Γ : Types g}
                          → ⊢ᵣ Γ ⊦ M ≫ A ⊃ B → ⊢ₗ Γ ⊦ N ≪ A
                          → ⊢ᵣ Γ ⊦ APP M N ≫ B

      check : ∀ {A g M} → {Γ : Types g}
                        → ⊢ₗ Γ ⊦ M ≪ A
                        → ⊢ᵣ Γ ⊦ CHECK M A ≫ A


--------------------------------------------------------------------------------


uniqR : ∀ {g M A₁ A₂} → {Γ : Types g}
                      → ⊢ᵣ Γ ⊦ M ≫ A₁ → ⊢ᵣ Γ ⊦ M ≫ A₂
                      → A₁ ≡ A₂
uniqR (var i₁)    (var i₂)    = uniq∋ i₁ i₂
uniqR (app 𝒟₁ ℰ₁) (app 𝒟₂ ℰ₂) = inj⊃₂ (uniqR 𝒟₁ 𝒟₂)
uniqR (check 𝒟₁)  (check 𝒟₂)  = refl


mutual
  recoverL : ∀ {g M A} → {Γ : Types g}
                       → ⊢ₗ Γ ⊦ M ≪ A
                       → ⊢ Γ ⊦ RECOVERL M ⦂ A
  recoverL (lam 𝒟)   = lam (recoverL 𝒟)
  recoverL (infer 𝒟) = recoverR 𝒟

  recoverR : ∀ {g M A} → {Γ : Types g}
                       → ⊢ᵣ Γ ⊦ M ≫ A
                       → ⊢ Γ ⊦ RECOVERR M ⦂ A
  recoverR (var i)   = var i
  recoverR (app 𝒟 ℰ) = app (recoverR 𝒟) (recoverL ℰ)
  recoverR (check 𝒟) = recoverL 𝒟


--------------------------------------------------------------------------------


mutual
  renL : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                        → Γ′ ⊇⟨ e ⟩ Γ → ⊢ₗ Γ ⊦ M ≪ A
                        → ⊢ₗ Γ′ ⊦ RENL e M ≪ A
  renL η (lam 𝒟)   = lam (renL (keep η) 𝒟)
  renL η (infer 𝒟) = infer (renR η 𝒟)

  renR : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                        → Γ′ ⊇⟨ e ⟩ Γ → ⊢ᵣ Γ ⊦ M ≫ A
                        → ⊢ᵣ Γ′ ⊦ RENR e M ≫ A
  renR η (var i)   = var (ren∋ η i)
  renR η (app 𝒟 ℰ) = app (renR η 𝒟) (renL η ℰ)
  renR η (check 𝒟) = check (renL η 𝒟)


wkR : ∀ {B g M A} → {Γ : Types g}
                  → ⊢ᵣ Γ ⊦ M ≫ A
                  → ⊢ᵣ Γ , B ⊦ WKR M ≫ A
wkR 𝒟 = renR (drop id⊇) 𝒟


vzR : ∀ {A g} → {Γ : Types g}
              → ⊢ᵣ Γ , A ⊦ VZR ≫ A
vzR = var zero


--------------------------------------------------------------------------------
