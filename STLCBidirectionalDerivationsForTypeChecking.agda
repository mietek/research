module STLCBidirectionalDerivationsForTypeChecking where

open import Prelude
open import Vec
open import STLCTypes
open import STLCDerivations
open import STLCBidirectionalTermsForTypeChecking


--------------------------------------------------------------------------------


infix 4 _⊦_≪_
record TypeChecking : Set
  where
    constructor _⊦_≪_
    field
      {g} : Nat
      Γ   : Types g
      M   : Termₗ g
      A   : Type


infix 4 _⊦_≫_
record TypeInference : Set
  where
    constructor _⊦_≫_
    field
      {g} : Nat
      Γ   : Types g
      M   : Termᵣ g
      A   : Type


--------------------------------------------------------------------------------


mutual
  infix 3 ⊢_checks
  data ⊢_checks : TypeChecking → Set
    where
      lam : ∀ {A B g M} → {Γ : Types g}
                        → ⊢ Γ , A ⊦ M ≪ B checks
                        → ⊢ Γ ⊦ LAM M ≪ A ⊃ B checks

      inf : ∀ {A g M} → {Γ : Types g}
                      → ⊢ Γ ⊦ M ≫ A infers
                      → ⊢ Γ ⊦ INF M ≪ A checks

  infix 3 ⊢_infers
  data ⊢_infers : TypeInference → Set
    where
      var : ∀ {A g I} → {Γ : Types g}
                      → Γ ∋⟨ I ⟩ A
                      → ⊢ Γ ⊦ VAR I ≫ A infers

      app : ∀ {A B g M N} → {Γ : Types g}
                          → ⊢ Γ ⊦ M ≫ A ⊃ B infers → ⊢ Γ ⊦ N ≪ A checks
                          → ⊢ Γ ⊦ APP M N ≫ B infers

      chk : ∀ {A g M} → {Γ : Types g}
                      → ⊢ Γ ⊦ M ≪ A checks
                      → ⊢ Γ ⊦ CHK M A ≫ A infers


--------------------------------------------------------------------------------


mutual
  renₗ : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                        → Γ′ ⊇⟨ e ⟩ Γ → ⊢ Γ ⊦ M ≪ A checks
                        → ⊢ Γ′ ⊦ RENₗ e M ≪ A checks
  renₗ η (lam 𝒟) = lam (renₗ (keep η) 𝒟)
  renₗ η (inf 𝒟) = inf (renᵣ η 𝒟)

  renᵣ : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                        → Γ′ ⊇⟨ e ⟩ Γ → ⊢ Γ ⊦ M ≫ A infers
                        → ⊢ Γ′ ⊦ RENᵣ e M ≫ A infers
  renᵣ η (var i)   = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₗ η ℰ)
  renᵣ η (chk 𝒟)   = chk (renₗ η 𝒟)


wkᵣ : ∀ {B g M A} → {Γ : Types g}
                  → ⊢ Γ ⊦ M ≫ A infers
                  → ⊢ Γ , B ⊦ WKᵣ M ≫ A infers
wkᵣ 𝒟 = renᵣ (drop id⊇) 𝒟


vzᵣ : ∀ {A g} → {Γ : Types g}
              → ⊢ Γ , A ⊦ VZᵣ ≫ A infers
vzᵣ = var zero


--------------------------------------------------------------------------------
