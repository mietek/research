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
  infix 3 ⊢_checked
  data ⊢_checked : TypeChecking → Set
    where
      lam : ∀ {A B g M} → {Γ : Types g}
                        → ⊢ Γ , A ⊦ M ≪ B checked
                        → ⊢ Γ ⊦ LAM M ≪ A ⊃ B checked

      inf : ∀ {A g M} → {Γ : Types g}
                      → ⊢ Γ ⊦ M ≫ A inferred
                      → ⊢ Γ ⊦ INF M ≪ A checked

  infix 3 ⊢_inferred
  data ⊢_inferred : TypeInference → Set
    where
      var : ∀ {A g I} → {Γ : Types g}
                      → Γ ∋⟨ I ⟩ A
                      → ⊢ Γ ⊦ VAR I ≫ A inferred

      app : ∀ {A B g M N} → {Γ : Types g}
                          → ⊢ Γ ⊦ M ≫ A ⊃ B inferred → ⊢ Γ ⊦ N ≪ A checked
                          → ⊢ Γ ⊦ APP M N ≫ B inferred

      chk : ∀ {A g M} → {Γ : Types g}
                      → ⊢ Γ ⊦ M ≪ A checked
                      → ⊢ Γ ⊦ CHK M A ≫ A inferred


--------------------------------------------------------------------------------


mutual
  renₗ : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                        → Γ′ ⊇⟨ e ⟩ Γ → ⊢ Γ ⊦ M ≪ A checked
                        → ⊢ Γ′ ⊦ RENₗ e M ≪ A checked
  renₗ η (lam 𝒟) = lam (renₗ (keep η) 𝒟)
  renₗ η (inf 𝒟) = inf (renᵣ η 𝒟)

  renᵣ : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                        → Γ′ ⊇⟨ e ⟩ Γ → ⊢ Γ ⊦ M ≫ A inferred
                        → ⊢ Γ′ ⊦ RENᵣ e M ≫ A inferred
  renᵣ η (var i)   = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₗ η ℰ)
  renᵣ η (chk 𝒟)   = chk (renₗ η 𝒟)


wkᵣ : ∀ {B g M A} → {Γ : Types g}
                  → ⊢ Γ ⊦ M ≫ A inferred
                  → ⊢ Γ , B ⊦ WKᵣ M ≫ A inferred
wkᵣ 𝒟 = renᵣ (drop id⊇) 𝒟


vzᵣ : ∀ {A g} → {Γ : Types g}
              → ⊢ Γ , A ⊦ VZᵣ ≫ A inferred
vzᵣ = var zero


--------------------------------------------------------------------------------
