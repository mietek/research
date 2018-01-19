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
  infix 3 ⊢ₗ_
  data ⊢ₗ_ : TypeChecking → Set
    where
      lam : ∀ {A B g M} → {Γ : Types g}
                        → ⊢ₗ Γ , A ⊦ M ≪ B
                        → ⊢ₗ Γ ⊦ LAM M ≪ A ⊃ B

      inf : ∀ {A g M} → {Γ : Types g}
                      → ⊢ᵣ Γ ⊦ M ≫ A
                      → ⊢ₗ Γ ⊦ INF M ≪ A

  infix 3 ⊢ᵣ_
  data ⊢ᵣ_ : TypeInference → Set
    where
      var : ∀ {A g I} → {Γ : Types g}
                      → Γ ∋⟨ I ⟩ A
                      → ⊢ᵣ Γ ⊦ VAR I ≫ A

      app : ∀ {A B g M N} → {Γ : Types g}
                          → ⊢ᵣ Γ ⊦ M ≫ A ⊃ B → ⊢ₗ Γ ⊦ N ≪ A
                          → ⊢ᵣ Γ ⊦ APP M N ≫ B

      chk : ∀ {A g M} → {Γ : Types g}
                      → ⊢ₗ Γ ⊦ M ≪ A
                      → ⊢ᵣ Γ ⊦ CHK M A ≫ A


--------------------------------------------------------------------------------


mutual
  renₗ : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                        → Γ′ ⊇⟨ e ⟩ Γ → ⊢ₗ Γ ⊦ M ≪ A
                        → ⊢ₗ Γ′ ⊦ RENₗ e M ≪ A
  renₗ η (lam 𝒟) = lam (renₗ (keep η) 𝒟)
  renₗ η (inf 𝒟) = inf (renᵣ η 𝒟)

  renᵣ : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                        → Γ′ ⊇⟨ e ⟩ Γ → ⊢ᵣ Γ ⊦ M ≫ A
                        → ⊢ᵣ Γ′ ⊦ RENᵣ e M ≫ A
  renᵣ η (var i)   = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₗ η ℰ)
  renᵣ η (chk 𝒟)   = chk (renₗ η 𝒟)


wkᵣ : ∀ {B g M A} → {Γ : Types g}
                  → ⊢ᵣ Γ ⊦ M ≫ A
                  → ⊢ᵣ Γ , B ⊦ WKᵣ M ≫ A
wkᵣ 𝒟 = renᵣ (drop id⊇) 𝒟


vzᵣ : ∀ {A g} → {Γ : Types g}
              → ⊢ᵣ Γ , A ⊦ VZᵣ ≫ A
vzᵣ = var zero


--------------------------------------------------------------------------------
