module A201801.STLCStandardBidirectionalDerivations-CheckedInferred where

open import A201801.Prelude
open import A201801.Vec
open import A201801.STLCTypes
open import A201801.STLCStandardDerivations
open import A201801.STLCStandardBidirectionalTerms-CheckedInferred


--------------------------------------------------------------------------------


mutual
  infix 3 ⊢_≪_checked[_]
  data ⊢_≪_checked[_] : ∀ {g} → Termₗ g → Type → Types g → Set
    where
      lam : ∀ {A B g M} → {Γ : Types g}
                        → ⊢ M ≪ B checked[ Γ , A ]
                        → ⊢ LAM M ≪ A ⊃ B checked[ Γ ]

      inf : ∀ {A g M} → {Γ : Types g}
                      → ⊢ M ≫ A inferred[ Γ ]
                      → ⊢ INF M ≪ A checked[ Γ ]

  infix 3 ⊢_≫_inferred[_]
  data ⊢_≫_inferred[_] : ∀ {g} → Termᵣ g → Type → Types g → Set
    where
      var : ∀ {A g I} → {Γ : Types g}
                      → Γ ∋⟨ I ⟩ A
                      → ⊢ VAR I ≫ A inferred[ Γ ]

      app : ∀ {A B g M N} → {Γ : Types g}
                          → ⊢ M ≫ A ⊃ B inferred[ Γ ] → ⊢ N ≪ A checked[ Γ ]
                          → ⊢ APP M N ≫ B inferred[ Γ ]

      chk : ∀ {A g M} → {Γ : Types g}
                      → ⊢ M ≪ A checked[ Γ ]
                      → ⊢ CHK M A ≫ A inferred[ Γ ]


--------------------------------------------------------------------------------


mutual
  renₗ : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                        → Γ′ ⊇⟨ e ⟩ Γ → ⊢ M ≪ A checked[ Γ ]
                        → ⊢ RENₗ e M ≪ A checked[ Γ′ ]
  renₗ η (lam 𝒟) = lam (renₗ (keep η) 𝒟)
  renₗ η (inf 𝒟) = inf (renᵣ η 𝒟)

  renᵣ : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                        → Γ′ ⊇⟨ e ⟩ Γ → ⊢ M ≫ A inferred[ Γ ]
                        → ⊢ RENᵣ e M ≫ A inferred[ Γ′ ]
  renᵣ η (var i)   = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₗ η ℰ)
  renᵣ η (chk 𝒟)   = chk (renₗ η 𝒟)


--------------------------------------------------------------------------------


wkᵣ : ∀ {B g M A} → {Γ : Types g}
                  → ⊢ M ≫ A inferred[ Γ ]
                  → ⊢ WKᵣ M ≫ A inferred[ Γ , B ]
wkᵣ 𝒟 = renᵣ (drop id⊇) 𝒟


vzᵣ : ∀ {A g} → {Γ : Types g}
              → ⊢ VZᵣ ≫ A inferred[ Γ , A ]
vzᵣ = var zero


--------------------------------------------------------------------------------
