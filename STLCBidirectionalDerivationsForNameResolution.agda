module STLCBidirectionalDerivationsForNameResolution where

open import Prelude
open import Names
open import Fin
open import Vec
open import STLCBidirectionalTermsForTypeChecking
open import STLCBidirectionalTermsForNameResolution


--------------------------------------------------------------------------------


mutual
  infix 3 ⊢_⊦_≫_tocheck
  data ⊢_⊦_≫_tocheck : ∀ {g} → Names g → RawTermₗ → Termₗ g → Set
    where
      lam : ∀ {x g P M} → {Γ : Names g}
                        → ⊢ Γ , x ⊦ P ≫ M tocheck
                        → ⊢ Γ ⊦ LAM x P ≫ LAM M tocheck

      inf : ∀ {g P M} → {Γ : Names g}
                      → ⊢ Γ ⊦ P ≫ M toinfer
                      → ⊢ Γ ⊦ INF P ≫ INF M tocheck

  infix 3 ⊢_⊦_≫_toinfer
  data ⊢_⊦_≫_toinfer : ∀ {g} → Names g → RawTermᵣ → Termᵣ g → Set
    where
      vz : ∀ {x g} → {Γ : Names g}
                   → ⊢ Γ , x ⊦ VAR x ≫ VAR zero toinfer

      wk : ∀ {x y g I} → {Γ : Names g}
                       → x ≢ y → ⊢ Γ ⊦ VAR x ≫ VAR I toinfer
                       → ⊢ Γ , y ⊦ VAR x ≫ VAR (suc I) toinfer

      app : ∀ {g P Q M N} → {Γ : Names g}
                          → ⊢ Γ ⊦ P ≫ M toinfer → ⊢ Γ ⊦ Q ≫ N tocheck
                          → ⊢ Γ ⊦ APP P Q ≫ APP M N toinfer

      chk : ∀ {A g P M} → {Γ : Names g}
                        → ⊢ Γ ⊦ P ≫ M tocheck
                        → ⊢ Γ ⊦ CHK P A ≫ CHK M A toinfer


--------------------------------------------------------------------------------
