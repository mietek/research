module BidirectionalSTLCRawDerivationsForNameResolution where

open import Prelude
open import Fin
open import Vec
open import BidirectionalSTLCRawTermsForNameResolution
open import BidirectionalSTLCTermsForTypeChecking


--------------------------------------------------------------------------------


mutual
  data ⊢ₗ_⊦_≪_ : ∀ {g} → Names g → RawTermₗ → Termₗ g → Set
    where
      lam : ∀ {x g P M} → {И : Names g}
                        → ⊢ₗ И , x ⊦ P ≪ M
                        → ⊢ₗ И ⊦ LAM x P ≪ LAM M

      inf : ∀ {g P M} → {И : Names g}
                      → ⊢ᵣ И ⊦ P ≫ M
                      → ⊢ₗ И ⊦ INF P ≪ INF M

  data ⊢ᵣ_⊦_≫_ : ∀ {g} → Names g → RawTermᵣ → Termᵣ g → Set
    where
      vz : ∀ {x g} → {И : Names g}
                   → ⊢ᵣ И , x ⊦ VAR x ≫ VAR zero

      wk : ∀ {x y g I} → {И : Names g}
                       → x ≢ y → ⊢ᵣ И ⊦ VAR x ≫ VAR I
                       → ⊢ᵣ И , y ⊦ VAR x ≫ VAR (suc I)

      app : ∀ {g P Q M N} → {И : Names g}
                          → ⊢ᵣ И ⊦ P ≫ M → ⊢ₗ И ⊦ Q ≪ N
                          → ⊢ᵣ И ⊦ APP P Q ≫ APP M N

      chk : ∀ {A g P M} → {И : Names g}
                        → ⊢ₗ И ⊦ P ≪ M
                        → ⊢ᵣ И ⊦ CHK P A ≫ CHK M A


--------------------------------------------------------------------------------
