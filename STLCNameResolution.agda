module STLCNameResolution where

open import Prelude
open import Names
open import Fin
open import Vec
open import STLCBidirectionalTermsForTypeChecking
open import STLCBidirectionalTermsForNameResolution
open import STLCBidirectionalDerivationsForNameResolution


--------------------------------------------------------------------------------


injvzwk : ∀ {g x y M} → {Γ : Names g}
                      → ⊢ Γ , y ⊦ VAR x ≫ M toinfer
                      → x ≡ y ⊎ Σ (Termᵣ g) (\ M′ → ⊢ Γ ⊦ VAR x ≫ M′ toinfer)
injvzwk vz       = inj₁ refl
injvzwk (wk p 𝒟) = inj₂ (VAR _ , 𝒟)


find : ∀ {g} → (Γ : Names g) (x : Name)
             → Dec (Σ (Termᵣ g) (\ M → ⊢ Γ ⊦ VAR x ≫ M toinfer))
find ∙       x  = no (\ { (M , ())})
find (Γ , y) x  with x ≟ₛ y
find (Γ , x) .x | yes refl = yes (VAR zero , vz)
find (Γ , y) x  | no x≢y   with find Γ x
find (Γ , y) x  | no x≢y   | yes (VAR I , 𝒟)    = yes (VAR (suc I) , wk x≢y 𝒟)
find (Γ , y) x  | no x≢y   | yes (APP M N , ())
find (Γ , y) x  | no x≢y   | yes (CHK M A , ())
find (Γ , y) x  | no x≢y   | no ¬M𝒟             = no (\ { (M′ , 𝒟′) → case injvzwk 𝒟′ of
                                                       (\ { (inj₁ x≡y) → x≡y ↯ x≢y
                                                          ; (inj₂ M𝒟) → M𝒟 ↯ ¬M𝒟
                                                          }) })


mutual
  resolveₗ : ∀ {g} → (Γ : Names g) (P : PreTermₗ)
                   → Dec (Σ (Termₗ g) (\ M → ⊢ Γ ⊦ P ≫ M tocheck))
  resolveₗ Γ (LAM x P) with resolveₗ (Γ , x) P
  resolveₗ Γ (LAM x P) | yes (M , 𝒟) = yes (LAM M , lam 𝒟)
  resolveₗ Γ (LAM x P) | no ¬M𝒟      = no (\ { (LAM M′ , lam 𝒟′) → (M′ , 𝒟′) ↯ ¬M𝒟 })
  resolveₗ Γ (INF P)   with resolveᵣ Γ P
  resolveₗ Γ (INF P)   | yes (M , 𝒟) = yes (INF M , inf 𝒟)
  resolveₗ Γ (INF P)   | no ¬M𝒟      = no (\ { (INF M′ , inf 𝒟′) → (M′ , 𝒟′) ↯ ¬M𝒟  })

  resolveᵣ : ∀ {g} → (Γ : Names g) (P : PreTermᵣ)
                   → Dec (Σ (Termᵣ g) (\ M → ⊢ Γ ⊦ P ≫ M toinfer))
  resolveᵣ Γ (VAR x)   = find Γ x
  resolveᵣ Γ (APP P Q) with resolveᵣ Γ P | resolveₗ Γ Q
  resolveᵣ Γ (APP P Q) | yes (M , 𝒟) | yes (N , ℰ) = yes (APP M N , app 𝒟 ℰ)
  resolveᵣ Γ (APP P Q) | yes (M , 𝒟) | no ¬Nℰ      = no (\ { (APP M′ N′ , app 𝒟′ ℰ′) → (N′ , ℰ′) ↯ ¬Nℰ })
  resolveᵣ Γ (APP P Q) | no ¬M𝒟      | _           = no (\ { (APP M′ N′ , app 𝒟′ ℰ′) → (M′ , 𝒟′) ↯ ¬M𝒟 })
  resolveᵣ Γ (CHK P A) with resolveₗ Γ P
  resolveᵣ Γ (CHK P A) | yes (M , 𝒟) = yes (CHK M A , chk 𝒟)
  resolveᵣ Γ (CHK P A) | no ¬M𝒟      = no (\ { (CHK M′ A′ , chk 𝒟′) → (M′ , 𝒟′) ↯ ¬M𝒟  })


--------------------------------------------------------------------------------
