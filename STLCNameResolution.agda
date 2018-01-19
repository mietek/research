module STLCNameResolution where

open import Prelude
open import Names
open import Fin
open import Vec
open import STLCBidirectionalTermsForTypeChecking
open import STLCBidirectionalRawTermsForNameResolution
open import STLCBidirectionalRawDerivationsForNameResolution


--------------------------------------------------------------------------------


injvzwk : ∀ {g x y M} → {И : Names g}
                      → ⊢ᵣ И , y ⊦ VAR x ≫ M
                      → x ≡ y ⊎ Σ (Termᵣ g) (\ M′ → ⊢ᵣ И ⊦ VAR x ≫ M′)
injvzwk vz       = inj₁ refl
injvzwk (wk p 𝒟) = inj₂ (VAR _ , 𝒟)


find : ∀ {g} → (И : Names g) (x : Name)
             → Dec (Σ (Termᵣ g) (\ M → ⊢ᵣ И ⊦ VAR x ≫ M))
find ∙       x  = no (\ { (M , ())})
find (И , y) x  with x ≟ₛ y
find (И , x) .x | yes refl = yes (VAR zero , vz)
find (И , y) x  | no x≢y   with find И x
find (И , y) x  | no x≢y   | yes (VAR I , 𝒟)    = yes (VAR (suc I) , wk x≢y 𝒟)
find (И , y) x  | no x≢y   | yes (APP M N , ())
find (И , y) x  | no x≢y   | yes (CHK M A , ())
find (И , y) x  | no x≢y   | no ¬M𝒟             = no (\ { (M′ , 𝒟′) → case injvzwk 𝒟′ of
                                                       (\ { (inj₁ refl) → refl ↯ x≢y
                                                          ; (inj₂ M𝒟) → M𝒟 ↯ ¬M𝒟
                                                          }) })


mutual
  resolveₗ : ∀ {g} → (И : Names g) (P : RawTermₗ)
                   → Dec (Σ (Termₗ g) (\ M → ⊢ₗ И ⊦ P ≪ M))
  resolveₗ И (LAM x P) with resolveₗ (И , x) P
  resolveₗ И (LAM x P) | yes (M , 𝒟) = yes (LAM M , lam 𝒟)
  resolveₗ И (LAM x P) | no ¬M𝒟      = no (\ { (LAM M′ , lam 𝒟′) → (M′ , 𝒟′) ↯ ¬M𝒟 })
  resolveₗ И (INF P)   with resolveᵣ И P
  resolveₗ И (INF P)   | yes (M , 𝒟) = yes (INF M , inf 𝒟)
  resolveₗ И (INF P)   | no ¬M𝒟      = no (\ { (INF M′ , inf 𝒟′) → (M′ , 𝒟′) ↯ ¬M𝒟  })

  resolveᵣ : ∀ {g} → (И : Names g) (P : RawTermᵣ)
                   → Dec (Σ (Termᵣ g) (\ M → ⊢ᵣ И ⊦ P ≫ M))
  resolveᵣ И (VAR x)   = find И x
  resolveᵣ И (APP P Q) with resolveᵣ И P | resolveₗ И Q
  resolveᵣ И (APP P Q) | yes (M , 𝒟) | yes (N , ℰ) = yes (APP M N , app 𝒟 ℰ)
  resolveᵣ И (APP P Q) | yes (M , 𝒟) | no ¬Nℰ      = no (\ { (APP M′ N′ , app 𝒟′ ℰ′) → (N′ , ℰ′) ↯ ¬Nℰ })
  resolveᵣ И (APP P Q) | no ¬M𝒟      | _           = no (\ { (APP M′ N′ , app 𝒟′ ℰ′) → (M′ , 𝒟′) ↯ ¬M𝒟 })
  resolveᵣ И (CHK P A) with resolveₗ И P
  resolveᵣ И (CHK P A) | yes (M , 𝒟) = yes (CHK M A , chk 𝒟)
  resolveᵣ И (CHK P A) | no ¬M𝒟      = no (\ { (CHK M′ A′ , chk 𝒟′) → (M′ , 𝒟′) ↯ ¬M𝒟  })


--------------------------------------------------------------------------------
