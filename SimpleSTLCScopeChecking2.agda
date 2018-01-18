module SimpleSTLCScopeChecking2 where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec
open import STLCTypes
open import STLCScopeCheckingTerms
open import STLCTypeCheckingTerms


--------------------------------------------------------------------------------


Name : Set
Name = String

Names : Nat → Set
Names n = Vec Name n


--------------------------------------------------------------------------------


mutual
  data RawTermL : Set
    where
      LAM   : Name → RawTermL → RawTermL
      INFER : RawTermR → RawTermL

  data RawTermR : Set
    where
      VAR   : Name → RawTermR
      APP   : RawTermR → RawTermL → RawTermR
      CHECK : RawTermL → Type → RawTermR


--------------------------------------------------------------------------------


mutual
  data ∴ₗ_⊢_≪_ : ∀ {g} → Names g → RawTermL → TermL g → Set
    where
      lam : ∀ {x g P M} → {И : Names g}
                         → ∴ₗ И , x ⊢ P ≪ M
                         → ∴ₗ И ⊢ LAM x P ≪ LAM M

      infer : ∀ {g P M} → {И : Names g}
                         → ∴ᵣ И ⊢ P ≫ M
                         → ∴ₗ И ⊢ INFER P ≪ INFER M

  data ∴ᵣ_⊢_≫_ : ∀ {g} → Names g → RawTermR → TermR g → Set
    where
      vz : ∀ {x g} → {И : Names g}
                   → ∴ᵣ И , x ⊢ VAR x ≫ VAR zero

      wk : ∀ {x y g I} → {И : Names g}
                       → x ≢ y → ∴ᵣ И ⊢ VAR x ≫ VAR I
                       → ∴ᵣ И , y ⊢ VAR x ≫ VAR (suc I)

      app : ∀ {g P Q M N} → {И : Names g}
                          → ∴ᵣ И ⊢ P ≫ M → ∴ₗ И ⊢ Q ≪ N
                          → ∴ᵣ И ⊢ APP P Q ≫ APP M N

      check : ∀ {A g P M} → {И : Names g}
                          → ∴ₗ И ⊢ P ≪ M
                          → ∴ᵣ И ⊢ CHECK P A ≫ CHECK M A


--------------------------------------------------------------------------------


injvzwk : ∀ {g x y M} → {И : Names g}
                      → ∴ᵣ И , y ⊢ VAR x ≫ M
                      → x ≡ y ⊎ Σ (TermR g) (\ M′ → ∴ᵣ И ⊢ VAR x ≫ M′)
injvzwk vz       = inj₁ refl
injvzwk (wk p 𝒟) = inj₂ (VAR _ , 𝒟)


find : ∀ {g} → (И : Names g) (x : Name)
                 → Dec (Σ (TermR g) (\ M → ∴ᵣ И ⊢ VAR x ≫ M))
find ∙       x  = no (\ ())
find (И , y) x  with x ≟ₛ y
find (И , x) .x | yes refl = yes (VAR zero , vz)
find (И , y) x  | no x≢y   with find И x
find (И , y) x  | no x≢y   | yes (VAR I , 𝒟)      = yes (VAR (suc I) , wk x≢y 𝒟)
find (И , y) x  | no x≢y   | yes (APP M N , ())
find (И , y) x  | no x≢y   | yes (CHECK M A , ())
find (И , y) x  | no x≢y   | no ¬M𝒟               = no (\ { (M′ , 𝒟′) → case injvzwk 𝒟′ of
                                                         (\ { (inj₁ refl) → refl ↯ x≢y
                                                            ; (inj₂ M𝒟) → M𝒟 ↯ ¬M𝒟
                                                            }) })


mutual
  resolveL : ∀ {g} → (И : Names g) (P : RawTermL)
                   → Dec (Σ (TermL g) (\ M → ∴ₗ И ⊢ P ≪ M))
  resolveL И (LAM x P) with resolveL (И , x) P
  resolveL И (LAM x P) | yes (M , 𝒟) = yes (LAM M , lam 𝒟)
  resolveL И (LAM x P) | no ¬M𝒟      = no (\ { (LAM M′ , lam 𝒟′) → (M′ , 𝒟′) ↯ ¬M𝒟 })
  resolveL И (INFER P) with resolveR И P
  resolveL И (INFER P) | yes (M , 𝒟) = yes (INFER M , infer 𝒟)
  resolveL И (INFER P) | no ¬M𝒟      = no (\ { (INFER M′ , infer 𝒟′) → (M′ , 𝒟′) ↯ ¬M𝒟  })

  resolveR : ∀ {g} → (И : Names g) (P : RawTermR)
                   → Dec (Σ (TermR g) (\ M → ∴ᵣ И ⊢ P ≫ M))
  resolveR И (VAR x)     = find И x
  resolveR И (APP P Q)   with resolveR И P | resolveL И Q
  resolveR И (APP P Q)   | yes (M , 𝒟) | yes (N , ℰ) = yes (APP M N , app 𝒟 ℰ)
  resolveR И (APP P Q)   | yes (M , 𝒟) | no ¬Nℰ      = no (\ { (APP M′ N′ , app 𝒟′ ℰ′) → (N′ , ℰ′) ↯ ¬Nℰ })
  resolveR И (APP P Q)   | no ¬M𝒟      | _           = no (\ { (APP M′ N′ , app 𝒟′ ℰ′) → (M′ , 𝒟′) ↯ ¬M𝒟 })
  resolveR И (CHECK P A) with resolveL И P
  resolveR И (CHECK P A) | yes (M , 𝒟) = yes (CHECK M A , check 𝒟)
  resolveR И (CHECK P A) | no ¬M𝒟      = no (\ { (CHECK M′ A′ , check 𝒟′) → (M′ , 𝒟′) ↯ ¬M𝒟  })


--------------------------------------------------------------------------------
