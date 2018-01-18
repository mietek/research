module SimpleSTLCScopeChecking where

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


data RawTerm : Set
  where
    VAR   : Name → RawTerm
    LAM   : Name → RawTerm → RawTerm
    APP   : RawTerm → RawTerm → RawTerm
    CHECK : RawTerm → Type → RawTerm


data Term : Nat → Set
  where
    VAR   : ∀ {g} → Fin g → Term g
    LAM   : ∀ {g} → Term (suc g) → Term g
    APP   : ∀ {g} → Term g → Term g → Term g
    CHECK : ∀ {g} → Term g → Type → Term g


--------------------------------------------------------------------------------


data ∴_⊢_≈_ : ∀ {g} → Names g → RawTerm → Term g → Set
  where
    vz : ∀ {x g} → {И : Names g}
                 → ∴ И , x ⊢ VAR x ≈ VAR zero

    wk : ∀ {x y g I} → {И : Names g}
                     → x ≢ y → ∴ И ⊢ VAR x ≈ VAR I
                     → ∴ И , y ⊢ VAR x ≈ VAR (suc I)

    lam : ∀ {x g P M} → {И : Names g}
                      → ∴ И , x ⊢ P ≈ M
                      → ∴ И ⊢ LAM x P ≈ LAM M

    app : ∀ {g P Q M N} → {И : Names g}
                        → ∴ И ⊢ P ≈ M → ∴ И ⊢ Q ≈ N
                        → ∴ И ⊢ APP P Q ≈ APP M N

    check : ∀ {A g P M} → {И : Names g}
                        → ∴ И ⊢ P ≈ M
                        → ∴ И ⊢ CHECK P A ≈ CHECK M A


--------------------------------------------------------------------------------


injvzwk : ∀ {g x y M} → {И : Names g}
                      → ∴ И , y ⊢ VAR x ≈ M
                      → x ≡ y ⊎ Σ (Term g) (\ M′ → ∴ И ⊢ VAR x ≈ M′)
injvzwk vz       = inj₁ refl
injvzwk (wk p 𝒟) = inj₂ (VAR _ , 𝒟)


find : ∀ {g} → (И : Names g) (x : Name)
             → Dec (Σ (Term g) (\ M → ∴ И ⊢ VAR x ≈ M))
find ∙       x  = no (\ ())
find (И , y) x  with x ≟ₛ y
find (И , x) .x | yes refl = yes (VAR zero , vz)
find (И , y) x  | no x≢y   with find И x
find (И , y) x  | no x≢y   | yes (VAR I , 𝒟)      = yes (VAR (suc I) , wk x≢y 𝒟)
find (И , y) x  | no x≢y   | yes (LAM M , ())
find (И , y) x  | no x≢y   | yes (APP M N , ())
find (И , y) x  | no x≢y   | yes (CHECK M A , ())
find (И , y) x  | no x≢y   | no ¬M𝒟               = no (\ { (M′ , 𝒟′) → case injvzwk 𝒟′ of
                                                         (\ { (inj₁ refl) → refl ↯ x≢y
                                                            ; (inj₂ M𝒟) → M𝒟 ↯ ¬M𝒟
                                                            }) })


resolve : ∀ {g} → (И : Names g) (P : RawTerm)
                → Dec (Σ (Term g) (\ M → ∴ И ⊢ P ≈ M))
resolve И (VAR x)     = find И x
resolve И (LAM x P)   with resolve (И , x) P
resolve И (LAM x P)   | yes (M , 𝒟) = yes (LAM M , lam 𝒟)
resolve И (LAM x P)   | no ¬M𝒟      = no (\ { (LAM M′ , lam 𝒟′) → (M′ , 𝒟′) ↯ ¬M𝒟 })
resolve И (APP P Q)   with resolve И P | resolve И Q
resolve И (APP P Q)   | yes (M , 𝒟) | yes (N , ℰ) = yes (APP M N , app 𝒟 ℰ)
resolve И (APP P Q)   | yes (M , 𝒟) | no ¬Nℰ      = no (\ { (APP M′ N′ , app 𝒟′ ℰ′) → (N′ , ℰ′) ↯ ¬Nℰ })
resolve И (APP P Q)   | no ¬M𝒟      | _           = no (\ { (APP M′ N′ , app 𝒟′ ℰ′) → (M′ , 𝒟′) ↯ ¬M𝒟 })
resolve И (CHECK P A) with resolve И P
resolve И (CHECK P A) | yes (M , 𝒟) = yes (CHECK M A , check 𝒟)
resolve И (CHECK P A) | no ¬M𝒟      = no (\ { (CHECK M′ A′ , check 𝒟′) → (M′ , 𝒟′) ↯ ¬M𝒟  })


--------------------------------------------------------------------------------
