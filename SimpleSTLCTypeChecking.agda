module SimpleSTLCTypeChecking where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec
open import AllVec
open import STLCTypes
open import STLCTypeCheckingTerms
open import STLCTypeCheckingDerivations
open import SimpleSTLCTerms
open import SimpleSTLCDerivations


--------------------------------------------------------------------------------


mutual
  checkType : ∀ {g} → (Γ : Types g) (M : TermL g) (A : Type)
                    → Dec (⊢ₗ Γ ⊦ M ≪ A)
  checkType Γ (LAM M)   BASE    = no (\ ())
  checkType Γ (LAM M)   (A ⊃ B) with checkType (Γ , A) M B
  checkType Γ (LAM M)   (A ⊃ B) | yes 𝒟 = yes (lam 𝒟)
  checkType Γ (LAM M)   (A ⊃ B) | no ¬𝒟 = no (\ { (lam 𝒟) → 𝒟 ↯ ¬𝒟 })
  checkType Γ (INFER M) A       with inferType Γ M
  checkType Γ (INFER M) A       | yes (A′ , 𝒟′) with A ≟ₜ A′
  checkType Γ (INFER M) A       | yes (.A , 𝒟)  | yes refl = yes (infer 𝒟)
  checkType Γ (INFER M) A       | yes (A′ , 𝒟′) | no A≢A′  = no (\ { (infer 𝒟) → uniqR 𝒟 𝒟′ ↯ A≢A′ })
  checkType Γ (INFER M) A       | no ¬A𝒟        = no (\ { (infer 𝒟) → (A , 𝒟) ↯ ¬A𝒟 })

  inferType : ∀ {g} → (Γ : Types g) (M : TermR g)
                    → Dec (Σ Type (\ A → ⊢ᵣ Γ ⊦ M ≫ A))
  inferType Γ (VAR I)     = yes (GET Γ I , var get∋)
  inferType Γ (APP M N)   with inferType Γ M
  inferType Γ (APP M N)   | yes (BASE    , 𝒟′) = no (\ { (B , app 𝒟 ℰ) → uniqR 𝒟 𝒟′ ↯ (\ ()) })
  inferType Γ (APP M N)   | yes (A ⊃ B   , 𝒟)  with checkType Γ N A
  inferType Γ (APP M N)   | yes (A ⊃ B   , 𝒟)  | yes ℰ = yes (B , app 𝒟 ℰ)
  inferType Γ (APP M N)   | yes (A′ ⊃ B′ , 𝒟′) | no ¬ℰ = no (\ { (B , app 𝒟 ℰ) →
                                                           coerce ℰ (_ & (inj⊃₁ (uniqR 𝒟 𝒟′))) ↯ ¬ℰ })
  inferType Γ (APP M N)   | no ¬AB𝒟            = no (\ { (B , app {A = A} 𝒟 ℰ) → (A ⊃ B , 𝒟) ↯ ¬AB𝒟 })
  inferType Γ (CHECK M A) with checkType Γ M A
  inferType Γ (CHECK M A) | yes 𝒟 = yes (A , check 𝒟)
  inferType Γ (CHECK M A) | no ¬𝒟 = no (\ { (.A , check 𝒟) → 𝒟 ↯ ¬𝒟 })


--------------------------------------------------------------------------------


-- Errors : Set
-- Errors = List String


-- mutual
--   check : ∀ {g} → (Γ : Types g) (M : TermL g) (A : Type)
--                 → Errors ⊎ ⊢ₗ Γ ⊦ M ≪ A
--   check Γ (LAM M) BASE    = inj₁ (∙ , "type of LAM M can't be BASE")
--   check Γ (LAM M) (A ⊃ B) = for⊎ (check (Γ , A) M B)
--                               (_, "when checking type of LAM M")
--                               lam
--   check Γ (INF M) A       = elim⊎ (infer Γ M)
--                               (\ ε → inj₁ (ε , "when checking type of INF M"))
--                               (\ { (A′ , 𝒟) →
--                                      case A ≟ A′ of
--                                        (\ { (yes refl) → inj₂ (inf 𝒟)
--                                           ; (no A≢A′) → inj₁ (∙ , "type mismatch in INF M")
--                                           })
--                                  })

--   infer : ∀ {g} → (Γ : Types g) (M : TermR g)
--                 → Errors ⊎ Σ Type (\ A → ⊢ᵣ Γ ⊦ M ≫ A)
--   infer Γ (VAR I)   = inj₂ (GET Γ I , var get∋)
--   infer Γ (APP M N) = elim⊎ (infer Γ M)
--                         (\ ε → inj₁ (ε , "when inferring type of M in APP M N"))
--                         (\ { (BASE  , 𝒟) → inj₁ (∙ , "type of M in APP M N can't be BASE")
--                            ; (A ⊃ B , 𝒟) →
--                                for⊎ (check Γ N A)
--                                  (_, "when checking type of N in APP M N")
--                                  (\ ℰ → B , app 𝒟 ℰ)
--                            })
--   infer Γ (CHK A M) = for⊎ (check Γ M A)
--                         (_, "when inferring type of CHK A M")
--                         (\ 𝒟 → A , chk 𝒟)


-- --------------------------------------------------------------------------------


-- testL : (𝒥 : TypeChecking) → ⊢ₗ 𝒥 → Set
-- testL (Γ ⊦ M ≪ A) 𝒟 = check Γ M A ≡ inj₂ 𝒟


-- testR : (𝒥 : TypeInference) → ⊢ᵣ 𝒥 → Set
-- testR (Γ ⊦ M ≫ A) 𝒟 = infer Γ M ≡ inj₂ (A , 𝒟)


-- --------------------------------------------------------------------------------


-- testL-combI : testL (∙ ⊦ LAM (INF VZ) ≪ BASE ⊃ BASE)
--                     (lam (inf vz))
-- testL-combI = refl


-- testR-combI : testR (∙ ⊦ CHK (LAM (INF VZ)) (BASE ⊃ BASE) ≫ BASE ⊃ BASE)
--                     (chk (lam (inf vz)))
-- testR-combI = refl


-- testL-combK : testL (∙ ⊦ LAM (LAM (INF (WK VZ))) ≪ BASE ⊃ BASE ⊃ BASE)
--                     (lam (lam (inf (wk vz))))
-- testL-combK = refl


-- testL-combS : testL (∙ ⊦ LAM (LAM (LAM (INF (APP
--                            (APP
--                              (WK (WK VZ))
--                              (INF VZ))
--                            (INF (APP
--                              (WK VZ)
--                              (INF VZ)))))))
--                        ≪ (BASE ⊃ BASE ⊃ BASE) ⊃ (BASE ⊃ BASE) ⊃ BASE ⊃ BASE)
--                     (lam (lam (lam (inf (app
--                       (app
--                         (wk (wk vz))
--                         (inf vz))
--                       (inf (app
--                         (wk vz)
--                         (inf vz))))))))
-- testL-combS = refl


-- --------------------------------------------------------------------------------
