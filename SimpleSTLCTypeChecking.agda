module SimpleSTLCTypeChecking where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import List using (List ; ∙ ; _,_)
open import Vec
open import AllVec
open import STLCTypes
open import SimpleSTLCTerms hiding (WK ; VZ)
open import SimpleSTLCDerivations hiding (wk ; vz)


--------------------------------------------------------------------------------


module STLCScopeCheckingTerms
  where
    mutual
      data TermL : Set
        where
          LAM : TermL → TermL
          INF : TermR → TermL

      data TermR : Set
        where
          VAR : Nat → TermR
          APP : TermR → TermL → TermR
          CHK : Type → TermL → TermR


--------------------------------------------------------------------------------


module STLCTypeCheckingTerms
  where
    mutual
      data TermL : Nat → Set
        where
          LAM : ∀ {g} → TermL (suc g) → TermL g
          INF : ∀ {g} → TermR g → TermL g
     
      data TermR : Nat → Set
        where
          VAR : ∀ {g} → Fin g → TermR g
          APP : ∀ {g} → TermR g → TermL g → TermR g
          CHK : ∀ {g} → Type → TermL g → TermR g
     
     
    --------------------------------------------------------------------------------
     
     
    mutual
      RECOVERL : ∀ {g} → TermL g
                       → Term g
      RECOVERL (LAM M) = LAM (RECOVERL M)
      RECOVERL (INF M) = RECOVERR M
     
      RECOVERR : ∀ {g} → TermR g
                       → Term g
      RECOVERR (VAR I)   = VAR I
      RECOVERR (APP M N) = APP (RECOVERR M) (RECOVERL N)
      RECOVERR (CHK A M) = RECOVERL M
     
     
    --------------------------------------------------------------------------------
     
     
    mutual
      RENL : ∀ {g g′} → g′ ≥ g → TermL g
                      → TermL g′
      RENL e (LAM M) = LAM (RENL (keep e) M)
      RENL e (INF M) = INF (RENR e M)
     
      RENR : ∀ {g g′} → g′ ≥ g → TermR g
                      → TermR g′
      RENR e (VAR I)   = VAR (REN∋ e I)
      RENR e (APP M N) = APP (RENR e M) (RENL e N)
      RENR e (CHK A M) = CHK A (RENL e M)
     
     
    WKR : ∀ {g} → TermR g
                → TermR (suc g)
    WKR M = RENR (drop id) M
     
     
    VZR : ∀ {g} → TermR (suc g)
    VZR = VAR zero


--------------------------------------------------------------------------------


module STLCScopeCheckingDerivations
  where
    open STLCScopeCheckingTerms


    --------------------------------------------------------------------------------


    -- TODO


--------------------------------------------------------------------------------


module STLCTypeCheckingDerivations
  where
    open STLCTypeCheckingTerms
     
     
    --------------------------------------------------------------------------------


    infix 4 _⊦_≪_
    record TypeChecking : Set
      where
        constructor _⊦_≪_
        field
          {g} : Nat
          Γ   : Types g
          M   : TermL g
          A   : Type
     
     
    infix 4 _⊦_≫_
    record TypeInference : Set
      where
        constructor _⊦_≫_
        field
          {g} : Nat
          Γ   : Types g
          M   : TermR g
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
                          → ⊢ᵣ Γ ⊦ CHK A M ≫ A


    --------------------------------------------------------------------------------
     
     
    mutual
      recoverL : ∀ {g M A} → {Γ : Types g}
                           → ⊢ₗ Γ ⊦ M ≪ A
                           → ⊢ Γ ⊦ RECOVERL M ⦂ A
      recoverL (lam 𝒟) = lam (recoverL 𝒟)
      recoverL (inf 𝒟) = recoverR 𝒟
     
      recoverR : ∀ {g M A} → {Γ : Types g}
                           → ⊢ᵣ Γ ⊦ M ≫ A
                           → ⊢ Γ ⊦ RECOVERR M ⦂ A
      recoverR (var i)   = var i
      recoverR (app 𝒟 ℰ) = app (recoverR 𝒟) (recoverL ℰ)
      recoverR (chk 𝒟)   = recoverL 𝒟
     
     
    --------------------------------------------------------------------------------
     
     
    mutual
      renL : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                            → Γ′ ⊇⟨ e ⟩ Γ → ⊢ₗ Γ ⊦ M ≪ A
                            → ⊢ₗ Γ′ ⊦ RENL e M ≪ A 
      renL η (lam 𝒟) = lam (renL (keep η) 𝒟)
      renL η (inf 𝒟) = inf (renR η 𝒟)
     
      renR : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                            → Γ′ ⊇⟨ e ⟩ Γ → ⊢ᵣ Γ ⊦ M ≫ A
                            → ⊢ᵣ Γ′ ⊦ RENR e M ≫ A 
      renR η (var i)   = var (ren∋ η i)
      renR η (app 𝒟 ℰ) = app (renR η 𝒟) (renL η ℰ)
      renR η (chk 𝒟)   = chk (renL η 𝒟)
     
     
    wkR : ∀ {B g M A} → {Γ : Types g}
                      → ⊢ᵣ Γ ⊦ M ≫ A
                      → ⊢ᵣ Γ , B ⊦ WKR M ≫ A 
    wkR 𝒟 = renR (drop id⊇) 𝒟
     
     
    vzR : ∀ {A g} → {Γ : Types g}
                  → ⊢ᵣ Γ , A ⊦ VZR ≫ A
    vzR = var zero


--------------------------------------------------------------------------------


module STLCTypeChecking
  where
    open STLCTypeCheckingTerms renaming (WKR to WK ; VZR to VZ)
    open STLCTypeCheckingDerivations renaming (wkR to wk ; vzR to vz)
     
     
    --------------------------------------------------------------------------------
     
    Errors : Set
    Errors = List String
     
     
    mutual
      check : ∀ {g} → (Γ : Types g) (M : TermL g) (A : Type)
                    → Errors ⊎ ⊢ₗ Γ ⊦ M ≪ A
      check Γ (LAM M) BASE    = inj₁ (∙ , "type of LAM M can't be BASE")
      check Γ (LAM M) (A ⊃ B) = for⊎ (check (Γ , A) M B)
                                  (_, "when checking type of LAM M")
                                  lam
      check Γ (INF M) A       = elim⊎ (infer Γ M)
                                  (\ ε → inj₁ (ε , "when checking type of INF M"))
                                  (\ { (A′ , 𝒟) → case A ≟ A′ of
                                                     (\ { (yes refl) → inj₂ (inf 𝒟)
                                                        ; (no A≢A′)  → inj₁ (∙ , "type of INF M doesn't match inferred type")
                                                        })
                                     })
     
      infer : ∀ {g} → (Γ : Types g) (M : TermR g)
                    → Errors ⊎ Σ Type (\ A → ⊢ᵣ Γ ⊦ M ≫ A) 
      infer Γ (VAR I)   = inj₂ (GET Γ I , var get∋)
      infer Γ (APP M N) = elim⊎ (infer Γ M)
                            (\ ε → inj₁ (ε , "when inferring type of M in APP M N"))
                            (λ { (BASE  , 𝒟) → inj₁ (∙ , "type of M in APP M N can't be BASE")
                               ; (A ⊃ B , 𝒟) → for⊎ (check Γ N A)
                                                  (_, "when checking type of N in APP M N")
                                                  (\ ℰ → B , app 𝒟 ℰ)
                               })
      infer Γ (CHK A M) = for⊎ (check Γ M A)
                            (_, "when inferring type of CHK A M")
                            (\ 𝒟 → A , chk 𝒟)
     
     
    --------------------------------------------------------------------------------

 
    testL : (𝒥 : TypeChecking) → ⊢ₗ 𝒥 → Set
    testL (Γ ⊦ M ≪ A) 𝒟 = check Γ M A ≡ inj₂ 𝒟
    
    
    testR : (𝒥 : TypeInference) → ⊢ᵣ 𝒥 → Set
    testR (Γ ⊦ M ≫ A) 𝒟 = infer Γ M ≡ inj₂ (A , 𝒟)
    
    
    --------------------------------------------------------------------------------
    
    
    testL-combI : testL (∙ ⊦ LAM (INF VZ) ≪ BASE ⊃ BASE)
                        (lam (inf vz))
    testL-combI = refl
    
    
    testR-combI : testR (∙ ⊦ CHK (BASE ⊃ BASE) (LAM (INF VZ)) ≫ BASE ⊃ BASE)
                        (chk (lam (inf vz)))
    testR-combI = refl
    
    
    testL-combK : testL (∙ ⊦ LAM (LAM (INF (WK VZ))) ≪ BASE ⊃ BASE ⊃ BASE)
                        (lam (lam (inf (wk vz))))
    testL-combK = refl
    
    
    testL-combS : testL (∙ ⊦ LAM (LAM (LAM (INF (APP
                               (APP
                                 (WK (WK VZ))
                                 (INF VZ))
                               (INF (APP
                                 (WK VZ)
                                 (INF VZ)))))))
                           ≪ (BASE ⊃ BASE ⊃ BASE) ⊃ (BASE ⊃ BASE) ⊃ BASE ⊃ BASE)
                        (lam (lam (lam (inf (app
                          (app
                            (wk (wk vz))
                            (inf vz))
                          (inf (app
                            (wk vz)
                            (inf vz))))))))
    testL-combS = refl


--------------------------------------------------------------------------------

