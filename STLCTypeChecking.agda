module STLCTypeChecking where

open import Prelude
open import Category
open import Fin
open import FinLemmas
open import Vec
open import AllVec
open import STLCTypes
open import STLCTerms
open import STLCDerivations
open import STLCBidirectionalTermsForTypeChecking
open import STLCBidirectionalDerivationsForTypeChecking


--------------------------------------------------------------------------------


uniqᵣ : ∀ {g M A₁ A₂} → {Γ : Types g}
                      → ⊢ᵣ Γ ⊦ M ≫ A₁ → ⊢ᵣ Γ ⊦ M ≫ A₂
                      → A₁ ≡ A₂
uniqᵣ (var i₁)    (var i₂)    = uniq∋ i₁ i₂
uniqᵣ (app 𝒟₁ ℰ₁) (app 𝒟₂ ℰ₂) = inj⊃₂ (uniqᵣ 𝒟₁ 𝒟₂)
uniqᵣ (chk 𝒟₁)    (chk 𝒟₂)    = refl


mutual
  check : ∀ {g} → (Γ : Types g) (M : Termₗ g) (A : Type)
                → Dec (⊢ₗ Γ ⊦ M ≪ A)
  check Γ (LAM M) BASE    = no (\ ())
  check Γ (LAM M) (A ⊃ B) with check (Γ , A) M B
  check Γ (LAM M) (A ⊃ B) | yes 𝒟 = yes (lam 𝒟)
  check Γ (LAM M) (A ⊃ B) | no ¬𝒟 = no (\ { (lam 𝒟) → 𝒟 ↯ ¬𝒟 })
  check Γ (INF M) A       with infer Γ M
  check Γ (INF M) A       | yes (A′ , 𝒟′) with A ≟ₜ A′
  check Γ (INF M) A       | yes (.A , 𝒟)  | yes refl = yes (inf 𝒟)
  check Γ (INF M) A       | yes (A′ , 𝒟′) | no A≢A′  = no (\ { (inf 𝒟) → uniqᵣ 𝒟 𝒟′ ↯ A≢A′ })
  check Γ (INF M) A       | no ¬A𝒟        = no (\ { (inf 𝒟) → (A , 𝒟) ↯ ¬A𝒟 })

  infer : ∀ {g} → (Γ : Types g) (M : Termᵣ g)
                → Dec (Σ Type (\ A → ⊢ᵣ Γ ⊦ M ≫ A))
  infer Γ (VAR I)   = yes (GET Γ I , var get∋)
  infer Γ (APP M N) with infer Γ M
  infer Γ (APP M N) | yes (BASE    , 𝒟′) = no (\ { (B , app 𝒟 ℰ) → uniqᵣ 𝒟 𝒟′ ↯ (\ ()) })
  infer Γ (APP M N) | yes (A ⊃ B   , 𝒟)  with check Γ N A
  infer Γ (APP M N) | yes (A ⊃ B   , 𝒟)  | yes ℰ = yes (B , app 𝒟 ℰ)
  infer Γ (APP M N) | yes (A′ ⊃ B′ , 𝒟′) | no ¬ℰ = no (\ { (B , app 𝒟 ℰ) →
                                                             coerce ℰ (_ & (inj⊃₁ (uniqᵣ 𝒟 𝒟′))) ↯ ¬ℰ })
  infer Γ (APP M N) | no ¬AB𝒟            = no (\ { (B , app {A = A} 𝒟 ℰ) → (A ⊃ B , 𝒟) ↯ ¬AB𝒟 })
  infer Γ (CHK M A) with check Γ M A
  infer Γ (CHK M A) | yes 𝒟 = yes (A , chk 𝒟)
  infer Γ (CHK M A) | no ¬𝒟 = no (\ { (.A , chk 𝒟) → 𝒟 ↯ ¬𝒟 })


--------------------------------------------------------------------------------


testₗ : (𝒥 : TypeChecking) → ⊢ₗ 𝒥 → Set
testₗ (Γ ⊦ M ≪ A) 𝒟 = check Γ M A ≡ yes 𝒟


testᵣ : (𝒥 : TypeInference) → ⊢ᵣ 𝒥 → Set
testᵣ (Γ ⊦ M ≫ A) 𝒟 = infer Γ M ≡ yes (A , 𝒟)


--------------------------------------------------------------------------------


testIₗ : testₗ (∙ ⊦ LAM (INF VZᵣ) ≪ BASE ⊃ BASE)
               (lam (inf vzᵣ))
testIₗ = refl


testIᵣ : testᵣ (∙ ⊦ CHK (LAM (INF VZᵣ)) (BASE ⊃ BASE) ≫ BASE ⊃ BASE)
               (chk (lam (inf vzᵣ)))
testIᵣ = refl


testKₗ : testₗ (∙ ⊦ LAM (LAM (INF (WKᵣ VZᵣ))) ≪ BASE ⊃ BASE ⊃ BASE)
               (lam (lam (inf (wkᵣ vzᵣ))))
testKₗ = refl


testSₗ : testₗ (∙ ⊦ LAM (LAM (LAM (INF (APP
                      (APP
                        (WKᵣ (WKᵣ VZᵣ))
                        (INF VZᵣ))
                      (INF (APP
                        (WKᵣ VZᵣ)
                        (INF VZᵣ)))))))
                  ≪ (BASE ⊃ BASE ⊃ BASE) ⊃ (BASE ⊃ BASE) ⊃ BASE ⊃ BASE)
               (lam (lam (lam (inf (app
                 (app
                   (wkᵣ (wkᵣ vzᵣ))
                   (inf vzᵣ))
                 (inf (app
                   (wkᵣ vzᵣ)
                   (inf vzᵣ))))))))
testSₗ = refl


--------------------------------------------------------------------------------
