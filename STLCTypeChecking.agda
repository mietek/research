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


unique : ∀ {g M A₁ A₂} → {Γ : Types g}
                       → ⊢ Γ ⊦ M ≫ A₁ infers → ⊢ Γ ⊦ M ≫ A₂ infers
                       → A₁ ≡ A₂
unique (var i₁)    (var i₂)    = uniq∋ i₁ i₂
unique (app 𝒟₁ ℰ₁) (app 𝒟₂ ℰ₂) = inj⊃₂ (unique 𝒟₁ 𝒟₂)
unique (chk 𝒟₁)    (chk 𝒟₂)    = refl


mutual
  check : ∀ {g} → (Γ : Types g) (M : Termₗ g) (A : Type)
                → Dec (⊢ Γ ⊦ M ≪ A checks)
  check Γ (LAM M) (ι P)   = no (\ ())
  check Γ (LAM M) (A ⊃ B) with check (Γ , A) M B
  check Γ (LAM M) (A ⊃ B) | yes 𝒟 = yes (lam 𝒟)
  check Γ (LAM M) (A ⊃ B) | no ¬𝒟 = no (\ { (lam 𝒟) → 𝒟 ↯ ¬𝒟 })
  check Γ (INF M) A       with infer Γ M
  check Γ (INF M) A       | yes (A′ , 𝒟′) with A ≟ₜ A′
  check Γ (INF M) A       | yes (.A , 𝒟)  | yes refl = yes (inf 𝒟)
  check Γ (INF M) A       | yes (A′ , 𝒟′) | no A≢A′  = no (\ { (inf 𝒟) → unique 𝒟 𝒟′ ↯ A≢A′ })
  check Γ (INF M) A       | no ¬A𝒟        = no (\ { (inf 𝒟) → (A , 𝒟) ↯ ¬A𝒟 })

  infer : ∀ {g} → (Γ : Types g) (M : Termᵣ g)
                → Dec (Σ Type (\ A → ⊢ Γ ⊦ M ≫ A infers))
  infer Γ (VAR I)   = yes (GET Γ I , var get∋)
  infer Γ (APP M N) with infer Γ M
  infer Γ (APP M N) | yes (ι P     , 𝒟′) = no (\ { (B , app 𝒟 ℰ) → unique 𝒟 𝒟′ ↯ (\ ()) })
  infer Γ (APP M N) | yes (A ⊃ B   , 𝒟)  with check Γ N A
  infer Γ (APP M N) | yes (A ⊃ B   , 𝒟)  | yes ℰ = yes (B , app 𝒟 ℰ)
  infer Γ (APP M N) | yes (A′ ⊃ B′ , 𝒟′) | no ¬ℰ = no (\ { (B , app 𝒟 ℰ) →
                                                             coerce ℰ (_ & (inj⊃₁ (unique 𝒟 𝒟′))) ↯ ¬ℰ })
  infer Γ (APP M N) | no ¬AB𝒟            = no (\ { (B , app {A = A} 𝒟 ℰ) → (A ⊃ B , 𝒟) ↯ ¬AB𝒟 })
  infer Γ (CHK M A) with check Γ M A
  infer Γ (CHK M A) | yes 𝒟 = yes (A , chk 𝒟)
  infer Γ (CHK M A) | no ¬𝒟 = no (\ { (.A , chk 𝒟) → 𝒟 ↯ ¬𝒟 })


--------------------------------------------------------------------------------


testₗ : ∀ {g} → (Γ : Types g) (M : Termₗ g) (A : Type) → ⊢ Γ ⊦ M ≪ A checks → Set
testₗ Γ M A 𝒟 = check Γ M A ≡ yes 𝒟


testᵣ : ∀ {g} → (Γ : Types g) (M : Termᵣ g) (A : Type) → ⊢ Γ ⊦ M ≫ A infers → Set
testᵣ Γ M A 𝒟 = infer Γ M ≡ yes (A , 𝒟)


--------------------------------------------------------------------------------


testIₗ : testₗ ∙ (LAM (INF VZᵣ))
                 ("A" ⊃ "A")
                 (lam (inf vzᵣ))
testIₗ = refl


testIᵣ : testᵣ ∙ (CHK (LAM (INF VZᵣ))
                 ("A" ⊃ "A")) ("A" ⊃ "A")
                 (chk (lam (inf vzᵣ)))
testIᵣ = refl


testKₗ : testₗ ∙ (LAM (LAM (INF (WKᵣ VZᵣ))))
                 ("A" ⊃ "B" ⊃ "A")
                 (lam (lam (inf (wkᵣ vzᵣ))))
testKₗ = refl


testSₗ : testₗ ∙ (LAM (LAM (LAM (INF (APP
                 (APP
                   (WKᵣ (WKᵣ VZᵣ))
                   (INF VZᵣ))
                 (INF (APP
                   (WKᵣ VZᵣ)
                   (INF VZᵣ))))))))
                 (("A" ⊃ "B" ⊃ "C") ⊃ ("A" ⊃ "B") ⊃ "A" ⊃ "C")
                 (lam (lam (lam (inf (app
                   (app
                     (wkᵣ (wkᵣ vzᵣ))
                     (inf vzᵣ))
                   (inf (app
                     (wkᵣ vzᵣ)
                     (inf vzᵣ))))))))
testSₗ = refl


--------------------------------------------------------------------------------
