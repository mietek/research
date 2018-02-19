module SequentCalculusDraft2b where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import FullIPLPropositions
open import FullIPLDerivations hiding (cut)
open import SequentCalculusDrafta


--------------------------------------------------------------------------------


-- Sequent calculus

infix 3 _⟹_
data _⟹_ : List Prop → Prop → Set
  where
    ⊃R : ∀ {A B Γ} → Γ , A ⟹ B
                   → Γ ⟹ A ⊃ B

    ∧R : ∀ {A B Γ} → Γ ⟹ A → Γ ⟹ B
                   → Γ ⟹ A ∧ B

    𝟏R : ∀ {Γ} → Γ ⟹ 𝟏

    ∨R₁ : ∀ {A B Γ} → Γ ⟹ A
                    → Γ ⟹ A ∨ B

    ∨R₂ : ∀ {A B Γ} → Γ ⟹ B
                    → Γ ⟹ A ∨ B

    vzₛ : ∀ {A Γ} → Γ , A ⟹ A

    wkₛ : ∀ {A B Γ} → Γ ⟹ B
                    → Γ , A ⟹ B

    exₛ : ∀ {Γ A B C} → Γ , A , B ⟹ C
                      → Γ , B , A ⟹ C

    ctₛ : ∀ {Γ A B} → Γ , A , A ⟹ B
                    → Γ , A ⟹ B

    ⊃L : ∀ {A B C Γ} → Γ , A ⊃ B ⟹ A → Γ , A ⊃ B , B ⟹ C
                     → Γ , A ⊃ B ⟹ C

    ∧L₁ : ∀ {A B C Γ} → Γ , A ∧ B , A ⟹ C
                      → Γ , A ∧ B ⟹ C

    ∧L₂ : ∀ {A B C Γ} → Γ , A ∧ B , B ⟹ C
                      → Γ , A ∧ B ⟹ C

    𝟎L : ∀ {A Γ} → Γ , 𝟎 ⟹ A

    ∨L : ∀ {A B C Γ} → Γ , A ∨ B , A ⟹ C → Γ , A ∨ B , B ⟹ C
                     → Γ , A ∨ B ⟹ C

infix 3 _⟹_all
_⟹_all : List Prop → List Prop → Set
Γ ⟹ Ξ all = All (Γ ⟹_) Ξ


-- Theorem 3.6 (Soundness of sequent calculus with respect to normal deduction)

thm36 : ∀ {Γ A} → Γ ⟹ A
                → Γ ⊢ A normal
thm36 (⊃R 𝒟)   = lam (thm36 𝒟)
thm36 (∧R 𝒟 ℰ) = pair (thm36 𝒟) (thm36 ℰ)
thm36 𝟏R       = unit
thm36 (∨R₁ 𝒟)  = inl (thm36 𝒟)
thm36 (∨R₂ 𝒟)  = inr (thm36 𝒟)
thm36 vzₛ      = vzₙₘ
thm36 (wkₛ 𝒟)  = wkₙₘ (thm36 𝒟)
thm36 (exₛ 𝒟)  = exₙₘ (thm36 𝒟)
thm36 (ctₛ 𝒟)  = ctₙₘ (thm36 𝒟)
thm36 (⊃L 𝒟 ℰ) = cutₙₘ (app vzₙₜ (thm36 𝒟)) (thm36 ℰ)
thm36 (∧L₁ 𝒟)  = cutₙₘ (fst vzₙₜ) (thm36 𝒟)
thm36 (∧L₂ 𝒟)  = cutₙₘ (snd vzₙₜ) (thm36 𝒟)
thm36 𝟎L       = abort vzₙₜ
thm36 (∨L 𝒟 ℰ) = case vzₙₜ (thm36 𝒟) (thm36 ℰ)


-- Corollary ??? (Soundness of sequent calculus with respect to natural deduction)

cor36′ : ∀ {Γ A} → Γ ⟹ A
                 → Γ ⊢ A true
cor36′ 𝒟 = thm31ₙₘ (thm36 𝒟)


varₛ : ∀ {A Γ} → Γ ∋ A
               → Γ ⟹ A
varₛ zero    = vzₛ
varₛ (suc i) = wkₛ (varₛ i)

wksₛ : ∀ {A Γ Ξ} → Γ ⟹ Ξ all
                 → Γ , A ⟹ Ξ all
wksₛ ξ = maps wkₛ ξ

liftsₛ : ∀ {A Γ Ξ} → Γ ⟹ Ξ all
                   → Γ , A ⟹ Ξ , A all
liftsₛ ξ = wksₛ ξ , vzₛ

idsₛ : ∀ {Γ} → Γ ⟹ Γ all
idsₛ {∙}     = ∙
idsₛ {Γ , A} = liftsₛ idsₛ


-- Lemma 3.7 (Structural properties of sequent calculus)

subₛ : ∀ {Γ Ξ A} → Γ ⟹ Ξ all → Ξ ⟹ A
                 → Γ ⟹ A
subₛ ξ           (⊃R 𝒟)   = ⊃R (subₛ (liftsₛ ξ) 𝒟)
subₛ ξ           (∧R 𝒟 ℰ) = ∧R (subₛ ξ 𝒟) (subₛ ξ ℰ)
subₛ ξ           𝟏R       = 𝟏R
subₛ ξ           (∨R₁ 𝒟)  = ∨R₁ (subₛ ξ 𝒟)
subₛ ξ           (∨R₂ 𝒟)  = ∨R₂ (subₛ ξ 𝒟)
subₛ (ξ , 𝒞)     vzₛ      = 𝒞
subₛ (ξ , 𝒞)     (wkₛ 𝒟)  = subₛ ξ 𝒟
subₛ (ξ , ℬ , 𝒞) (exₛ 𝒟)  = subₛ (ξ , 𝒞 , ℬ) 𝒟
subₛ (ξ , 𝒞)     (ctₛ 𝒟)  = subₛ (ξ , 𝒞 , 𝒞) 𝒟
subₛ (ξ , 𝒞)     (⊃L 𝒟 ℰ) = {!!}
subₛ (ξ , 𝒞)     (∧L₁ 𝒟)  = {!!}
subₛ (ξ , 𝒞)     (∧L₂ 𝒟)  = {!!}
subₛ (ξ , 𝒞)     𝟎L       = {!!}
subₛ (ξ , 𝒞)     (∨L 𝒟 ℰ) = {!!}

renₛ : ∀ {Γ Γ′ A} → Γ′ ⊒ Γ → Γ ⟹ A
                  → Γ′ ⟹ A
renₛ η (⊃R 𝒟)   = ⊃R (renₛ (keep⊒ η) 𝒟)
renₛ η (∧R 𝒟 ℰ) = ∧R (renₛ η 𝒟) (renₛ η ℰ)
renₛ η 𝟏R       = 𝟏R
renₛ η (∨R₁ 𝒟)  = ∨R₁ (renₛ η 𝒟)
renₛ η (∨R₂ 𝒟)  = ∨R₂ (renₛ η 𝒟)
renₛ η vzₛ      = varₛ (η zero)
renₛ η (wkₛ 𝒟)  = renₛ (η ∘ suc) 𝒟
renₛ η (exₛ 𝒟)  = renₛ (η ∘ ex⊒) 𝒟
renₛ η (ctₛ 𝒟)  = renₛ (η ∘ ct⊒) 𝒟
renₛ η (⊃L 𝒟 ℰ) = {!!}
renₛ η (∧L₁ 𝒟)  = {!!}
renₛ η (∧L₂ 𝒟)  = {!!}
renₛ η 𝟎L       = {!!}
renₛ η (∨L 𝒟 ℰ) = {!!}


-- Theorem 3.8 (Completeness of sequent calculus with respect to normal/neutral deductions)

mutual
  thm38ₙₘ : ∀ {Γ A} → Γ ⊢ A normal
                    → Γ ⟹ A
  thm38ₙₘ (lam 𝒟)      = ⊃R (thm38ₙₘ 𝒟)
  thm38ₙₘ (pair 𝒟 ℰ)   = ∧R (thm38ₙₘ 𝒟) (thm38ₙₘ ℰ)
  thm38ₙₘ unit         = 𝟏R
  thm38ₙₘ (abort 𝒟)    = thm38ₙₜ 𝒟 𝟎L
  thm38ₙₘ (inl 𝒟)      = ∨R₁ (thm38ₙₘ 𝒟)
  thm38ₙₘ (inr 𝒟)      = ∨R₂ (thm38ₙₘ 𝒟)
  thm38ₙₘ (case 𝒟 ℰ ℱ) = thm38ₙₜ 𝒟 (∨L (exₛ (wkₛ (thm38ₙₘ ℰ))) (exₛ (wkₛ (thm38ₙₘ ℱ))))
  thm38ₙₘ (ent 𝒟)      = thm38ₙₜ 𝒟 vzₛ

  thm38ₙₜ : ∀ {Γ A B} → Γ ⊢ A neutral → Γ , A ⟹ B
                      → Γ ⟹ B
  thm38ₙₜ (var i)     ℰ = renₛ (genct⊒ i) ℰ
  thm38ₙₜ (app 𝒟₁ 𝒟₂) ℰ = thm38ₙₜ 𝒟₁ (⊃L (wkₛ (thm38ₙₘ 𝒟₂)) (exₛ (wkₛ ℰ)))
  thm38ₙₜ (fst 𝒟)     ℰ = thm38ₙₜ 𝒟 (∧L₁ (exₛ (wkₛ ℰ)))
  thm38ₙₜ (snd 𝒟)     ℰ = thm38ₙₜ 𝒟 (∧L₂ (exₛ (wkₛ ℰ)))


--------------------------------------------------------------------------------
