{-# OPTIONS --allow-unsolved-metas #-}

module A201801.SequentCalculusDraft2a where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.FullIPLPropositions
open import A201801.FullIPLDerivations hiding (cut)
open import A201801.SequentCalculusDraft


--------------------------------------------------------------------------------


-- Sequent calculus

infix 3 _⟹_
data _⟹_ : List Form → Form → Set
  where
    ⊃R : ∀ {A B Γ} → Γ , A ⟹ B
                   → Γ ⟹ A ⊃ B

    ∧R : ∀ {A B Γ} → Γ ⟹ A → Γ ⟹ B
                   → Γ ⟹ A ∧ B

    𝟙R : ∀ {Γ} → Γ ⟹ 𝟙

    ∨R₁ : ∀ {A B Γ} → Γ ⟹ A
                    → Γ ⟹ A ∨ B

    ∨R₂ : ∀ {A B Γ} → Γ ⟹ B
                    → Γ ⟹ A ∨ B

    var : ∀ {A Γ} → Γ ∋ A
                  → Γ ⟹ A

    ⊃L : ∀ {A B C Γ} → Γ ∋ A ⊃ B → Γ ⟹ A → Γ , B ⟹ C
                     → Γ ⟹ C

    ∧L₁ : ∀ {A B C Γ} → Γ ∋ A ∧ B → Γ , A ⟹ C
                      → Γ ⟹ C

    ∧L₂ : ∀ {A B C Γ} → Γ ∋ A ∧ B → Γ , B ⟹ C
                      → Γ ⟹ C

    𝟘L : ∀ {A Γ} → Γ ∋ 𝟘
                 → Γ ⟹ A

    ∨L : ∀ {A B C Γ} → Γ ∋ A ∨ B → Γ , A ⟹ C → Γ , B ⟹ C
                     → Γ ⟹ C

infix 3 _⟹_all
_⟹_all : List Form → List Form → Set
Γ ⟹ Ξ all = All (Γ ⟹_) Ξ


-- Theorem 3.6 (Soundness of sequent calculus with respect to normal deduction)

thm36 : ∀ {Γ A} → Γ ⟹ A
                → Γ ⊢ A normal
thm36 (⊃R 𝒟)     = lam (thm36 𝒟)
thm36 (∧R 𝒟 ℰ)   = pair (thm36 𝒟) (thm36 ℰ)
thm36 𝟙R         = unit
thm36 (∨R₁ 𝒟)    = inl (thm36 𝒟)
thm36 (∨R₂ 𝒟)    = inr (thm36 𝒟)
thm36 (var i)    = ent (var i)
thm36 (⊃L i 𝒟 ℰ) = cutₙₘ (app (var i) (thm36 𝒟)) (thm36 ℰ)
thm36 (∧L₁ i 𝒟)  = cutₙₘ (fst (var i)) (thm36 𝒟)
thm36 (∧L₂ i 𝒟)  = cutₙₘ (snd (var i)) (thm36 𝒟)
thm36 (𝟘L i)     = abort (var i)
thm36 (∨L i 𝒟 ℰ) = case (var i) (thm36 𝒟) (thm36 ℰ)


-- Corollary ??? (Soundness of sequent calculus with respect to natural deduction)

cor36′ : ∀ {Γ A} → Γ ⟹ A
                 → Γ ⊢ A true
cor36′ 𝒟 = thm31ₙₘ (thm36 𝒟)


-- Lemma 3.7 (Structural properties of sequent calculus)

vzₛ : ∀ {Γ A} → Γ , A ⟹ A
vzₛ = var zero

renₛ : ∀ {Γ Γ′ A} → Γ′ ⊒ Γ → Γ ⟹ A
                  → Γ′ ⟹ A
renₛ η (⊃R 𝒟)     = ⊃R (renₛ (keep⊒ η) 𝒟)
renₛ η (∧R 𝒟 ℰ)   = ∧R (renₛ η 𝒟) (renₛ η ℰ)
renₛ η 𝟙R         = 𝟙R
renₛ η (∨R₁ 𝒟)    = ∨R₁ (renₛ η 𝒟)
renₛ η (∨R₂ 𝒟)    = ∨R₂ (renₛ η 𝒟)
renₛ η (var i)    = var (η i)
renₛ η (⊃L i 𝒟 ℰ) = ⊃L (η i) (renₛ η 𝒟) (renₛ (keep⊒ η) ℰ)
renₛ η (∧L₁ i 𝒟)  = ∧L₁ (η i) (renₛ (keep⊒ η) 𝒟)
renₛ η (∧L₂ i 𝒟)  = ∧L₂ (η i) (renₛ (keep⊒ η) 𝒟)
renₛ η (𝟘L i)     = 𝟘L (η i)
renₛ η (∨L i 𝒟 ℰ) = ∨L (η i) (renₛ (keep⊒ η) 𝒟) (renₛ (keep⊒ η) ℰ)

wkₛ : ∀ {B Γ A} → Γ ⟹ A
                → Γ , B ⟹ A
wkₛ 𝒟 = renₛ suc 𝒟

exₛ : ∀ {Γ A B C} → Γ , A , B ⟹ C
                  → Γ , B , A ⟹ C
exₛ 𝒟 = renₛ ex⊒ 𝒟

ctₛ : ∀ {Γ A B} → Γ , A , A ⟹ B
                → Γ , A ⟹ B
ctₛ 𝒟 = renₛ ct⊒ 𝒟

wksₛ : ∀ {A Γ Ξ} → Γ ⟹ Ξ all
                 → Γ , A ⟹ Ξ all
wksₛ ξ = maps wkₛ ξ

liftsₛ : ∀ {A Γ Ξ} → Γ ⟹ Ξ all
                   → Γ , A ⟹ Ξ , A all
liftsₛ ξ = wksₛ ξ , vzₛ

idsₛ : ∀ {Γ} → Γ ⟹ Γ all
idsₛ {∙}     = ∙
idsₛ {Γ , A} = liftsₛ idsₛ


-- Theorem 3.8 (Completeness of sequent calculus with respect to normal/neutral deductions)

mutual
  thm38ₙₘ : ∀ {Γ A} → Γ ⊢ A normal
                    → Γ ⟹ A
  thm38ₙₘ (lam 𝒟)      = ⊃R (thm38ₙₘ 𝒟)
  thm38ₙₘ (pair 𝒟 ℰ)   = ∧R (thm38ₙₘ 𝒟) (thm38ₙₘ ℰ)
  thm38ₙₘ unit         = 𝟙R
  thm38ₙₘ (abort 𝒟)    = thm38ₙₜ 𝒟 (𝟘L zero)
  thm38ₙₘ (inl 𝒟)      = ∨R₁ (thm38ₙₘ 𝒟)
  thm38ₙₘ (inr 𝒟)      = ∨R₂ (thm38ₙₘ 𝒟)
  thm38ₙₘ (case 𝒟 ℰ ℱ) = thm38ₙₜ 𝒟 (∨L zero (exₛ (wkₛ (thm38ₙₘ ℰ))) (exₛ (wkₛ (thm38ₙₘ ℱ))))
  thm38ₙₘ (ent 𝒟)      = thm38ₙₜ 𝒟 vzₛ

  thm38ₙₜ : ∀ {Γ A B} → Γ ⊢ A neutral → Γ , A ⟹ B
                      → Γ ⟹ B
  thm38ₙₜ (var i)     ℰ = renₛ (genct⊒ i) ℰ
  thm38ₙₜ (app 𝒟₁ 𝒟₂) ℰ = thm38ₙₜ 𝒟₁ (⊃L zero (wkₛ (thm38ₙₘ 𝒟₂)) (exₛ (wkₛ ℰ)))
  thm38ₙₜ (fst 𝒟)     ℰ = thm38ₙₜ 𝒟 (∧L₁ zero (exₛ (wkₛ ℰ)))
  thm38ₙₜ (snd 𝒟)     ℰ = thm38ₙₜ 𝒟 (∧L₂ zero (exₛ (wkₛ ℰ)))


--------------------------------------------------------------------------------


-- Sequent calculus with cut

infix 3 _⟹₊_
data _⟹₊_ : List Form → Form → Set
  where
    ⊃R : ∀ {A B Γ} → Γ , A ⟹₊ B
                   → Γ ⟹₊ A ⊃ B

    ∧R : ∀ {A B Γ} → Γ ⟹₊ A → Γ ⟹₊ B
                   → Γ ⟹₊ A ∧ B

    𝟙R : ∀ {Γ} → Γ ⟹₊ 𝟙

    ∨R₁ : ∀ {A B Γ} → Γ ⟹₊ A
                    → Γ ⟹₊ A ∨ B

    ∨R₂ : ∀ {A B Γ} → Γ ⟹₊ B
                    → Γ ⟹₊ A ∨ B

    var : ∀ {A Γ} → Γ ∋ A
                  → Γ ⟹₊ A

    ⊃L : ∀ {A B C Γ} → Γ ∋ A ⊃ B → Γ ⟹₊ A → Γ , B ⟹₊ C
                     → Γ ⟹₊ C

    ∧L₁ : ∀ {A B C Γ} → Γ ∋ A ∧ B → Γ , A ⟹₊ C
                      → Γ ⟹₊ C

    ∧L₂ : ∀ {A B C Γ} → Γ ∋ A ∧ B → Γ , B ⟹₊ C
                      → Γ ⟹₊ C

    𝟘L : ∀ {A Γ} → Γ ∋ 𝟘
                 → Γ ⟹₊ A

    ∨L : ∀ {A B C Γ} → Γ ∋ A ∨ B → Γ , A ⟹₊ C → Γ , B ⟹₊ C
                     → Γ ⟹₊ C

    cut : ∀ {A B Γ} → Γ ⟹₊ A → Γ , A ⟹₊ B
                    → Γ ⟹₊ B

infix 3 _⟹₊_all
_⟹₊_all : List Form → List Form → Set
Γ ⟹₊ Ξ all = All (Γ ⟹₊_) Ξ


-- Theorem 3.9 (Soundness of sequent calculus with cut with respect to annotated normal deduction)

thm39 : ∀ {Γ A} → Γ ⟹₊ A
                → Γ ⊢₊ A normal
thm39 (⊃R 𝒟)     = lam (thm39 𝒟)
thm39 (∧R 𝒟 ℰ)   = pair (thm39 𝒟) (thm39 ℰ)
thm39 𝟙R         = unit
thm39 (∨R₁ 𝒟)    = inl (thm39 𝒟)
thm39 (∨R₂ 𝒟)    = inr (thm39 𝒟)
thm39 (var i)    = ent (var i)
thm39 (⊃L i 𝒟 ℰ) = cutₙₘ₊ (app (var i) (thm39 𝒟)) (thm39 ℰ)
thm39 (∧L₁ i 𝒟)  = cutₙₘ₊ (fst (var i)) (thm39 𝒟)
thm39 (∧L₂ i 𝒟)  = cutₙₘ₊ (snd (var i)) (thm39 𝒟)
thm39 (𝟘L i)     = abort (var i)
thm39 (∨L x 𝒟 ℰ) = case (var x) (thm39 𝒟) (thm39 ℰ)
thm39 (cut 𝒟 ℰ)  = cutₙₘ₊ (enm (thm39 𝒟)) (thm39 ℰ)


-- Lemma ??? (Structural properties of sequent calculus with cut)

vzₛ₊ : ∀ {Γ A} → Γ , A ⟹₊ A
vzₛ₊ = var zero

renₛ₊ : ∀ {Γ Γ′ A} → Γ′ ⊒ Γ → Γ ⟹₊ A
                   → Γ′ ⟹₊ A
renₛ₊ η (⊃R 𝒟)     = ⊃R (renₛ₊ (keep⊒ η) 𝒟)
renₛ₊ η (∧R 𝒟 ℰ)   = ∧R (renₛ₊ η 𝒟) (renₛ₊ η ℰ)
renₛ₊ η 𝟙R         = 𝟙R
renₛ₊ η (∨R₁ 𝒟)    = ∨R₁ (renₛ₊ η 𝒟)
renₛ₊ η (∨R₂ 𝒟)    = ∨R₂ (renₛ₊ η 𝒟)
renₛ₊ η (var i)    = var (η i)
renₛ₊ η (⊃L i 𝒟 ℰ) = ⊃L (η i) (renₛ₊ η 𝒟) (renₛ₊ (keep⊒ η) ℰ)
renₛ₊ η (∧L₁ i 𝒟)  = ∧L₁ (η i) (renₛ₊ (keep⊒ η) 𝒟)
renₛ₊ η (∧L₂ i 𝒟)  = ∧L₂ (η i) (renₛ₊ (keep⊒ η) 𝒟)
renₛ₊ η (𝟘L i)     = 𝟘L (η i)
renₛ₊ η (∨L i 𝒟 ℰ) = ∨L (η i) (renₛ₊ (keep⊒ η) 𝒟) (renₛ₊ (keep⊒ η) ℰ)
renₛ₊ η (cut 𝒟 ℰ)  = cut (renₛ₊ η 𝒟) (renₛ₊ (keep⊒ η) ℰ)

wkₛ₊ : ∀ {B Γ A} → Γ ⟹₊ A
                 → Γ , B ⟹₊ A
wkₛ₊ 𝒟 = renₛ₊ suc 𝒟

exₛ₊ : ∀ {Γ A B C} → Γ , A , B ⟹₊ C
                   → Γ , B , A ⟹₊ C
exₛ₊ 𝒟 = renₛ₊ ex⊒ 𝒟

ctₛ₊ : ∀ {Γ A B} → Γ , A , A ⟹₊ B
                 → Γ , A ⟹₊ B
ctₛ₊ 𝒟 = renₛ₊ ct⊒ 𝒟


-- Theorem 3.10 (Completeness of sequent calculus with cut with respect to annotated normal/neutral deductions)

mutual
  thm310ₙₘ : ∀ {Γ A} → Γ ⊢₊ A normal
                     → Γ ⟹₊ A
  thm310ₙₘ (lam 𝒟)      = ⊃R (thm310ₙₘ 𝒟)
  thm310ₙₘ (pair 𝒟 ℰ)   = ∧R (thm310ₙₘ 𝒟) (thm310ₙₘ ℰ)
  thm310ₙₘ unit         = 𝟙R
  thm310ₙₘ (abort 𝒟)    = thm310ₙₜ 𝒟 (𝟘L zero)
  thm310ₙₘ (inl 𝒟)      = ∨R₁ (thm310ₙₘ 𝒟)
  thm310ₙₘ (inr 𝒟)      = ∨R₂ (thm310ₙₘ 𝒟)
  thm310ₙₘ (case 𝒟 ℰ ℱ) = thm310ₙₜ 𝒟 (∨L zero (exₛ₊ (wkₛ₊ (thm310ₙₘ ℰ))) (exₛ₊ (wkₛ₊ (thm310ₙₘ ℱ))))
  thm310ₙₘ (ent 𝒟)      = thm310ₙₜ 𝒟 vzₛ₊

  thm310ₙₜ : ∀ {Γ A B} → Γ ⊢₊ A neutral → Γ , A ⟹₊ B
                       → Γ ⟹₊ B
  thm310ₙₜ (var i)     ℰ = renₛ₊ (genct⊒ i) ℰ
  thm310ₙₜ (app 𝒟₁ 𝒟₂) ℰ = thm310ₙₜ 𝒟₁ (⊃L zero (wkₛ₊ (thm310ₙₘ 𝒟₂)) (exₛ₊ (wkₛ₊ ℰ)))
  thm310ₙₜ (fst 𝒟)     ℰ = thm310ₙₜ 𝒟 (∧L₁ zero (exₛ₊ (wkₛ₊ ℰ)))
  thm310ₙₜ (snd 𝒟)     ℰ = thm310ₙₜ 𝒟 (∧L₂ zero (exₛ₊ (wkₛ₊ ℰ)))
  thm310ₙₜ (enm 𝒟)     ℰ = cut (thm310ₙₘ 𝒟) ℰ


--------------------------------------------------------------------------------


-- Theorem 3.11 (Admissibility of cut)

-- TODO: Weakening and exchange confuse the termination checker

-- TODO: unfinished
-- -- {-# TERMINATING #-}
-- thm311 : ∀ {Γ A C} → Γ ⟹ A → Γ , A ⟹ C
--                    → Γ ⟹ C

-- -- Case: A is not the principal formula of the last inference in ℰ.
-- -- In this case, we appeal to the induction hypothesis on the
-- -- subderivations of ℰ and directly infer the conclusion from the results.
-- thm311 𝒟 (⊃R ℰ)     = ⊃R (thm311 (wkₛ 𝒟) (exₛ ℰ))
-- thm311 𝒟 (∧R ℰ₁ ℰ₂) = ∧R (thm311 𝒟 ℰ₁) (thm311 𝒟 ℰ₂)
-- thm311 𝒟 𝟙R         = 𝟙R
-- thm311 𝒟 (∨R₁ ℰ)    = ∨R₁ (thm311 𝒟 ℰ)
-- thm311 𝒟 (∨R₂ ℰ)    = ∨R₂ (thm311 𝒟 ℰ)

-- -- Case: ℰ is an initial sequent using the cut formula
-- thm311 𝒟 (var zero) = 𝒟

-- -- Case: ℰ is an initial sequent not using the cut formula
-- thm311 𝒟 (var (suc i)) = var i

-- -- Case: 𝒟 is an initial sequent
-- thm311 (var i) ℰ = renₛ (genct⊒ i) ℰ

-- -- Case: A is not the principal formula of the last inference in 𝒟.
-- -- In that case 𝒟 must end in a left rule and we can appeal to the
-- -- induction hypothesis on one of its premises.
-- thm311 (⊃L i 𝒟₁ 𝒟₂) ℰ = ⊃L i 𝒟₁ (thm311 𝒟₂ (exₛ (wkₛ ℰ)))
-- thm311 (∧L₁ i 𝒟)    ℰ = ∧L₁ i (thm311 𝒟 (exₛ (wkₛ ℰ)))
-- thm311 (∧L₂ i 𝒟)    ℰ = ∧L₂ i (thm311 𝒟 (exₛ (wkₛ ℰ)))
-- thm311 (𝟘L i)       ℰ = 𝟘L i
-- thm311 (∨L i 𝒟₁ 𝒟₂) ℰ = ∨L i (thm311 𝒟₁ (exₛ (wkₛ ℰ))) (thm311 𝒟₂ (exₛ (wkₛ ℰ)))

-- -- Case: A is the principal formula of the final inference in both
-- -- 𝒟 and ℰ.  There are a number of subcases to consider, based on the
-- -- last inference in 𝒟 and ℰ.

-- -- TODO: unfinished
-- -- -- TODO: Termination
-- -- thm311 𝒟 (⊃L (suc i) ℰ₁ ℰ₂) = ⊃L i {!thm311 𝒟 ℰ₁!} {!thm311 (wkₛ 𝒟) (exₛ ℰ₂)!}
-- -- thm311 𝒟 (∧L₁ (suc i) ℰ)    = ∧L₁ i {!thm311 (wkₛ 𝒟) (exₛ ℰ)!}
-- -- thm311 𝒟 (∧L₂ (suc i) ℰ)    = ∧L₂ i {!thm311 (wkₛ 𝒟) (exₛ ℰ)!}
-- -- thm311 𝒟 (𝟘L (suc i))       = 𝟘L i
-- -- thm311 𝒟 (∨L (suc i) ℰ₁ ℰ₂) = ∨L i {!thm311 (wkₛ 𝒟) (exₛ ℰ₁)!} {!thm311 (wkₛ 𝒟) (exₛ ℰ₂)!}
-- --
-- -- -- TODO: ???
-- -- thm311 (⊃R 𝒟)     (⊃L zero ℰ₁ ℰ₂) = {!!}
-- -- thm311 (∧R 𝒟₁ 𝒟₂) (∧L₁ zero ℰ)    = {!!}
-- -- thm311 (∧R 𝒟₁ 𝒟₂) (∧L₂ zero ℰ)    = {!!}
-- -- thm311 (∨R₁ 𝒟)    (∨L zero ℰ₁ ℰ₂) = {!!}
-- -- thm311 (∨R₂ 𝒟)    (∨L zero ℰ₁ ℰ₂) = {!!}


-- --------------------------------------------------------------------------------


-- -- Theorem 3.12 (Cut elimination)

-- thm312 : ∀ {Γ A} → Γ ⟹₊ A
--                  → Γ ⟹ A
-- thm312 (⊃R 𝒟)     = ⊃R (thm312 𝒟)
-- thm312 (∧R 𝒟 ℰ)   = ∧R (thm312 𝒟) (thm312 ℰ)
-- thm312 𝟙R         = 𝟙R
-- thm312 (∨R₁ 𝒟)    = ∨R₁ (thm312 𝒟)
-- thm312 (∨R₂ 𝒟)    = ∨R₂ (thm312 𝒟)
-- thm312 (var i)    = var i
-- thm312 (⊃L i 𝒟 ℰ) = ⊃L i (thm312 𝒟) (thm312 ℰ)
-- thm312 (∧L₁ i 𝒟)  = ∧L₁ i (thm312 𝒟)
-- thm312 (∧L₂ i 𝒟)  = ∧L₂ i (thm312 𝒟)
-- thm312 (𝟘L i)     = 𝟘L i
-- thm312 (∨L i 𝒟 ℰ) = ∨L i (thm312 𝒟) (thm312 ℰ)
-- thm312 (cut 𝒟 ℰ)  = thm311 (thm312 𝒟) (thm312 ℰ)


-- -- Corollary ??? (Completeness of sequent calculus with respect to natural deduction)

-- cor312′ : ∀ {Γ A} → Γ ⊢ A true
--                   → Γ ⟹ A
-- cor312′ 𝒟 = thm312 (thm310ₙₘ (thm33ₙₘ 𝒟))


-- -- Theorem 3.13 (Normalisation of natural deduction)

-- thm313 : ∀ {Γ A} → Γ ⊢ A true
--                  → Γ ⊢ A normal
-- thm313 𝒟 = thm36 (cor312′ 𝒟)


-- -- Corollary 3.14 (Consistency of natural deduction)

-- cor314 : ¬ (∙ ⊢ 𝟘 true)
-- cor314 𝒟 with cor312′ 𝒟
-- cor314 𝒟 | var ()
-- cor314 𝒟 | ⊃L () 𝒟′ ℰ′
-- cor314 𝒟 | ∧L₁ () 𝒟′
-- cor314 𝒟 | ∧L₂ () 𝒟′
-- cor314 𝒟 | 𝟘L ()
-- cor314 𝒟 | ∨L () 𝒟′ ℰ′


-- -- Corollary 3.15 (Disjunction property of natural deduction)

-- -- TODO: Existentials for the existential property! Skulls for the skull throne!

-- cor315ₛ : ∀ {A B} → ∙ ⟹ A ∨ B
--                   → ∙ ⟹ A ⊎ ∙ ⟹ B
-- cor315ₛ 𝒟 with cor312′ (cor36′ 𝒟)
-- cor315ₛ 𝒟 | ∨R₁ 𝒟′      = inj₁ 𝒟′
-- cor315ₛ 𝒟 | ∨R₂ 𝒟′      = inj₂ 𝒟′
-- cor315ₛ 𝒟 | var ()
-- cor315ₛ 𝒟 | ⊃L () 𝒟′ ℰ′
-- cor315ₛ 𝒟 | ∧L₁ () 𝒟′
-- cor315ₛ 𝒟 | ∧L₂ () 𝒟′
-- cor315ₛ 𝒟 | 𝟘L ()
-- cor315ₛ 𝒟 | ∨L () 𝒟′ ℰ′

-- cor315 : ∀ {A B} → ∙ ⊢ A ∨ B true
--                  → ∙ ⊢ A true ⊎ ∙ ⊢ B true
-- cor315 𝒟 with cor315ₛ (cor312′ 𝒟)
-- cor315 𝒟 | inj₁ ℰ = inj₁ (cor36′ ℰ)
-- cor315 𝒟 | inj₂ ℰ = inj₂ (cor36′ ℰ)


-- -- Corollary 3.16 (Independence of excluded middle from natural deduction)

-- -- NOTE: Cannot use a schematic metavariable here

-- cor316ₛ : ¬ (∙ ⟹ "A" ∨ ~ "A")
-- cor316ₛ 𝒟 with cor315ₛ 𝒟
-- cor316ₛ 𝒟 | inj₁ (var ())
-- cor316ₛ 𝒟 | inj₁ (⊃L () 𝒟′ ℰ′)
-- cor316ₛ 𝒟 | inj₁ (∧L₁ () 𝒟′)
-- cor316ₛ 𝒟 | inj₁ (∧L₂ () 𝒟′)
-- cor316ₛ 𝒟 | inj₁ (𝟘L ())
-- cor316ₛ 𝒟 | inj₁ (∨L () 𝒟′ ℰ′)
-- cor316ₛ 𝒟 | inj₂ (⊃R (var (suc ())))
-- cor316ₛ 𝒟 | inj₂ (⊃R (⊃L (suc ()) 𝒟′ ℰ′))
-- cor316ₛ 𝒟 | inj₂ (⊃R (∧L₁ (suc ()) 𝒟′))
-- cor316ₛ 𝒟 | inj₂ (⊃R (∧L₂ (suc ()) 𝒟′))
-- cor316ₛ 𝒟 | inj₂ (⊃R (𝟘L (suc ())))
-- cor316ₛ 𝒟 | inj₂ (⊃R (∨L (suc ()) 𝒟′ ℰ′))
-- cor316ₛ 𝒟 | inj₂ (var ())
-- cor316ₛ 𝒟 | inj₂ (⊃L () 𝒟′ ℰ′)
-- cor316ₛ 𝒟 | inj₂ (∧L₁ () 𝒟′)
-- cor316ₛ 𝒟 | inj₂ (∧L₂ () 𝒟′)
-- cor316ₛ 𝒟 | inj₂ (𝟘L ())
-- cor316ₛ 𝒟 | inj₂ (∨L () 𝒟′ ℰ′)

-- cor316 : ¬ (∙ ⊢ "A" ∨ ~ "A" true)
-- cor316 𝒟 = cor316ₛ (cor312′ 𝒟)


-- --------------------------------------------------------------------------------
