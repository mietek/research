module A201801.SequentCalculusDraft2b where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.FullIPLPropositions
open import A201801.FullIPLDerivations hiding (cut)
open import A201801.SequentCalculusDraftSquasha


--------------------------------------------------------------------------------


-- Sequent calculus

infix 3 _⟹_
data _⟹_ : [List] Form → Form → Set
  where
    ⊃R : ∀ {A B Γ} → Γ [,] A ⟹ B
                   → Γ ⟹ A ⊃ B

    ∧R : ∀ {A B Γ} → Γ ⟹ A → Γ ⟹ B
                   → Γ ⟹ A ∧ B

    𝟙R : ∀ {Γ} → Γ ⟹ 𝟙

    ∨R₁ : ∀ {A B Γ} → Γ ⟹ A
                    → Γ ⟹ A ∨ B

    ∨R₂ : ∀ {A B Γ} → Γ ⟹ B
                    → Γ ⟹ A ∨ B

    vzₛ : ∀ {A Γ} → Γ [,] A ⟹ A

    ⊃L : ∀ {A B C Γ} → Γ [,] A ⊃ B ⟹ A → Γ [,] A ⊃ B [,] B ⟹ C
                     → Γ [,] A ⊃ B ⟹ C

    ∧L₁ : ∀ {A B C Γ} → Γ [,] A ∧ B [,] A ⟹ C
                      → Γ [,] A ∧ B ⟹ C

    ∧L₂ : ∀ {A B C Γ} → Γ [,] A ∧ B [,] B ⟹ C
                      → Γ [,] A ∧ B ⟹ C

    𝟘L : ∀ {A Γ} → Γ [,] 𝟘 ⟹ A

    ∨L : ∀ {A B C Γ} → Γ [,] A ∨ B [,] A ⟹ C → Γ [,] A ∨ B [,] B ⟹ C
                     → Γ [,] A ∨ B ⟹ C

infix 3 _⟹_all
_⟹_all : [List] Form → List Form → Set
Γ ⟹ Ξ all = All (Γ ⟹_) Ξ


-- Theorem 3.6 (Soundness of sequent calculus with respect to normal deduction)

thm36 : ∀ {Γ A} → squash Γ ⟹ A
                → squash Γ ⊢ A normal
thm36 {Γ} (⊃R 𝒟)           = lam (thm36 {Γ} 𝒟)
thm36 {Γ} (∧R 𝒟 ℰ)         = pair (thm36 {Γ} 𝒟) (thm36 {Γ} ℰ)
thm36 {Γ} 𝟙R               = unit
thm36 {Γ} (∨R₁ 𝒟)          = inl (thm36 {Γ} 𝒟)
thm36 {Γ} (∨R₂ 𝒟)          = inr (thm36 {Γ} 𝒟)
thm36 {Γ} vzₛ              = vzₙₘ {squash Γ}
thm36 {Γ} (⊃L {B = B} 𝒟 ℰ) = cutₙₘ {Γ} {B} (app (vzₙₜ {squash Γ}) (thm36 {Γ} 𝒟)) (thm36 {Γ} ℰ)
thm36 {Γ} (∧L₁ {B = B} 𝒟)  = cutₙₘ {Γ} {B} (fst {B = B} (vzₙₜ {squash Γ})) (thm36 {Γ} 𝒟)
thm36 {Γ} (∧L₂ {A} 𝒟)      = cutₙₘ {Γ} {A} (snd {A = A} (vzₙₜ {squash Γ})) (thm36 {Γ} 𝒟)
thm36 {Γ} 𝟘L               = abort (vzₙₜ {squash Γ})
thm36 {Γ} (∨L {A} {B} 𝒟 ℰ) = case {A} {B} (vzₙₜ {squash Γ}) (thm36 {Γ} 𝒟) (thm36 {Γ} ℰ)


-- Corollary ??? (Soundness of sequent calculus with respect to natural deduction)

cor36′ : ∀ {Γ A} → squash Γ ⟹ A
                 → Γ ⊢ A true
cor36′ {Γ} 𝒟 = thm31ₙₘ (thm36 {Γ} 𝒟)


-- Lemma 3.7 (Structural properties of sequent calculus)

-- wkₛ : ∀ {B Γ A} → Γ ⟹ A
--                 → Γ [,] B ⟹ A
-- wkₛ 𝒟 = 𝒟
--
-- exₛ : ∀ {Γ A B C} → Γ [,] A [,] B ⟹ C
--                   → Γ [,] B [,] A ⟹ C
-- exₛ 𝒟 = 𝒟
--
-- ctₛ : ∀ {Γ A B} → Γ [,] A [,] A ⟹ B
--                 → Γ [,] A ⟹ B
-- ctₛ 𝒟 = 𝒟

varₛ : ∀ {Γ A} → Γ [∋] A
               → Γ ⟹ A
varₛ {Γ} zero    = vzₛ {Γ = Γ}
varₛ     (suc i) = varₛ i

liftsₛ : ∀ {Γ Ξ A} → Γ ⟹ Ξ all
                   → Γ [,] A ⟹ Ξ , A all
liftsₛ {Γ} ξ = ξ , vzₛ {Γ = Γ}

idsₛ : ∀ {Γ} → squash Γ ⟹ Γ all
idsₛ {∙}     = ∙
idsₛ {Γ , A} = liftsₛ idsₛ


-- Theorem 3.8 (Completeness of sequent calculus with respect to normal/neutral deductions)

mutual
  thm38ₙₘ : ∀ {Γ A} → Γ ⊢ A normal
                    → Γ ⟹ A
  thm38ₙₘ     (lam 𝒟)              = ⊃R (thm38ₙₘ 𝒟)
  thm38ₙₘ     (pair 𝒟 ℰ)           = ∧R (thm38ₙₘ 𝒟) (thm38ₙₘ ℰ)
  thm38ₙₘ     unit                 = 𝟙R
  thm38ₙₘ {Γ} (abort 𝒟)            = thm38ₙₜ 𝒟 (𝟘L {Γ = Γ})
  thm38ₙₘ     (inl 𝒟)              = ∨R₁ (thm38ₙₘ 𝒟)
  thm38ₙₘ     (inr 𝒟)              = ∨R₂ (thm38ₙₘ 𝒟)
  thm38ₙₘ {Γ} (case {A} {B} 𝒟 ℰ ℱ) = thm38ₙₜ 𝒟 (∨L {A} {B} {Γ = Γ} (thm38ₙₘ ℰ) (thm38ₙₘ ℱ))
  thm38ₙₘ {Γ} (ent 𝒟)              = thm38ₙₜ 𝒟 (vzₛ {Γ = Γ})

  thm38ₙₜ : ∀ {Γ A B} → Γ ⊢ A neutral → Γ [,] A ⟹ B
                      → Γ ⟹ B
  thm38ₙₜ     (var i)             ℰ = ℰ
  thm38ₙₜ {Γ} (app {B = B} 𝒟₁ 𝒟₂) ℰ = thm38ₙₜ 𝒟₁ (⊃L {B = B} {Γ = Γ} (thm38ₙₘ 𝒟₂) ℰ)
  thm38ₙₜ {Γ} (fst {A} {B} 𝒟)     ℰ = thm38ₙₜ 𝒟 (∧L₁ {A} {B} {Γ = Γ} ℰ)
  thm38ₙₜ {Γ} (snd {A} {B} 𝒟)     ℰ = thm38ₙₜ 𝒟 (∧L₂ {A} {B} {Γ = Γ} ℰ)


--------------------------------------------------------------------------------


-- Sequent calculus with cut

infix 3 _⟹₊_
data _⟹₊_ : [List] Form → Form → Set
  where
    ⊃R : ∀ {A B Γ} → Γ [,] A ⟹₊ B
                   → Γ ⟹₊ A ⊃ B

    ∧R : ∀ {A B Γ} → Γ ⟹₊ A → Γ ⟹₊ B
                   → Γ ⟹₊ A ∧ B

    𝟙R : ∀ {Γ} → Γ ⟹₊ 𝟙

    ∨R₁ : ∀ {A B Γ} → Γ ⟹₊ A
                    → Γ ⟹₊ A ∨ B

    ∨R₂ : ∀ {A B Γ} → Γ ⟹₊ B
                    → Γ ⟹₊ A ∨ B

    vzₛ₊ : ∀ {A Γ} → Γ [,] A ⟹₊ A

    ⊃L : ∀ {A B C Γ} → Γ [,] A ⊃ B ⟹₊ A → Γ [,] A ⊃ B [,] B ⟹₊ C
                     → Γ [,] A ⊃ B ⟹₊ C

    ∧L₁ : ∀ {A B C Γ} → Γ [,] A ∧ B [,] A ⟹₊ C
                      → Γ [,] A ∧ B ⟹₊ C

    ∧L₂ : ∀ {A B C Γ} → Γ [,] A ∧ B [,] B ⟹₊ C
                      → Γ [,] A ∧ B ⟹₊ C

    𝟘L : ∀ {A Γ} → Γ [,] 𝟘 ⟹₊ A

    ∨L : ∀ {A B C Γ} → Γ [,] A ∨ B [,] A ⟹₊ C → Γ [,] A ∨ B [,] B ⟹₊ C
                     → Γ [,] A ∨ B ⟹₊ C

    cut : ∀ {A B Γ} → Γ ⟹₊ A → Γ [,] A ⟹₊ B
                    → Γ ⟹₊ B

infix 3 _⟹₊_all
_⟹₊_all : [List] Form → List Form → Set
Γ ⟹₊ Ξ all = All (Γ ⟹₊_) Ξ


-- Theorem 3.9 (Soundness of sequent calculus with cut with respect to annotated normal deduction)

thm39 : ∀ {Γ A} → squash Γ ⟹₊ A
                → squash Γ ⊢₊ A normal
thm39 {Γ} (⊃R 𝒟)           = lam (thm39 {Γ} 𝒟)
thm39 {Γ} (∧R 𝒟 ℰ)         = pair (thm39 {Γ} 𝒟) (thm39 {Γ} ℰ)
thm39 {Γ} 𝟙R               = unit
thm39 {Γ} (∨R₁ 𝒟)          = inl (thm39 {Γ} 𝒟)
thm39 {Γ} (∨R₂ 𝒟)          = inr (thm39 {Γ} 𝒟)
thm39 {Γ} vzₛ₊             = vzₙₘ₊ {squash Γ}
thm39 {Γ} (⊃L {B = B} 𝒟 ℰ) = cutₙₘ₊ {Γ} {B} (app (vzₙₜ₊ {squash Γ}) (thm39 {Γ} 𝒟)) (thm39 {Γ} ℰ)
thm39 {Γ} (∧L₁ {B = B} 𝒟)  = cutₙₘ₊ {Γ} {B} (fst {B = B} (vzₙₜ₊ {squash Γ})) (thm39 {Γ} 𝒟)
thm39 {Γ} (∧L₂ {A} 𝒟)      = cutₙₘ₊ {Γ} {A} (snd {A = A} (vzₙₜ₊ {squash Γ})) (thm39 {Γ} 𝒟)
thm39 {Γ} 𝟘L               = abort (vzₙₜ₊ {squash Γ})
thm39 {Γ} (∨L {A} {B} 𝒟 ℰ) = case {A} {B} (vzₙₜ₊ {squash Γ}) (thm39 {Γ} 𝒟) (thm39 {Γ} ℰ)
thm39 {Γ} (cut 𝒟 ℰ)        = cutₙₘ₊ {Γ = Γ} (enm (thm39 {Γ} 𝒟)) (thm39 {Γ} ℰ)


-- Lemma ??? (Structural properties of sequent calculus with cut)

varₛ₊ : ∀ {Γ A} → Γ [∋] A
                → Γ ⟹₊ A
varₛ₊ {Γ} zero    = vzₛ₊ {Γ = Γ}
varₛ₊     (suc i) = varₛ₊ i

liftsₛ₊ : ∀ {Γ Ξ A} → Γ ⟹₊ Ξ all
                    → Γ [,] A ⟹₊ Ξ , A all
liftsₛ₊ {Γ} ξ = ξ , vzₛ₊ {Γ = Γ}

idsₛ₊ : ∀ {Γ} → squash Γ ⟹₊ Γ all
idsₛ₊ {∙}     = ∙
idsₛ₊ {Γ , A} = liftsₛ₊ idsₛ₊


-- Theorem 3.10 (Completeness of sequent calculus with cut with respect to normal/neutral deductions)

mutual
  thm310ₙₘ : ∀ {Γ A} → Γ ⊢₊ A normal
                     → Γ ⟹₊ A
  thm310ₙₘ     (lam 𝒟)              = ⊃R (thm310ₙₘ 𝒟)
  thm310ₙₘ     (pair 𝒟 ℰ)           = ∧R (thm310ₙₘ 𝒟) (thm310ₙₘ ℰ)
  thm310ₙₘ     unit                 = 𝟙R
  thm310ₙₘ {Γ} (abort 𝒟)            = thm310ₙₜ 𝒟 (𝟘L {Γ = Γ})
  thm310ₙₘ     (inl 𝒟)              = ∨R₁ (thm310ₙₘ 𝒟)
  thm310ₙₘ     (inr 𝒟)              = ∨R₂ (thm310ₙₘ 𝒟)
  thm310ₙₘ {Γ} (case {A} {B} 𝒟 ℰ ℱ) = thm310ₙₜ 𝒟 (∨L {A} {B} {Γ = Γ} (thm310ₙₘ ℰ) (thm310ₙₘ ℱ))
  thm310ₙₘ {Γ} (ent 𝒟)              = thm310ₙₜ 𝒟 (vzₛ₊ {Γ = Γ})

  thm310ₙₜ : ∀ {Γ A B} → Γ ⊢₊ A neutral → Γ [,] A ⟹₊ B
                       → Γ ⟹₊ B
  thm310ₙₜ     (var i)             ℰ = ℰ
  thm310ₙₜ {Γ} (app {B = B} 𝒟₁ 𝒟₂) ℰ = thm310ₙₜ 𝒟₁ (⊃L {B = B} {Γ = Γ} (thm310ₙₘ 𝒟₂) ℰ)
  thm310ₙₜ {Γ} (fst {A} {B} 𝒟)     ℰ = thm310ₙₜ 𝒟 (∧L₁ {A} {B} {Γ = Γ} ℰ)
  thm310ₙₜ {Γ} (snd {A} {B} 𝒟)     ℰ = thm310ₙₜ 𝒟 (∧L₂ {A} {B} {Γ = Γ} ℰ)
  thm310ₙₜ {Γ} (enm 𝒟)             ℰ = cut (thm310ₙₘ 𝒟) ℰ


--------------------------------------------------------------------------------


-- TODO: unfinished
-- -- Theorem 3.11 (Admissibility of cut)

-- thm311 : ∀ {Γ A C} → Γ ⟹ A → Γ [,] A ⟹ C
--                    → Γ ⟹ C

-- -- Case: A is not the principal formula of the last inference in ℰ.
-- -- In this case, we appeal to the induction hypothesis on the
-- -- subderivations of ℰ and directly infer the conclusion from the results.
-- thm311 𝒟 (⊃R ℰ)     = ⊃R (thm311 𝒟 ℰ)
-- thm311 𝒟 (∧R ℰ₁ ℰ₂) = ∧R (thm311 𝒟 ℰ₁) (thm311 𝒟 ℰ₂)
-- thm311 𝒟 𝟙R         = 𝟙R
-- thm311 𝒟 (∨R₁ ℰ)    = ∨R₁ (thm311 𝒟 ℰ)
-- thm311 𝒟 (∨R₂ ℰ)    = ∨R₂ (thm311 𝒟 ℰ)

-- -- Case: ℰ is an initial sequent using the cut formula
-- -- Case: ℰ is an initial sequent not using the cut formula
-- -- TODO: ???
-- thm311 𝒟 vzₛ = {!𝒟!}

-- -- Case: 𝒟 is an initial sequent
-- thm311 vzₛ ℰ = ℰ

-- -- Case: A is not the principal formula of the last inference in 𝒟.
-- -- In that case 𝒟 must end in a left rule and we can appeal to the
-- -- induction hypothesis on one of its premises.
-- thm311 {Γ} (⊃L {B = B} 𝒟₁ 𝒟₂) ℰ = ⊃L {B = B} {Γ = Γ} 𝒟₁ (thm311 𝒟₂ ℰ)
-- thm311 {Γ} (∧L₁ {A} {B} 𝒟)    ℰ = ∧L₁ {A} {B} {Γ = Γ} (thm311 𝒟 ℰ)
-- thm311 {Γ} (∧L₂ {A} {B} 𝒟)    ℰ = ∧L₂ {A} {B} {Γ = Γ} (thm311 𝒟 ℰ)
-- thm311 {Γ} 𝟘L                 ℰ = 𝟘L {Γ = Γ}
-- thm311 {Γ} (∨L {A} {B} 𝒟₁ 𝒟₂) ℰ = ∨L {A} {B} {Γ = Γ} (thm311 𝒟₁ ℰ) (thm311 𝒟₂ ℰ)

-- -- Case: A is the principal formula of the final inference in both
-- -- 𝒟 and ℰ.  There are a number of subcases to consider, based on the
-- -- last inference in 𝒟 and ℰ.
-- thm311 {Γ} 𝒟 (⊃L {B = B} ℰ₁ ℰ₂) = ⊃L {B = B} {Γ = Γ} (thm311 𝒟 ℰ₁) (thm311 𝒟 ℰ₂)
-- thm311 {Γ} 𝒟 (∧L₁ {A} {B} ℰ)    = ∧L₁ {A} {B} {Γ = Γ} (thm311 𝒟 ℰ)
-- thm311 {Γ} 𝒟 (∧L₂ {A} {B} ℰ)    = ∧L₂ {A} {B} {Γ = Γ} (thm311 𝒟 ℰ)
-- thm311 {Γ} 𝒟 𝟘L                 = 𝟘L {Γ = Γ}
-- thm311 {Γ} 𝒟 (∨L {A} {B} ℰ₁ ℰ₂) = ∨L {A} {B} {Γ = Γ} (thm311 𝒟 ℰ₁) (thm311 𝒟 ℰ₂)


-- --------------------------------------------------------------------------------


-- -- Theorem 3.12 (Cut elimination)

-- thm312 : ∀ {Γ A} → Γ ⟹₊ A
--                  → Γ ⟹ A
-- thm312     (⊃R 𝒟)           = ⊃R (thm312 𝒟)
-- thm312     (∧R 𝒟 ℰ)         = ∧R (thm312 𝒟) (thm312 ℰ)
-- thm312     𝟙R               = 𝟙R
-- thm312     (∨R₁ 𝒟)          = ∨R₁ (thm312 𝒟)
-- thm312     (∨R₂ 𝒟)          = ∨R₂ (thm312 𝒟)
-- thm312 {Γ} vzₛ₊             = vzₛ {Γ = Γ}
-- thm312 {Γ} (⊃L {B = B} 𝒟 ℰ) = ⊃L {B = B} {Γ = Γ} (thm312 𝒟) (thm312 ℰ)
-- thm312 {Γ} (∧L₁ {A} {B} 𝒟)  = ∧L₁ {A} {B} {Γ = Γ}(thm312 𝒟)
-- thm312 {Γ} (∧L₂ {A} {B} 𝒟)  = ∧L₂ {A} {B} {Γ = Γ}(thm312 𝒟)
-- thm312 {Γ} 𝟘L               = 𝟘L {Γ = Γ}
-- thm312 {Γ} (∨L {A} {B} 𝒟 ℰ) = ∨L {A} {B} {Γ = Γ} (thm312 𝒟) (thm312 ℰ)
-- thm312     (cut 𝒟 ℰ)        = thm311 (thm312 𝒟) (thm312 ℰ)


-- -- Corollary ??? (Completeness of sequent calculus with respect to natural deduction)

-- cor312′ : ∀ {Γ A} → Γ ⊢ A true
--                   → squash Γ ⟹ A
-- cor312′ 𝒟 = thm312 (thm310ₙₘ (thm33ₙₘ 𝒟))


-- -- Theorem 3.13 (Normalisation of natural deduction)

-- thm313 : ∀ {Γ A} → Γ ⊢ A true
--                  → squash Γ ⊢ A normal
-- thm313 {Γ} 𝒟 = thm36 {Γ} (cor312′ 𝒟)


-- -- Corollary 3.14 (Consistency of natural deduction)

-- -- TODO: ???

-- postulate
--   cor314 : ¬ (∙ ⊢ 𝟘 true)
-- -- cor314 𝒟 with cor312′ 𝒟
-- -- cor314 𝒟 | vzₛ      = {!!}
-- -- cor314 𝒟 | ⊃L 𝒟′ ℰ′ = {!!}
-- -- cor314 𝒟 | ∧L₁ 𝒟′   = {!!}
-- -- cor314 𝒟 | ∧L₂ 𝒟′   = {!!}
-- -- cor314 𝒟 | 𝟘L       = {!!}
-- -- cor314 𝒟 | ∨L 𝒟′ ℰ′ = {!!}


-- -- Corollary 3.15 (Disjunction property of natural deduction)

-- -- TODO: Existentials for the existential property! Skulls for the skull throne!

-- -- TODO: ???

-- postulate
--   cor315ₛ : ∀ {A B} → squash ∙ ⟹ A ∨ B
--                     → squash ∙ ⟹ A ⊎ squash ∙ ⟹ B
-- -- cor315ₛ 𝒟 with cor312′ {∙} (cor36′ 𝒟)
-- -- cor315ₛ 𝒟 | ∨R₁ 𝒟′   = inj₁ 𝒟′
-- -- cor315ₛ 𝒟 | ∨R₂ 𝒟′   = inj₂ 𝒟′
-- -- cor315ₛ 𝒟 | vzₛ      = {!!}
-- -- cor315ₛ 𝒟 | ⊃L 𝒟′ ℰ′ = {!!}
-- -- cor315ₛ 𝒟 | ∧L₁ 𝒟′   = {!!}
-- -- cor315ₛ 𝒟 | ∧L₂ 𝒟′   = {!!}
-- -- cor315ₛ 𝒟 | 𝟘L       = {!!}
-- -- cor315ₛ 𝒟 | ∨L 𝒟′ ℰ′ = {!!}

-- cor315 : ∀ {A B} → ∙ ⊢ A ∨ B true
--                  → ∙ ⊢ A true ⊎ ∙ ⊢ B true
-- cor315 𝒟 with cor315ₛ (cor312′ 𝒟)
-- cor315 𝒟 | inj₁ ℰ = inj₁ (cor36′ ℰ)
-- cor315 𝒟 | inj₂ ℰ = inj₂ (cor36′ ℰ)


-- -- Corollary 3.16 (Independence of excluded middle from natural deduction)

-- -- NOTE: Cannot use a schematic metavariable here

-- -- TODO: ???

-- postulate
--   cor316ₛ : ¬ (squash ∙ ⟹ "A" ∨ ~ "A")
-- -- cor316ₛ 𝒟 with cor315ₛ 𝒟
-- -- cor316ₛ 𝒟 | inj₁ vzₛ             = {!!}
-- -- cor316ₛ 𝒟 | inj₁ (⊃L 𝒟′ ℰ′)      = {!!}
-- -- cor316ₛ 𝒟 | inj₁ (∧L₁ 𝒟′)        = {!!}
-- -- cor316ₛ 𝒟 | inj₁ (∧L₂ 𝒟′)        = {!!}
-- -- cor316ₛ 𝒟 | inj₁ 𝟘L              = {!!}
-- -- cor316ₛ 𝒟 | inj₁ (∨L 𝒟′ ℰ′)      = {!!}
-- -- cor316ₛ 𝒟 | inj₂ (⊃R vzₛ)        = {!!}
-- -- cor316ₛ 𝒟 | inj₂ (⊃R (⊃L 𝒟′ ℰ′)) = {!!}
-- -- cor316ₛ 𝒟 | inj₂ (⊃R (∧L₁ 𝒟′))   = {!!}
-- -- cor316ₛ 𝒟 | inj₂ (⊃R (∧L₂ 𝒟′))   = {!!}
-- -- cor316ₛ 𝒟 | inj₂ (⊃R 𝟘L)         = {!!}
-- -- cor316ₛ 𝒟 | inj₂ (⊃R (∨L 𝒟′ ℰ′)) = {!!}
-- -- cor316ₛ 𝒟 | inj₂ vzₛ             = {!!}
-- -- cor316ₛ 𝒟 | inj₂ (⊃L 𝒟′ ℰ′)      = {!!}
-- -- cor316ₛ 𝒟 | inj₂ (∧L₁ 𝒟′)        = {!!}
-- -- cor316ₛ 𝒟 | inj₂ (∧L₂ 𝒟′)        = {!!}
-- -- cor316ₛ 𝒟 | inj₂ 𝟘L              = {!!}
-- -- cor316ₛ 𝒟 | inj₂ (∨L 𝒟′ ℰ′)      = {!!}

-- cor316 : ¬ (∙ ⊢ "A" ∨ ~ "A" true)
-- cor316 𝒟 = cor316ₛ (cor312′ 𝒟)


-- --------------------------------------------------------------------------------
