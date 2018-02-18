-- Based on http://www.cs.cmu.edu/~fp/courses/atp/handouts/ch3-seqcalc.pdf

-- NOTE: The direction of ₗ/ᵣ in previous code is wrong compared to Pfenning

-- NOTE: The direction of ⇑/⇓ in previous code is wrong compared to Filinski

module IPLBidirectionalDerivationsForCutElimination where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import FullIPLPropositions
import FullIPLDerivations as IPL


--------------------------------------------------------------------------------


-- Function-based inclusion

infix 4 _⊒_
_⊒_ : ∀ {X} → List X → List X → Set
Ξ′ ⊒ Ξ = ∀ {A} → Ξ ∋ A → Ξ′ ∋ A

keep⊒ : ∀ {X A} → {Ξ Ξ′ : List X}
                → Ξ′ ⊒ Ξ
                → Ξ′ , A ⊒ Ξ , A
keep⊒ η zero    = zero
keep⊒ η (suc i) = suc (η i)


--------------------------------------------------------------------------------


-- Unused now

{-
-- McBride's context deletions

_-_ : ∀ {X A} → (Ξ : List X) → Ξ ∋ A → List X
∙       - ()
(Ξ , A) - zero  = Ξ
(Ξ , B) - suc i = (Ξ - i) , B

del⊇ : ∀ {X A} → {Ξ : List X}
               → (i : Ξ ∋ A)
               → Ξ ⊇ Ξ - i
del⊇ zero    = drop id
del⊇ (suc i) = keep (del⊇ i)


-- McBride's deletion-based variable equality

data _≡∋_ {X} : ∀ {A B} → {Ξ : List X} → Ξ ∋ A → Ξ ∋ B → Set
  where
    same : ∀ {A} → {Ξ : List X}
                 → (i : Ξ ∋ A)
                 → i ≡∋ i

    diff : ∀ {A B} → {Ξ : List X}
                   → (i : Ξ ∋ A) (j : Ξ - i ∋ B)
                   → i ≡∋ ren∋ (del⊇ i) j

_≟∋_ : ∀ {X A B} → {Ξ : List X}
                 → (i : Ξ ∋ A) (j : Ξ ∋ B)
                 → i ≡∋ j
zero  ≟∋ zero   = same zero
zero  ≟∋ suc j  rewrite id-ren∋ j ⁻¹ = diff zero j
suc i ≟∋ zero   = diff (suc i) zero
suc i ≟∋ suc j  with i ≟∋ j
suc i ≟∋ suc .i | same .i = same (suc i)
suc i ≟∋ suc ._ | diff .i j = diff (suc i) (suc j)
-}


--------------------------------------------------------------------------------


-- Normal/neutral deductions

mutual
  infix 3 _⊢_normal
  data _⊢_normal : List Prop → Prop → Set
    where
      lam : ∀ {A B Γ} → Γ , A ⊢ B normal
                      → Γ ⊢ A ⊃ B normal

      pair : ∀ {A B Γ} → Γ ⊢ A normal → Γ ⊢ B normal
                       → Γ ⊢ A ∧ B normal

      unit : ∀ {Γ} → Γ ⊢ ⊤ normal

      abort : ∀ {A Γ} → Γ ⊢ ⊥ neutral
                      → Γ ⊢ A normal

      inl : ∀ {A B Γ} → Γ ⊢ A normal
                      → Γ ⊢ A ∨ B normal

      inr : ∀ {A B Γ} → Γ ⊢ B normal
                      → Γ ⊢ A ∨ B normal

      case : ∀ {A B C Γ} → Γ ⊢ A ∨ B neutral → Γ , A ⊢ C normal → Γ , B ⊢ C normal
                         → Γ ⊢ C normal

      use : ∀ {A Γ} → Γ ⊢ A neutral
                    → Γ ⊢ A normal

  infix 3 _⊢_neutral
  data _⊢_neutral : List Prop → Prop → Set
    where
      var : ∀ {A Γ} → Γ ∋ A
                    → Γ ⊢ A neutral

      app : ∀ {A B Γ} → Γ ⊢ A ⊃ B neutral → Γ ⊢ A normal
                      → Γ ⊢ B neutral

      fst : ∀ {A B Γ} → Γ ⊢ A ∧ B neutral
                      → Γ ⊢ A neutral

      snd : ∀ {A B Γ} → Γ ⊢ A ∧ B neutral
                      → Γ ⊢ B neutral

infix 3 _⊢_allneutral
_⊢_allneutral : List Prop → List Prop → Set
Γ ⊢ Ξ allneutral = All (Γ ⊢_neutral) Ξ


module M1
  where
    mutual
      renₙₘ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A normal
                         → Γ′ ⊢ A normal
      renₙₘ η (lam 𝒟)      = lam (renₙₘ (keep η) 𝒟)
      renₙₘ η (pair 𝒟 ℰ)   = pair (renₙₘ η 𝒟) (renₙₘ η ℰ)
      renₙₘ η unit         = unit
      renₙₘ η (abort 𝒟)    = abort (renₙₜ η 𝒟)
      renₙₘ η (inl 𝒟)      = inl (renₙₘ η 𝒟)
      renₙₘ η (inr 𝒟)      = inr (renₙₘ η 𝒟)
      renₙₘ η (case 𝒟 ℰ ℱ) = case (renₙₜ η 𝒟) (renₙₘ (keep η) ℰ) (renₙₘ (keep η) ℱ)
      renₙₘ η (use 𝒟)      = use (renₙₜ η 𝒟)

      renₙₜ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A neutral
                         → Γ′ ⊢ A neutral
      renₙₜ η (var i)   = var (ren∋ η i)
      renₙₜ η (app 𝒟 ℰ) = app (renₙₜ η 𝒟) (renₙₘ η ℰ)
      renₙₜ η (fst 𝒟)   = fst (renₙₜ η 𝒟)
      renₙₜ η (snd 𝒟)   = snd (renₙₜ η 𝒟)

    rensₙₜ : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢ Ξ allneutral
                        → Γ′ ⊢ Ξ allneutral
    rensₙₜ η ξ = maps (renₙₜ η) ξ

    wkₙₜ : ∀ {B Γ A} → Γ ⊢ A neutral
                     → Γ , B ⊢ A neutral
    wkₙₜ 𝒟 = renₙₜ (drop id) 𝒟

    wksₙₜ : ∀ {A Γ Ξ} → Γ ⊢ Ξ allneutral
                      → Γ , A ⊢ Ξ allneutral
    wksₙₜ ξ = rensₙₜ (drop id) ξ

    vzₙₜ : ∀ {Γ A} → Γ , A ⊢ A neutral
    vzₙₜ = var zero

    liftsₙₜ : ∀ {A Γ Ξ} → Γ ⊢ Ξ allneutral
                        → Γ , A ⊢ Ξ , A allneutral
    liftsₙₜ ξ = wksₙₜ ξ , vzₙₜ

    varsₙₜ : ∀ {Γ Γ′} → Γ′ ⊇ Γ
                      → Γ′ ⊢ Γ allneutral
    varsₙₜ done     = ∙
    varsₙₜ (drop η) = wksₙₜ (varsₙₜ η)
    varsₙₜ (keep η) = liftsₙₜ (varsₙₜ η)

    idsₙₜ : ∀ {Γ} → Γ ⊢ Γ allneutral
    idsₙₜ = varsₙₜ id


-- Theorem 3.1 (Soundness of normal/neutral deductions with respect to natural deduction)

mutual
  thm31ₙₘ : ∀ {Γ A} → Γ ⊢ A normal
                   → Γ IPL.⊢ A true
  thm31ₙₘ (lam 𝒟)      = IPL.lam (thm31ₙₘ 𝒟)
  thm31ₙₘ (pair 𝒟 ℰ)   = IPL.pair (thm31ₙₘ 𝒟) (thm31ₙₘ ℰ)
  thm31ₙₘ unit         = IPL.unit
  thm31ₙₘ (abort 𝒟)    = IPL.abort (thm31ₙₜ 𝒟)
  thm31ₙₘ (inl 𝒟)      = IPL.inl (thm31ₙₘ 𝒟)
  thm31ₙₘ (inr 𝒟)      = IPL.inr (thm31ₙₘ 𝒟)
  thm31ₙₘ (case 𝒟 ℰ ℱ) = IPL.case (thm31ₙₜ 𝒟) (thm31ₙₘ ℰ) (thm31ₙₘ ℱ)
  thm31ₙₘ (use 𝒟)      = thm31ₙₜ 𝒟

  thm31ₙₜ : ∀ {Γ A} → Γ ⊢ A neutral
                   → Γ IPL.⊢ A true
  thm31ₙₜ (var i)   = IPL.var i
  thm31ₙₜ (app 𝒟 ℰ) = IPL.app (thm31ₙₜ 𝒟) (thm31ₙₘ ℰ)
  thm31ₙₜ (fst 𝒟)   = IPL.fst (thm31ₙₜ 𝒟)
  thm31ₙₜ (snd 𝒟)   = IPL.snd (thm31ₙₜ 𝒟)


--------------------------------------------------------------------------------


-- Annotated normal/neutral deductions

mutual
  infix 3 _⊢₊_normal
  data _⊢₊_normal : List Prop → Prop → Set
    where
      lam : ∀ {A B Γ} → Γ , A ⊢₊ B normal
                      → Γ ⊢₊ A ⊃ B normal

      pair : ∀ {A B Γ} → Γ ⊢₊ A normal → Γ ⊢₊ B normal
                       → Γ ⊢₊ A ∧ B normal

      unit : ∀ {Γ} → Γ ⊢₊ ⊤ normal

      abort : ∀ {A Γ} → Γ ⊢₊ ⊥ neutral
                      → Γ ⊢₊ A normal

      inl : ∀ {A B Γ} → Γ ⊢₊ A normal
                      → Γ ⊢₊ A ∨ B normal

      inr : ∀ {A B Γ} → Γ ⊢₊ B normal
                      → Γ ⊢₊ A ∨ B normal

      case : ∀ {A B C Γ} → Γ ⊢₊ A ∨ B neutral → Γ , A ⊢₊ C normal → Γ , B ⊢₊ C normal
                         → Γ ⊢₊ C normal

      use : ∀ {A Γ} → Γ ⊢₊ A neutral
                    → Γ ⊢₊ A normal

  infix 3 _⊢₊_neutral
  data _⊢₊_neutral : List Prop → Prop → Set
    where
      var : ∀ {A Γ} → Γ ∋ A
                    → Γ ⊢₊ A neutral

      app : ∀ {A B Γ} → Γ ⊢₊ A ⊃ B neutral → Γ ⊢₊ A normal
                      → Γ ⊢₊ B neutral

      fst : ∀ {A B Γ} → Γ ⊢₊ A ∧ B neutral
                      → Γ ⊢₊ A neutral

      snd : ∀ {A B Γ} → Γ ⊢₊ A ∧ B neutral
                      → Γ ⊢₊ B neutral

      chk : ∀ {A Γ} → Γ ⊢₊ A normal
                    → Γ ⊢₊ A neutral

infix 3 _⊢₊_allneutral
_⊢₊_allneutral : List Prop → List Prop → Set
Γ ⊢₊ Ξ allneutral = All (Γ ⊢₊_neutral) Ξ


module M2
  where
    mutual
      renₙₘ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢₊ A normal
                         → Γ′ ⊢₊ A normal
      renₙₘ η (lam 𝒟)      = lam (renₙₘ (keep η) 𝒟)
      renₙₘ η (pair 𝒟 ℰ)   = pair (renₙₘ η 𝒟) (renₙₘ η ℰ)
      renₙₘ η unit         = unit
      renₙₘ η (abort 𝒟)    = abort (renₙₜ η 𝒟)
      renₙₘ η (inl 𝒟)      = inl (renₙₘ η 𝒟)
      renₙₘ η (inr 𝒟)      = inr (renₙₘ η 𝒟)
      renₙₘ η (case 𝒟 ℰ ℱ) = case (renₙₜ η 𝒟) (renₙₘ (keep η) ℰ) (renₙₘ (keep η) ℱ)
      renₙₘ η (use 𝒟)      = use (renₙₜ η 𝒟)

      renₙₜ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢₊ A neutral
                         → Γ′ ⊢₊ A neutral
      renₙₜ η (var i)   = var (ren∋ η i)
      renₙₜ η (app 𝒟 ℰ) = app (renₙₜ η 𝒟) (renₙₘ η ℰ)
      renₙₜ η (fst 𝒟)   = fst (renₙₜ η 𝒟)
      renₙₜ η (snd 𝒟)   = snd (renₙₜ η 𝒟)
      renₙₜ η (chk 𝒟)   = chk (renₙₘ η 𝒟)

    rensₙₜ : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢₊ Ξ allneutral
                        → Γ′ ⊢₊ Ξ allneutral
    rensₙₜ η ξ = maps (renₙₜ η) ξ

    wkₙₜ : ∀ {B Γ A} → Γ ⊢₊ A neutral
                     → Γ , B ⊢₊ A neutral
    wkₙₜ 𝒟 = renₙₜ (drop id) 𝒟

    wksₙₜ : ∀ {A Γ Ξ} → Γ ⊢₊ Ξ allneutral
                      → Γ , A ⊢₊ Ξ allneutral
    wksₙₜ ξ = rensₙₜ (drop id) ξ

    vzₙₜ : ∀ {Γ A} → Γ , A ⊢₊ A neutral
    vzₙₜ = var zero

    liftsₙₜ : ∀ {A Γ Ξ} → Γ ⊢₊ Ξ allneutral
                        → Γ , A ⊢₊ Ξ , A allneutral
    liftsₙₜ ξ = wksₙₜ ξ , vzₙₜ

    varsₙₜ : ∀ {Γ Γ′} → Γ′ ⊇ Γ
                      → Γ′ ⊢₊ Γ allneutral
    varsₙₜ done     = ∙
    varsₙₜ (drop η) = wksₙₜ (varsₙₜ η)
    varsₙₜ (keep η) = liftsₙₜ (varsₙₜ η)

    idsₙₜ : ∀ {Γ} → Γ ⊢₊ Γ allneutral
    idsₙₜ = varsₙₜ id


-- Theorem 3.2 (Soundness of annotated normal/neutral deductions with respect to natural deduction)

mutual
  thm32ₙₘ : ∀ {Γ A} → Γ ⊢₊ A normal
                    → Γ IPL.⊢ A true
  thm32ₙₘ (lam 𝒟)      = IPL.lam (thm32ₙₘ 𝒟)
  thm32ₙₘ (pair 𝒟 ℰ)   = IPL.pair (thm32ₙₘ 𝒟) (thm32ₙₘ ℰ)
  thm32ₙₘ unit         = IPL.unit
  thm32ₙₘ (abort 𝒟)    = IPL.abort (thm32ₙₜ 𝒟)
  thm32ₙₘ (inl 𝒟)      = IPL.inl (thm32ₙₘ 𝒟)
  thm32ₙₘ (inr 𝒟)      = IPL.inr (thm32ₙₘ 𝒟)
  thm32ₙₘ (case 𝒟 ℰ ℱ) = IPL.case (thm32ₙₜ 𝒟) (thm32ₙₘ ℰ) (thm32ₙₘ ℱ)
  thm32ₙₘ (use 𝒟)      = thm32ₙₜ 𝒟

  thm32ₙₜ : ∀ {Γ A} → Γ ⊢₊ A neutral
                    → Γ IPL.⊢ A true
  thm32ₙₜ (var i)   = IPL.var i
  thm32ₙₜ (app 𝒟 ℰ) = IPL.app (thm32ₙₜ 𝒟) (thm32ₙₘ ℰ)
  thm32ₙₜ (fst 𝒟)   = IPL.fst (thm32ₙₜ 𝒟)
  thm32ₙₜ (snd 𝒟)   = IPL.snd (thm32ₙₜ 𝒟)
  thm32ₙₜ (chk 𝒟)   = thm32ₙₘ 𝒟


-- Theorem 3.3 (Completeness of annotated normal/neutral deductions with respect to natural deduction)

thm33ₙₘ : ∀ {Γ A} → Γ IPL.⊢ A true
                  → Γ ⊢₊ A normal
thm33ₙₘ (IPL.var i)      = use (var i)
thm33ₙₘ (IPL.lam 𝒟)      = lam (thm33ₙₘ 𝒟)
thm33ₙₘ (IPL.app 𝒟 ℰ)    = use (app (chk (thm33ₙₘ 𝒟)) (thm33ₙₘ ℰ))
thm33ₙₘ (IPL.pair 𝒟 ℰ)   = pair (thm33ₙₘ 𝒟) (thm33ₙₘ ℰ)
thm33ₙₘ (IPL.fst 𝒟)      = use (fst (chk (thm33ₙₘ 𝒟)))
thm33ₙₘ (IPL.snd 𝒟)      = use (snd (chk (thm33ₙₘ 𝒟)))
thm33ₙₘ IPL.unit         = unit
thm33ₙₘ (IPL.abort 𝒟)    = abort (chk (thm33ₙₘ 𝒟))
thm33ₙₘ (IPL.inl 𝒟)      = inl (thm33ₙₘ 𝒟)
thm33ₙₘ (IPL.inr 𝒟)      = inr (thm33ₙₘ 𝒟)
thm33ₙₘ (IPL.case 𝒟 ℰ ℱ) = case (chk (thm33ₙₘ 𝒟)) (thm33ₙₘ ℰ) (thm33ₙₘ ℱ)

thm33ₙₜ : ∀ {Γ A} → Γ IPL.⊢ A true
                  → Γ ⊢₊ A neutral
thm33ₙₜ (IPL.var i)      = var i
thm33ₙₜ (IPL.lam 𝒟)      = chk (lam (use (thm33ₙₜ 𝒟)))
thm33ₙₜ (IPL.app 𝒟 ℰ)    = app (thm33ₙₜ 𝒟) (use (thm33ₙₜ ℰ))
thm33ₙₜ (IPL.pair 𝒟 ℰ)   = chk (pair (use (thm33ₙₜ 𝒟)) (use (thm33ₙₜ ℰ)))
thm33ₙₜ (IPL.fst 𝒟)      = fst (thm33ₙₜ 𝒟)
thm33ₙₜ (IPL.snd 𝒟)      = snd (thm33ₙₜ 𝒟)
thm33ₙₜ IPL.unit         = chk unit
thm33ₙₜ (IPL.abort 𝒟)    = chk (abort (thm33ₙₜ 𝒟))
thm33ₙₜ (IPL.inl 𝒟)      = chk (inl (use (thm33ₙₜ 𝒟)))
thm33ₙₜ (IPL.inr 𝒟)      = chk (inr (use (thm33ₙₜ 𝒟)))
thm33ₙₜ (IPL.case 𝒟 ℰ ℱ) = chk (case (thm33ₙₜ 𝒟) (use (thm33ₙₜ ℰ)) (use (thm33ₙₜ ℱ)))


--------------------------------------------------------------------------------


-- Sequent calculus

mutual
  infix 3 _⟹_
  data _⟹_ : List Prop → Prop → Set
    where
      var : ∀ {A Γ} → Γ ∋ A
                    → Γ ⟹ A

      ⊃r : ∀ {A B Γ} → Γ , A ⟹ B
                     → Γ ⟹ A ⊃ B

      ⊃l : ∀ {A B C Γ} → Γ ∋ A ⊃ B → Γ ⟹ A → Γ , B ⟹ C
                       → Γ ⟹ C

      ∧r : ∀ {A B Γ} → Γ ⟹ A → Γ ⟹ B
                     → Γ ⟹ A ∧ B

      ∧l₁ : ∀ {A B C Γ} → Γ ∋ A ∧ B → Γ , A ⟹ C
                        → Γ ⟹ C

      ∧l₂ : ∀ {A B C Γ} → Γ ∋ A ∧ B → Γ , B ⟹ C
                        → Γ ⟹ C

      ⊤r : ∀ {Γ} → Γ ⟹ ⊤

      ⊥l : ∀ {A Γ} → Γ ∋ ⊥
                    → Γ ⟹ A

      ∨r₁ : ∀ {A B Γ} → Γ ⟹ A
                      → Γ ⟹ A ∨ B

      ∨r₂ : ∀ {A B Γ} → Γ ⟹ B
                      → Γ ⟹ A ∨ B

      ∨l : ∀ {A B C Γ} → Γ ∋ A ∨ B → Γ , A ⟹ C → Γ , B ⟹ C
                       → Γ ⟹ C


-- Lemma 3.5 (Substitution property for normal/neutral deductions)

-- Unused now

{-
mutual
  subₙₘ : ∀ {Γ A B} → (i : Γ ∋ A) → Γ - i ⊢ A neutral → Γ ⊢ B normal
                    → Γ - i ⊢ B normal
  subₙₘ i 𝒞 (lam 𝒟)      = lam (subₙₘ (suc i) (M1.renₙₜ (drop id) 𝒞) 𝒟)
  subₙₘ i 𝒞 (pair 𝒟 ℰ)   = pair (subₙₘ i 𝒞 𝒟) (subₙₘ i 𝒞 ℰ)
  subₙₘ i 𝒞 unit         = unit
  subₙₘ i 𝒞 (abort 𝒟)    = abort (subₙₜ i 𝒞 𝒟)
  subₙₘ i 𝒞 (inl 𝒟)      = inl (subₙₘ i 𝒞 𝒟)
  subₙₘ i 𝒞 (inr 𝒟)      = inr (subₙₘ i 𝒞 𝒟)
  subₙₘ i 𝒞 (case 𝒟 ℰ ℱ) = case (subₙₜ i 𝒞 𝒟) (subₙₘ (suc i) (M1.renₙₜ (drop id) 𝒞) ℰ)
                                              (subₙₘ (suc i) (M1.renₙₜ (drop id) 𝒞) ℱ)
  subₙₘ i 𝒞 (use 𝒟)      = use (subₙₜ i 𝒞 𝒟)

  subₙₜ : ∀ {Γ A B} → (i : Γ ∋ A) → Γ - i ⊢ A neutral → Γ ⊢ B neutral
                    → Γ - i ⊢ B neutral
  subₙₜ i 𝒞 (var j)   with i ≟∋ j
  subₙₜ i 𝒞 (var .i)  | same .i   = 𝒞
  subₙₜ i 𝒞 (var ._)  | diff .i j = var j
  subₙₜ i 𝒞 (app 𝒟 ℰ) = app (subₙₜ i 𝒞 𝒟) (subₙₘ i 𝒞 ℰ)
  subₙₜ i 𝒞 (fst 𝒟)   = fst (subₙₜ i 𝒞 𝒟)
  subₙₜ i 𝒞 (snd 𝒟)   = snd (subₙₜ i 𝒞 𝒟)
-}

mutual
  ssubₙₘ : ∀ {Γ Ξ A} → Γ ⊢ Ξ allneutral → Ξ ⊢ A normal
                     → Γ ⊢ A normal
  ssubₙₘ ξ (lam 𝒟)      = lam (ssubₙₘ (M1.liftsₙₜ ξ) 𝒟)
  ssubₙₘ ξ (pair 𝒟 ℰ)   = pair (ssubₙₘ ξ 𝒟) (ssubₙₘ ξ ℰ)
  ssubₙₘ ξ unit         = unit
  ssubₙₘ ξ (abort 𝒟)    = abort (ssubₙₜ ξ 𝒟)
  ssubₙₘ ξ (inl 𝒟)      = inl (ssubₙₘ ξ 𝒟)
  ssubₙₘ ξ (inr 𝒟)      = inr (ssubₙₘ ξ 𝒟)
  ssubₙₘ ξ (case 𝒟 ℰ ℱ) = case (ssubₙₜ ξ 𝒟) (ssubₙₘ (M1.liftsₙₜ ξ) ℰ)
                                            (ssubₙₘ (M1.liftsₙₜ ξ) ℱ)
  ssubₙₘ ξ (use 𝒟)      = use (ssubₙₜ ξ 𝒟)

  ssubₙₜ : ∀ {Γ Ξ A} → Γ ⊢ Ξ allneutral → Ξ ⊢ A neutral
                     → Γ ⊢ A neutral
  ssubₙₜ ξ (var i)   = get ξ i
  ssubₙₜ ξ (app 𝒟 ℰ) = app (ssubₙₜ ξ 𝒟) (ssubₙₘ ξ ℰ)
  ssubₙₜ ξ (fst 𝒟)   = fst (ssubₙₜ ξ 𝒟)
  ssubₙₜ ξ (snd 𝒟)   = snd (ssubₙₜ ξ 𝒟)

cutₙₘ : ∀ {Γ A B} → Γ ⊢ A neutral → Γ , A ⊢ B normal
                  → Γ ⊢ B normal
cutₙₘ 𝒟 ℰ = ssubₙₘ (M1.idsₙₜ , 𝒟) ℰ


-- Theorem 3.6 (Soundness of sequent calculus with respect to normal deduction)

thm36 : ∀ {Γ A} → Γ ⟹ A
                → Γ ⊢ A normal
thm36 (var i)    = use (var i)
thm36 (⊃r 𝒟)     = lam (thm36 𝒟)
thm36 (⊃l i 𝒟 ℰ) = cutₙₘ (app (var i) (thm36 𝒟)) (thm36 ℰ)
thm36 (∧r 𝒟 ℰ)   = pair (thm36 𝒟) (thm36 ℰ)
thm36 (∧l₁ i 𝒟)  = cutₙₘ (fst (var i)) (thm36 𝒟)
thm36 (∧l₂ i 𝒟)  = cutₙₘ (snd (var i)) (thm36 𝒟)
thm36 ⊤r        = unit
thm36 (⊥l i)    = abort (var i)
thm36 (∨r₁ 𝒟)    = inl (thm36 𝒟)
thm36 (∨r₂ 𝒟)    = inr (thm36 𝒟)
thm36 (∨l i 𝒟 ℰ) = case (var i) (thm36 𝒟) (thm36 ℰ)


-- Lemma 3.7 (Structural properties of sequent calculus)

vzₛ : ∀ {Γ A} → Γ , A ⟹ A
vzₛ = var zero

renₛ : ∀ {Γ Γ′ A} → Γ′ ⊒ Γ → Γ ⟹ A
                  → Γ′ ⟹ A
renₛ η (var i)    = var (η i)
renₛ η (⊃r 𝒟)     = ⊃r (renₛ (keep⊒ η) 𝒟)
renₛ η (⊃l i 𝒟 ℰ) = ⊃l (η i) (renₛ η 𝒟) (renₛ (keep⊒ η) ℰ)
renₛ η (∧r 𝒟 ℰ)   = ∧r (renₛ η 𝒟) (renₛ η ℰ)
renₛ η (∧l₁ i 𝒟)  = ∧l₁ (η i) (renₛ (keep⊒ η) 𝒟)
renₛ η (∧l₂ i 𝒟)  = ∧l₂ (η i) (renₛ (keep⊒ η) 𝒟)
renₛ η ⊤r        = ⊤r
renₛ η (⊥l i)    = ⊥l (η i)
renₛ η (∨r₁ 𝒟)    = ∨r₁ (renₛ η 𝒟)
renₛ η (∨r₂ 𝒟)    = ∨r₂ (renₛ η 𝒟)
renₛ η (∨l i 𝒟 ℰ) = ∨l (η i) (renₛ (keep⊒ η) 𝒟) (renₛ (keep⊒ η) ℰ)

wkₛ : ∀ {B Γ A} → Γ ⟹ A
                → Γ , B ⟹ A
wkₛ = renₛ suc

exₛ : ∀ {Γ A B C} → Γ , A , B ⟹ C
                  → Γ , B , A ⟹ C
exₛ = renₛ \ { zero          → suc zero
             ; (suc zero)    → zero
             ; (suc (suc i)) → suc (suc i)
             }

ctₛ : ∀ {Γ A B} → Γ , A , A ⟹ B
                → Γ , A ⟹ B
ctₛ = renₛ \ { zero          → zero
             ; (suc zero)    → zero
             ; (suc (suc i)) → suc i
             }


-- Theorem 3.8 (Completeness of sequent calculus with respect to normal/neutral deductions)

-- TODO: ???

-- postulate
--   thm38∋ : ∀ {Γ A B} → Γ ∋ A → Γ , A ⟹ B
--                      → Γ ⟹ B
-- thm38∋ zero    𝒟        = ctₛ 𝒟
-- thm38∋ (suc i) vzₛ      = wkₛ (thm38∋ i vzₛ)
-- thm38∋ (suc i) (⊃r 𝒟)   = ⊃r (thm38∋ (suc (suc i)) (exₛ 𝒟))
-- thm38∋ (suc i) (⊃l 𝒟 ℰ) = {!⊃l ? ℰ!}

mutual
  thm38ₙₘ : ∀ {Γ A} → Γ ⊢ A normal
                    → Γ ⟹ A
  thm38ₙₘ (lam 𝒟)      = ⊃r (thm38ₙₘ 𝒟)
  thm38ₙₘ (pair 𝒟 ℰ)   = ∧r (thm38ₙₘ 𝒟) (thm38ₙₘ ℰ)
  thm38ₙₘ unit         = ⊤r
  thm38ₙₘ (abort 𝒟)    = ⊥l {!!} -- Γ ∋ ⊥
  thm38ₙₘ (inl 𝒟)      = ∨r₁ (thm38ₙₘ 𝒟)
  thm38ₙₘ (inr 𝒟)      = ∨r₂ (thm38ₙₘ 𝒟)
  thm38ₙₘ (case 𝒟 ℰ ℱ) = ∨l {!!} (thm38ₙₘ ℰ) (thm38ₙₘ ℱ) -- Γ ∋ A ∨ B
  thm38ₙₘ (use 𝒟)      = thm38ₙₜ 𝒟 vzₛ

  thm38ₙₜ : ∀ {Γ A B} → Γ ⊢ A neutral → Γ , A ⟹ B
                      → Γ ⟹ B
  thm38ₙₜ (var i)     ℰ = {!!} -- Γ ⟹ B
  thm38ₙₜ (app 𝒟₁ 𝒟₂) ℰ = thm38ₙₜ 𝒟₁ (⊃l zero (wkₛ (thm38ₙₘ 𝒟₂)) (exₛ (wkₛ ℰ)))
  thm38ₙₜ (fst 𝒟)     ℰ = thm38ₙₜ 𝒟 (∧l₁ zero (exₛ (wkₛ ℰ)))
  thm38ₙₜ (snd 𝒟)     ℰ = thm38ₙₜ 𝒟 (∧l₂ zero (exₛ (wkₛ ℰ)))


--------------------------------------------------------------------------------


-- -- Sequent calculus with cut

-- mutual
--   infix 3 _⟹₊_
--   data _⟹₊_ : List Prop → Prop → Set
--     where
--       vzₛ : ∀ {A Γ} → Γ , A ⟹₊ A

--       ⊃r : ∀ {A B Γ} → Γ , A ⟹₊ B
--                      → Γ ⟹₊ A ⊃ B

--       ⊃l : ∀ {A B C Γ} → Γ , A ⊃ B ⟹₊ A → Γ , A ⊃ B , B ⟹₊ C
--                        → Γ , A ⊃ B ⟹₊ C

--       cutₛ : ∀ {A B Γ} → Γ ⟹₊ A → Γ , A ⟹₊ B
--                        → Γ ⟹₊ B


-- -- Lemma ??? (Substitution property for annotated normal/neutral deductions)

-- mutual
--   subₙₘ₊ : ∀ {Γ A B} → (i : Γ ∋ A) → Γ - i ⊢₊ A neutral → Γ ⊢₊ B normal
--                     → Γ - i ⊢₊ B normal
--   subₙₘ₊ i 𝒞 (lam 𝒟) = lam (subₙₘ₊ (suc i) (M2.renₙₜ (drop id) 𝒞) 𝒟)
--   subₙₘ₊ i 𝒞 (use 𝒟) = use (subₙₜ₊ i 𝒞 𝒟)

--   subₙₜ₊ : ∀ {Γ A B} → (i : Γ ∋ A) → Γ - i ⊢₊ A neutral → Γ ⊢₊ B neutral
--                     → Γ - i ⊢₊ B neutral
--   subₙₜ₊ i 𝒞 (var j)   with i ≟∋ j
--   subₙₜ₊ i 𝒞 (var .i)  | same .i   = 𝒞
--   subₙₜ₊ i 𝒞 (var ._)  | diff .i j = var j
--   subₙₜ₊ i 𝒞 (app 𝒟 ℰ) = app (subₙₜ₊ i 𝒞 𝒟) (subₙₘ₊ i 𝒞 ℰ)
--   subₙₜ₊ i 𝒞 (chk 𝒟)   = chk (subₙₘ₊ i 𝒞 𝒟)


-- -- Alternative?

-- pseudosubₙₘ₊ : ∀ {Γ A B} → Γ ⊢₊ A normal → Γ , A ⊢₊ B normal
--                         → Γ ⊢₊ B normal
-- pseudosubₙₘ₊ 𝒟 ℰ = use (app (chk (lam ℰ)) 𝒟)

-- pseudosubₙₜ₊ : ∀ {Γ A B} → Γ ⊢₊ A neutral → Γ , A ⊢₊ B neutral
--                         → Γ ⊢₊ B neutral
-- pseudosubₙₜ₊ 𝒟 ℰ = app (chk (lam (use ℰ))) (use 𝒟)


-- -- Theorem 3.9 (Soundness of sequent calculus with cut with respect to annotated normal deductions)

-- mutual
--   thm39ᵣ₊ : ∀ {Γ A} → Γ ⟹₊ A
--                     → Γ ⊢₊ A normal
--   thm39ᵣ₊ vzₛ        = use M2.vzₙₜ
--   thm39ᵣ₊ (⊃r 𝒟)     = lam (thm39ᵣ₊ 𝒟)
--   thm39ᵣ₊ (⊃l 𝒟 ℰ)   = subₙₘ₊ zero (app (var zero) (thm39ᵣ₊ 𝒟)) (thm39ᵣ₊ ℰ)
--   thm39ᵣ₊ (cutₛ 𝒟 ℰ) = subₙₘ₊ zero (thm39ₗ₊ 𝒟) (thm39ᵣ₊ ℰ)

--   thm39ₗ₊ : ∀ {Γ A} → Γ ⟹₊ A
--                     → Γ ⊢₊ A neutral
--   thm39ₗ₊ vzₛ        = M2.vzₙₜ
--   thm39ₗ₊ (⊃r 𝒟)     = chk (lam (use (thm39ₗ₊ 𝒟)))
--   thm39ₗ₊ (⊃l 𝒟 ℰ)   = subₙₜ₊ zero (app (var zero) (use (thm39ₗ₊ 𝒟))) (thm39ₗ₊ ℰ)
--   thm39ₗ₊ (cutₛ 𝒟 ℰ) = subₙₜ₊ zero (thm39ₗ₊ 𝒟) (thm39ₗ₊ ℰ)

-- module Alternative
--   where
--     athm39ᵣ₊ : ∀ {Γ A} → Γ ⟹₊ A
--                        → Γ ⊢₊ A normal
--     athm39ᵣ₊ vzₛ        = use M2.vzₙₜ
--     athm39ᵣ₊ (⊃r 𝒟)     = lam (athm39ᵣ₊ 𝒟)
--     athm39ᵣ₊ (⊃l 𝒟 ℰ)   = pseudosubₙₘ₊ (use (app (var zero) (athm39ᵣ₊ 𝒟))) (athm39ᵣ₊ ℰ)
--     athm39ᵣ₊ (cutₛ 𝒟 ℰ) = pseudosubₙₘ₊ (athm39ᵣ₊ 𝒟) (athm39ᵣ₊ ℰ)

--     athm39ₗ₊ : ∀ {Γ A} → Γ ⟹₊ A
--                        → Γ ⊢₊ A neutral
--     athm39ₗ₊ vzₛ        = M2.vzₙₜ
--     athm39ₗ₊ (⊃r 𝒟)     = chk (lam (use (athm39ₗ₊ 𝒟)))
--     athm39ₗ₊ (⊃l 𝒟 ℰ)   = pseudosubₙₜ₊ (app (var zero) (use (athm39ₗ₊ 𝒟))) (athm39ₗ₊ ℰ)
--     athm39ₗ₊ (cutₛ 𝒟 ℰ) = pseudosubₙₜ₊ (athm39ₗ₊ 𝒟) (athm39ₗ₊ ℰ)


-- -- Lemma ??? (Structural properties of sequent calculus with cut)

-- -- TODO: Do we need these as primitives?

-- postulate
--   wkₛ₊ : ∀ {B Γ A} → Γ ⟹₊ A
--                    → Γ , B ⟹₊ A

--   ctₛ₊ : ∀ {Γ A B} → Γ , A , A ⟹₊ B
--                    → Γ , A ⟹₊ B

--   exₛ₊ : ∀ {Γ A B C} → Γ , A , B ⟹₊ C
--                      → Γ , B , A ⟹₊ C


-- -- Theorem 3.10 (Completeness of sequent calculus with cut with respect to annotated normal/neutral deductions)

-- -- TODO: ???

-- postulate
--   thm310∋ : ∀ {Γ A B} → Γ ∋ A → Γ , A ⟹₊ B
--                       → Γ ⟹₊ B
-- -- thm310∋ zero    𝒟          = ctₛ₊ 𝒟
-- -- thm310∋ (suc i) vzₛ        = wkₛ₊ (thm310∋ i vzₛ)
-- -- thm310∋ (suc i) (⊃r 𝒟)     = ⊃r (thm310∋ (suc (suc i)) (exₛ₊ 𝒟))
-- -- thm310∋ (suc i) (⊃l 𝒟 ℰ)   = {!⊃l ? ℰ!}
-- -- thm310∋ (suc i) (cutₛ 𝒟 ℰ) = {!cutₛ 𝒟 ℰ!}

-- mutual
--   thm310ᵣ₊ : ∀ {Γ A} → Γ ⊢₊ A normal
--                      → Γ ⟹₊ A
--   thm310ᵣ₊ (lam 𝒟) = ⊃r (thm310ᵣ₊ 𝒟)
--   thm310ᵣ₊ (use 𝒟) = thm310ₗ₊ 𝒟 vzₛ

--   thm310ₗ₊ : ∀ {Γ A B} → Γ ⊢₊ A neutral → Γ , A ⟹₊ B
--                        → Γ ⟹₊ B
--   thm310ₗ₊ (var i)     ℰ = thm310∋ i ℰ
--   thm310ₗ₊ (app 𝒟₁ 𝒟₂) ℰ = thm310ₗ₊ 𝒟₁ (⊃l (wkₛ₊ (thm310ᵣ₊ 𝒟₂)) (exₛ₊ (wkₛ₊ ℰ)))
--   thm310ₗ₊ (chk 𝒟)     ℰ = cutₛ (thm310ᵣ₊ 𝒟) ℰ


-- -- Theorem 3.11 (Admissibility of cut)

-- thm311 : ∀ {A Γ B} → Γ ⟹ A → Γ , A ⟹ B
--                    → Γ ⟹ B
-- thm311 {A}     vzₛ        ℰ          = ctₛ ℰ
-- thm311 {A}     𝒟          vzₛ        = 𝒟
-- thm311 {ι P}   (⊃l 𝒟₁ 𝒟₂) (⊃r ℰ)     = {!!}
-- thm311 {A ⊃ B} (⊃r 𝒟)     (⊃r ℰ)     = {!!}
-- thm311 {A ⊃ B} (⊃r 𝒟)     (⊃l ℰ₁ ℰ₂) = {!!}
-- thm311 {A ⊃ B} (⊃l 𝒟₁ 𝒟₂) (⊃r ℰ)     = {!!}
-- thm311 {A ⊃ B} (⊃l 𝒟₁ 𝒟₂) (⊃l ℰ₁ ℰ₂) = {!!}
-- thm311 {A ∧ B} 𝒟 ℰ = {!!}
-- thm311 {⊤}    𝒟 ℰ = {!!}
-- thm311 {⊥}    𝒟 ℰ = {!!}
-- thm311 {A ∨ B} 𝒟 ℰ = {!!}


-- -- Theorem 3.12 (Cut elimination)

-- thm312 : ∀ {Γ A} → Γ ⟹₊ A
--                  → Γ ⟹ A
-- thm312 vzₛ        = vzₛ
-- thm312 (⊃r 𝒟)     = ⊃r (thm312 𝒟)
-- thm312 (⊃l 𝒟 ℰ)   = ⊃l (thm312 𝒟) (thm312 ℰ)
-- thm312 (cutₛ 𝒟 ℰ) = thm311 (thm312 𝒟) (thm312 ℰ)


-- ⊢→⟹ : ∀ {Γ A} → Γ ⊢ A true
--                   → Γ ⟹ A
-- ⊢→⟹ 𝒟 = thm312 (thm310ᵣ₊ (thm33ₙₘ 𝒟))


-- -- Theorem 3.13 (Normalisation for natural deduction)

-- thm313 : ∀ {Γ A} → Γ ⊢ A true
--                  → Γ ⊢ A normal
-- thm313 𝒟 = thm36 (⊢→⟹ 𝒟)


-- -- Corollary 3.14 (Consistency)

-- cor314 : ¬ (∙ ⊢ ⊥ true)
-- cor314 𝒟 with ⊢→⟹ 𝒟
-- cor314 𝒟 | ()


-- -- Corollary 3.15 (Disjunction property)

-- -- TODO: Existentials for the existential property

-- cor315 : ∀ {A B} → ∙ ⊢ A ∨ B true → ∙ ⊢ A true ⊎ ∙ ⊢ B true
-- cor315 𝒟 with ⊢→⟹ 𝒟
-- cor315 𝒟 | ()


-- -- Corollary 3.16 (Independence of excluded middle)

-- -- TODO: ???

-- -- postulate
-- --   oops₁ : ∀ {A} → ¬ (∙ ⟹ A)
-- --   oops₂ : ∀ {A} → ¬ (∙ ⟹ ~ A)
-- --
-- --
-- -- wat : ((∀ {A} → ∙ ⊢ A true) ⊎ (∀ {B} → ∙ ⊢ B true)) → (∀ {A B} → ∙ ⊢ A true ⊎ ∙ ⊢ B true)
-- -- wat (inj₁ 𝒟) = inj₁ 𝒟
-- -- wat (inj₂ ℰ) = inj₁ ℰ
-- --
-- -- unwat : (∀ {A} → ∙ ⊢ A true ⊎ ∙ ⊢ ~ A true) → ((∀ {A} → ∙ ⊢ A true) ⊎ (∀ {A} → ∙ ⊢ ~ A true))
-- -- unwat f = {!!}
-- --
-- --
-- --
-- -- distribute-∀ : (∀ {A B : Set} → A ⊎ B) → ((∀ {A : Set} → A) ⊎ (∀ {B : Set} → B))
-- -- distribute-∀ f = {!f!}
-- --
-- -- distribute-∀″ : ∀ {A : Set} (P : A → Set) (Q : A → Set) →
-- --                            (∀ a → P a ⊎ Q a) →
-- --                            (∀ a → P a) ⊎ (∀ a → Q a)
-- -- distribute-∀″ P Q f = {!!}
-- --
-- --
-- --
-- -- -- distribute-∀ : ∀ {A : Set} (P : A → Set) (Q : A → Set) → (∀ a → P a ⊎ Q a) → (∀ a → P a) ⊎ (∀ a → Q a)
-- -- -- distribute-∀ P Q f = {!!}
-- --
-- --
-- -- omg : ∀ {A} → ∙ ⊢ A true ⊎ ∙ ⊢ ~ A true
-- -- omg {ι P}   = {!!}
-- -- omg {A ⊃ B} = {!!}
-- -- omg {A ∧ B} = {!!}
-- -- omg {⊤}    = {!!}
-- -- omg {⊥}    = {!!}
-- -- omg {A ∨ B} = {!!}
-- --
-- -- -- cor316 : ∀ {A} → ¬ (∙ ⊢ A ∨ ~ A true)
-- -- -- cor316 𝒟 = {!cor315 𝒟!}
-- --
-- -- watt : ∙ ⊢ ⊥ ∨ ~ ⊥ true
-- -- watt = inr (lam (var zero))

-- -- cor316 𝒟 with cor315 𝒟
-- -- cor316 𝒟 | inj₁ 𝒟′ with ⊢→⟹ 𝒟′
-- -- cor316 𝒟 | inj₁ 𝒟′ | 𝒟″ = oops₁ 𝒟″
-- -- cor316 𝒟 | inj₂ 𝒟′ with ⊢→⟹ 𝒟′
-- -- cor316 𝒟 | inj₂ 𝒟′ | 𝒟″ = oops₂ 𝒟″


-- cor316 : ¬ (∀ {A} → ∙ ⊢ A ∨ ~ A true)
-- cor316 f = {!!}



-- --------------------------------------------------------------------------------
