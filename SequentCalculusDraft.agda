-- Based on http://www.cs.cmu.edu/~fp/courses/atp/handouts/ch3-seqcalc.pdf

-- NOTE: The direction of ₗ/ᵣ in previous code is wrong compared to Pfenning

-- NOTE: The direction of ⇑/⇓ in previous code is wrong compared to Filinski

module SequentCalculusDraft where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import FullIPLPropositions
open import FullIPLDerivations hiding (cut)


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

ex⊒ : ∀ {X A B} → {Ξ : List X}
                → Ξ , B , A ⊒ Ξ , A , B
ex⊒ zero          = suc zero
ex⊒ (suc zero)    = zero
ex⊒ (suc (suc i)) = suc (suc i)

ct⊒ : ∀ {X A} → {Ξ : List X}
              → Ξ , A  ⊒ Ξ , A , A
ct⊒ zero          = zero
ct⊒ (suc zero)    = zero
ct⊒ (suc (suc i)) = suc i

genct⊒ : ∀ {X A} → {Ξ : List X}
                 → Ξ ∋ A
                 → Ξ ⊒ Ξ , A
genct⊒ i zero    = i
genct⊒ i (suc j) = j


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

      ent : ∀ {A Γ} → Γ ⊢ A neutral
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
  renₙₘ η (ent 𝒟)      = ent (renₙₜ η 𝒟)

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


-- Lemma 3.5 (Substitution property of normal/neutral deductions)

mutual
  subₙₘ : ∀ {Γ Ξ A} → Γ ⊢ Ξ allneutral → Ξ ⊢ A normal
                    → Γ ⊢ A normal
  subₙₘ ξ (lam 𝒟)      = lam (subₙₘ (liftsₙₜ ξ) 𝒟)
  subₙₘ ξ (pair 𝒟 ℰ)   = pair (subₙₘ ξ 𝒟) (subₙₘ ξ ℰ)
  subₙₘ ξ unit         = unit
  subₙₘ ξ (abort 𝒟)    = abort (subₙₜ ξ 𝒟)
  subₙₘ ξ (inl 𝒟)      = inl (subₙₘ ξ 𝒟)
  subₙₘ ξ (inr 𝒟)      = inr (subₙₘ ξ 𝒟)
  subₙₘ ξ (case 𝒟 ℰ ℱ) = case (subₙₜ ξ 𝒟) (subₙₘ (liftsₙₜ ξ) ℰ)
                                          (subₙₘ (liftsₙₜ ξ) ℱ)
  subₙₘ ξ (ent 𝒟)      = ent (subₙₜ ξ 𝒟)

  subₙₜ : ∀ {Γ Ξ A} → Γ ⊢ Ξ allneutral → Ξ ⊢ A neutral
                    → Γ ⊢ A neutral
  subₙₜ ξ (var i)   = get ξ i
  subₙₜ ξ (app 𝒟 ℰ) = app (subₙₜ ξ 𝒟) (subₙₘ ξ ℰ)
  subₙₜ ξ (fst 𝒟)   = fst (subₙₜ ξ 𝒟)
  subₙₜ ξ (snd 𝒟)   = snd (subₙₜ ξ 𝒟)

cutₙₘ : ∀ {Γ A B} → Γ ⊢ A neutral → Γ , A ⊢ B normal
                  → Γ ⊢ B normal
cutₙₘ 𝒟 ℰ = subₙₘ (idsₙₜ , 𝒟) ℰ


-- Theorem 3.1 (Soundness of normal/neutral deductions with respect to natural deduction)

mutual
  thm31ₙₘ : ∀ {Γ A} → Γ ⊢ A normal
                    → Γ ⊢ A true
  thm31ₙₘ (lam 𝒟)      = lam (thm31ₙₘ 𝒟)
  thm31ₙₘ (pair 𝒟 ℰ)   = pair (thm31ₙₘ 𝒟) (thm31ₙₘ ℰ)
  thm31ₙₘ unit         = unit
  thm31ₙₘ (abort 𝒟)    = abort (thm31ₙₜ 𝒟)
  thm31ₙₘ (inl 𝒟)      = inl (thm31ₙₘ 𝒟)
  thm31ₙₘ (inr 𝒟)      = inr (thm31ₙₘ 𝒟)
  thm31ₙₘ (case 𝒟 ℰ ℱ) = case (thm31ₙₜ 𝒟) (thm31ₙₘ ℰ) (thm31ₙₘ ℱ)
  thm31ₙₘ (ent 𝒟)      = thm31ₙₜ 𝒟

  thm31ₙₜ : ∀ {Γ A} → Γ ⊢ A neutral
                    → Γ ⊢ A true
  thm31ₙₜ (var i)   = var i
  thm31ₙₜ (app 𝒟 ℰ) = app (thm31ₙₜ 𝒟) (thm31ₙₘ ℰ)
  thm31ₙₜ (fst 𝒟)   = fst (thm31ₙₜ 𝒟)
  thm31ₙₜ (snd 𝒟)   = snd (thm31ₙₜ 𝒟)


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

      ent : ∀ {A Γ} → Γ ⊢₊ A neutral
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

      enm : ∀ {A Γ} → Γ ⊢₊ A normal
                    → Γ ⊢₊ A neutral

infix 3 _⊢₊_allneutral
_⊢₊_allneutral : List Prop → List Prop → Set
Γ ⊢₊ Ξ allneutral = All (Γ ⊢₊_neutral) Ξ


mutual
  renₙₘ₊ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢₊ A normal
                     → Γ′ ⊢₊ A normal
  renₙₘ₊ η (lam 𝒟)      = lam (renₙₘ₊ (keep η) 𝒟)
  renₙₘ₊ η (pair 𝒟 ℰ)   = pair (renₙₘ₊ η 𝒟) (renₙₘ₊ η ℰ)
  renₙₘ₊ η unit         = unit
  renₙₘ₊ η (abort 𝒟)    = abort (renₙₜ₊ η 𝒟)
  renₙₘ₊ η (inl 𝒟)      = inl (renₙₘ₊ η 𝒟)
  renₙₘ₊ η (inr 𝒟)      = inr (renₙₘ₊ η 𝒟)
  renₙₘ₊ η (case 𝒟 ℰ ℱ) = case (renₙₜ₊ η 𝒟) (renₙₘ₊ (keep η) ℰ) (renₙₘ₊ (keep η) ℱ)
  renₙₘ₊ η (ent 𝒟)      = ent (renₙₜ₊ η 𝒟)

  renₙₜ₊ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢₊ A neutral
                     → Γ′ ⊢₊ A neutral
  renₙₜ₊ η (var i)   = var (ren∋ η i)
  renₙₜ₊ η (app 𝒟 ℰ) = app (renₙₜ₊ η 𝒟) (renₙₘ₊ η ℰ)
  renₙₜ₊ η (fst 𝒟)   = fst (renₙₜ₊ η 𝒟)
  renₙₜ₊ η (snd 𝒟)   = snd (renₙₜ₊ η 𝒟)
  renₙₜ₊ η (enm 𝒟)   = enm (renₙₘ₊ η 𝒟)

rensₙₜ₊ : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢₊ Ξ allneutral
                     → Γ′ ⊢₊ Ξ allneutral
rensₙₜ₊ η ξ = maps (renₙₜ₊ η) ξ

wkₙₜ₊ : ∀ {B Γ A} → Γ ⊢₊ A neutral
                  → Γ , B ⊢₊ A neutral
wkₙₜ₊ 𝒟 = renₙₜ₊ (drop id) 𝒟

wksₙₜ₊ : ∀ {A Γ Ξ} → Γ ⊢₊ Ξ allneutral
                   → Γ , A ⊢₊ Ξ allneutral
wksₙₜ₊ ξ = rensₙₜ₊ (drop id) ξ

vzₙₜ₊ : ∀ {Γ A} → Γ , A ⊢₊ A neutral
vzₙₜ₊ = var zero

liftsₙₜ₊ : ∀ {A Γ Ξ} → Γ ⊢₊ Ξ allneutral
                     → Γ , A ⊢₊ Ξ , A allneutral
liftsₙₜ₊ ξ = wksₙₜ₊ ξ , vzₙₜ₊

varsₙₜ₊ : ∀ {Γ Γ′} → Γ′ ⊇ Γ
                   → Γ′ ⊢₊ Γ allneutral
varsₙₜ₊ done     = ∙
varsₙₜ₊ (drop η) = wksₙₜ₊ (varsₙₜ₊ η)
varsₙₜ₊ (keep η) = liftsₙₜ₊ (varsₙₜ₊ η)

idsₙₜ₊ : ∀ {Γ} → Γ ⊢₊ Γ allneutral
idsₙₜ₊ = varsₙₜ₊ id


-- Lemma ??? (Substitution property of annotated normal/neutral deductions)

mutual
  subₙₘ₊ : ∀ {Γ Ξ A} → Γ ⊢₊ Ξ allneutral → Ξ ⊢₊ A normal
                     → Γ ⊢₊ A normal
  subₙₘ₊ ξ (lam 𝒟)      = lam (subₙₘ₊ (liftsₙₜ₊ ξ) 𝒟)
  subₙₘ₊ ξ (pair 𝒟 ℰ)   = pair (subₙₘ₊ ξ 𝒟) (subₙₘ₊ ξ ℰ)
  subₙₘ₊ ξ unit         = unit
  subₙₘ₊ ξ (abort 𝒟)    = abort (subₙₜ₊ ξ 𝒟)
  subₙₘ₊ ξ (inl 𝒟)      = inl (subₙₘ₊ ξ 𝒟)
  subₙₘ₊ ξ (inr 𝒟)      = inr (subₙₘ₊ ξ 𝒟)
  subₙₘ₊ ξ (case 𝒟 ℰ ℱ) = case (subₙₜ₊ ξ 𝒟) (subₙₘ₊ (liftsₙₜ₊ ξ) ℰ)
                                            (subₙₘ₊ (liftsₙₜ₊ ξ) ℱ)
  subₙₘ₊ ξ (ent 𝒟)      = ent (subₙₜ₊ ξ 𝒟)

  subₙₜ₊ : ∀ {Γ Ξ A} → Γ ⊢₊ Ξ allneutral → Ξ ⊢₊ A neutral
                     → Γ ⊢₊ A neutral
  subₙₜ₊ ξ (var i)   = get ξ i
  subₙₜ₊ ξ (app 𝒟 ℰ) = app (subₙₜ₊ ξ 𝒟) (subₙₘ₊ ξ ℰ)
  subₙₜ₊ ξ (fst 𝒟)   = fst (subₙₜ₊ ξ 𝒟)
  subₙₜ₊ ξ (snd 𝒟)   = snd (subₙₜ₊ ξ 𝒟)
  subₙₜ₊ ξ (enm 𝒟)   = enm (subₙₘ₊ ξ 𝒟)

cutₙₘ₊ : ∀ {Γ A B} → Γ ⊢₊ A neutral → Γ , A ⊢₊ B normal
                   → Γ ⊢₊ B normal
cutₙₘ₊ 𝒟 ℰ = subₙₘ₊ (idsₙₜ₊ , 𝒟) ℰ

pseudocutₙₘ₊ : ∀ {Γ A B} → Γ ⊢₊ A normal → Γ , A ⊢₊ B normal
                         → Γ ⊢₊ B normal
pseudocutₙₘ₊ 𝒟 ℰ = ent (app (enm (lam ℰ)) 𝒟)


-- Theorem 3.2 (Soundness of annotated normal/neutral deductions with respect to natural deduction)

mutual
  thm32ₙₘ : ∀ {Γ A} → Γ ⊢₊ A normal
                    → Γ ⊢ A true
  thm32ₙₘ (lam 𝒟)      = lam (thm32ₙₘ 𝒟)
  thm32ₙₘ (pair 𝒟 ℰ)   = pair (thm32ₙₘ 𝒟) (thm32ₙₘ ℰ)
  thm32ₙₘ unit         = unit
  thm32ₙₘ (abort 𝒟)    = abort (thm32ₙₜ 𝒟)
  thm32ₙₘ (inl 𝒟)      = inl (thm32ₙₘ 𝒟)
  thm32ₙₘ (inr 𝒟)      = inr (thm32ₙₘ 𝒟)
  thm32ₙₘ (case 𝒟 ℰ ℱ) = case (thm32ₙₜ 𝒟) (thm32ₙₘ ℰ) (thm32ₙₘ ℱ)
  thm32ₙₘ (ent 𝒟)      = thm32ₙₜ 𝒟

  thm32ₙₜ : ∀ {Γ A} → Γ ⊢₊ A neutral
                    → Γ ⊢ A true
  thm32ₙₜ (var i)   = var i
  thm32ₙₜ (app 𝒟 ℰ) = app (thm32ₙₜ 𝒟) (thm32ₙₘ ℰ)
  thm32ₙₜ (fst 𝒟)   = fst (thm32ₙₜ 𝒟)
  thm32ₙₜ (snd 𝒟)   = snd (thm32ₙₜ 𝒟)
  thm32ₙₜ (enm 𝒟)   = thm32ₙₘ 𝒟


-- Theorem 3.3 (Completeness of annotated normal/neutral deductions with respect to natural deduction)

thm33ₙₘ : ∀ {Γ A} → Γ ⊢ A true
                  → Γ ⊢₊ A normal
thm33ₙₘ (var i)      = ent (var i)
thm33ₙₘ (lam 𝒟)      = lam (thm33ₙₘ 𝒟)
thm33ₙₘ (app 𝒟 ℰ)    = ent (app (enm (thm33ₙₘ 𝒟)) (thm33ₙₘ ℰ))
thm33ₙₘ (pair 𝒟 ℰ)   = pair (thm33ₙₘ 𝒟) (thm33ₙₘ ℰ)
thm33ₙₘ (fst 𝒟)      = ent (fst (enm (thm33ₙₘ 𝒟)))
thm33ₙₘ (snd 𝒟)      = ent (snd (enm (thm33ₙₘ 𝒟)))
thm33ₙₘ unit         = unit
thm33ₙₘ (abort 𝒟)    = abort (enm (thm33ₙₘ 𝒟))
thm33ₙₘ (inl 𝒟)      = inl (thm33ₙₘ 𝒟)
thm33ₙₘ (inr 𝒟)      = inr (thm33ₙₘ 𝒟)
thm33ₙₘ (case 𝒟 ℰ ℱ) = case (enm (thm33ₙₘ 𝒟)) (thm33ₙₘ ℰ) (thm33ₙₘ ℱ)

thm33ₙₜ : ∀ {Γ A} → Γ ⊢ A true
                  → Γ ⊢₊ A neutral
thm33ₙₜ (var i)      = var i
thm33ₙₜ (lam 𝒟)      = enm (lam (ent (thm33ₙₜ 𝒟)))
thm33ₙₜ (app 𝒟 ℰ)    = app (thm33ₙₜ 𝒟) (ent (thm33ₙₜ ℰ))
thm33ₙₜ (pair 𝒟 ℰ)   = enm (pair (ent (thm33ₙₜ 𝒟)) (ent (thm33ₙₜ ℰ)))
thm33ₙₜ (fst 𝒟)      = fst (thm33ₙₜ 𝒟)
thm33ₙₜ (snd 𝒟)      = snd (thm33ₙₜ 𝒟)
thm33ₙₜ unit         = enm unit
thm33ₙₜ (abort 𝒟)    = enm (abort (thm33ₙₜ 𝒟))
thm33ₙₜ (inl 𝒟)      = enm (inl (ent (thm33ₙₜ 𝒟)))
thm33ₙₜ (inr 𝒟)      = enm (inr (ent (thm33ₙₜ 𝒟)))
thm33ₙₜ (case 𝒟 ℰ ℱ) = enm (case (thm33ₙₜ 𝒟) (ent (thm33ₙₜ ℰ)) (ent (thm33ₙₜ ℱ)))


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


-- Theorem 3.6 (Soundness of sequent calculus with respect to normal deduction)

thm36 : ∀ {Γ A} → Γ ⟹ A
                → Γ ⊢ A normal
thm36 (var i)    = ent (var i)
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


-- Corollary ??? (Soundness of sequent calculus with respect to natural deduction)

cor36′ : ∀ {Γ A} → Γ ⟹ A
                 → Γ ⊢ A true
cor36′ 𝒟 = thm31ₙₘ (thm36 𝒟)


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
wkₛ 𝒟 = renₛ suc 𝒟

exₛ : ∀ {Γ A B C} → Γ , A , B ⟹ C
                  → Γ , B , A ⟹ C
exₛ 𝒟 = renₛ ex⊒ 𝒟

ctₛ : ∀ {Γ A B} → Γ , A , A ⟹ B
                → Γ , A ⟹ B
ctₛ 𝒟 = renₛ ct⊒ 𝒟


-- Theorem 3.8 (Completeness of sequent calculus with respect to normal/neutral deductions)

mutual
  thm38ₙₘ : ∀ {Γ A} → Γ ⊢ A normal
                    → Γ ⟹ A
  thm38ₙₘ (lam 𝒟)      = ⊃r (thm38ₙₘ 𝒟)
  thm38ₙₘ (pair 𝒟 ℰ)   = ∧r (thm38ₙₘ 𝒟) (thm38ₙₘ ℰ)
  thm38ₙₘ unit         = ⊤r
  thm38ₙₘ (abort 𝒟)    = thm38ₙₜ 𝒟 (⊥l zero)
  thm38ₙₘ (inl 𝒟)      = ∨r₁ (thm38ₙₘ 𝒟)
  thm38ₙₘ (inr 𝒟)      = ∨r₂ (thm38ₙₘ 𝒟)
  thm38ₙₘ (case 𝒟 ℰ ℱ) = thm38ₙₜ 𝒟 (∨l zero (exₛ (wkₛ (thm38ₙₘ ℰ)))
                                            (exₛ (wkₛ (thm38ₙₘ ℱ))))
  thm38ₙₘ (ent 𝒟)      = thm38ₙₜ 𝒟 vzₛ

  thm38ₙₜ : ∀ {Γ A B} → Γ ⊢ A neutral → Γ , A ⟹ B
                      → Γ ⟹ B
  thm38ₙₜ (var i)     ℰ = renₛ (genct⊒ i) ℰ
  thm38ₙₜ (app 𝒟₁ 𝒟₂) ℰ = thm38ₙₜ 𝒟₁ (⊃l zero (wkₛ (thm38ₙₘ 𝒟₂)) (exₛ (wkₛ ℰ)))
  thm38ₙₜ (fst 𝒟)     ℰ = thm38ₙₜ 𝒟 (∧l₁ zero (exₛ (wkₛ ℰ)))
  thm38ₙₜ (snd 𝒟)     ℰ = thm38ₙₜ 𝒟 (∧l₂ zero (exₛ (wkₛ ℰ)))


--------------------------------------------------------------------------------


-- Sequent calculus with cut

mutual
  infix 3 _⟹₊_
  data _⟹₊_ : List Prop → Prop → Set
    where
      var : ∀ {A Γ} → Γ ∋ A
                    → Γ ⟹₊ A

      ⊃r : ∀ {A B Γ} → Γ , A ⟹₊ B
                     → Γ ⟹₊ A ⊃ B

      ⊃l : ∀ {A B C Γ} → Γ ∋ A ⊃ B → Γ ⟹₊ A → Γ , B ⟹₊ C
                       → Γ ⟹₊ C

      ∧r : ∀ {A B Γ} → Γ ⟹₊ A → Γ ⟹₊ B
                     → Γ ⟹₊ A ∧ B

      ∧l₁ : ∀ {A B C Γ} → Γ ∋ A ∧ B → Γ , A ⟹₊ C
                        → Γ ⟹₊ C

      ∧l₂ : ∀ {A B C Γ} → Γ ∋ A ∧ B → Γ , B ⟹₊ C
                        → Γ ⟹₊ C

      ⊤r : ∀ {Γ} → Γ ⟹₊ ⊤

      ⊥l : ∀ {A Γ} → Γ ∋ ⊥
                    → Γ ⟹₊ A

      ∨r₁ : ∀ {A B Γ} → Γ ⟹₊ A
                      → Γ ⟹₊ A ∨ B

      ∨r₂ : ∀ {A B Γ} → Γ ⟹₊ B
                      → Γ ⟹₊ A ∨ B

      ∨l : ∀ {A B C Γ} → Γ ∋ A ∨ B → Γ , A ⟹₊ C → Γ , B ⟹₊ C
                       → Γ ⟹₊ C

      cut : ∀ {A B Γ} → Γ ⟹₊ A → Γ , A ⟹₊ B
                      → Γ ⟹₊ B


-- Theorem 3.9 (Soundness of sequent calculus with cut with respect to annotated normal deductions)

thm39 : ∀ {Γ A} → Γ ⟹₊ A
                → Γ ⊢₊ A normal
thm39 (var i)    = ent (var i)
thm39 (⊃r 𝒟)     = lam (thm39 𝒟)
thm39 (⊃l i 𝒟 ℰ) = cutₙₘ₊ (app (var i) (thm39 𝒟)) (thm39 ℰ)
thm39 (∧r 𝒟 ℰ)   = pair (thm39 𝒟) (thm39 ℰ)
thm39 (∧l₁ i 𝒟)  = cutₙₘ₊ (fst (var i)) (thm39 𝒟)
thm39 (∧l₂ i 𝒟)  = cutₙₘ₊ (snd (var i)) (thm39 𝒟)
thm39 ⊤r        = unit
thm39 (⊥l i)    = abort (var i)
thm39 (∨r₁ 𝒟)    = inl (thm39 𝒟)
thm39 (∨r₂ 𝒟)    = inr (thm39 𝒟)
thm39 (∨l x 𝒟 ℰ) = case (var x) (thm39 𝒟) (thm39 ℰ)
thm39 (cut 𝒟 ℰ)  = cutₙₘ₊ (enm (thm39 𝒟)) (thm39 ℰ)


-- Lemma ??? (Structural properties of sequent calculus with cut)

vzₛ₊ : ∀ {Γ A} → Γ , A ⟹₊ A
vzₛ₊ = var zero

renₛ₊ : ∀ {Γ Γ′ A} → Γ′ ⊒ Γ → Γ ⟹₊ A
                   → Γ′ ⟹₊ A
renₛ₊ η (var i)    = var (η i)
renₛ₊ η (⊃r 𝒟)     = ⊃r (renₛ₊ (keep⊒ η) 𝒟)
renₛ₊ η (⊃l i 𝒟 ℰ) = ⊃l (η i) (renₛ₊ η 𝒟) (renₛ₊ (keep⊒ η) ℰ)
renₛ₊ η (∧r 𝒟 ℰ)   = ∧r (renₛ₊ η 𝒟) (renₛ₊ η ℰ)
renₛ₊ η (∧l₁ i 𝒟)  = ∧l₁ (η i) (renₛ₊ (keep⊒ η) 𝒟)
renₛ₊ η (∧l₂ i 𝒟)  = ∧l₂ (η i) (renₛ₊ (keep⊒ η) 𝒟)
renₛ₊ η ⊤r        = ⊤r
renₛ₊ η (⊥l i)    = ⊥l (η i)
renₛ₊ η (∨r₁ 𝒟)    = ∨r₁ (renₛ₊ η 𝒟)
renₛ₊ η (∨r₂ 𝒟)    = ∨r₂ (renₛ₊ η 𝒟)
renₛ₊ η (∨l i 𝒟 ℰ) = ∨l (η i) (renₛ₊ (keep⊒ η) 𝒟) (renₛ₊ (keep⊒ η) ℰ)
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
  thm310ₙₘ (lam 𝒟)      = ⊃r (thm310ₙₘ 𝒟)
  thm310ₙₘ (pair 𝒟 ℰ)   = ∧r (thm310ₙₘ 𝒟) (thm310ₙₘ ℰ)
  thm310ₙₘ unit         = ⊤r
  thm310ₙₘ (abort 𝒟)    = thm310ₙₜ 𝒟 (⊥l zero)
  thm310ₙₘ (inl 𝒟)      = ∨r₁ (thm310ₙₘ 𝒟)
  thm310ₙₘ (inr 𝒟)      = ∨r₂ (thm310ₙₘ 𝒟)
  thm310ₙₘ (case 𝒟 ℰ ℱ) = thm310ₙₜ 𝒟 (∨l zero (exₛ₊ (wkₛ₊ (thm310ₙₘ ℰ)))
                                              (exₛ₊ (wkₛ₊ (thm310ₙₘ ℱ))))
  thm310ₙₘ (ent 𝒟)      = thm310ₙₜ 𝒟 vzₛ₊

  thm310ₙₜ : ∀ {Γ A B} → Γ ⊢₊ A neutral → Γ , A ⟹₊ B
                       → Γ ⟹₊ B
  thm310ₙₜ (var i)     ℰ = renₛ₊ (genct⊒ i) ℰ
  thm310ₙₜ (app 𝒟₁ 𝒟₂) ℰ = thm310ₙₜ 𝒟₁ (⊃l zero (wkₛ₊ (thm310ₙₘ 𝒟₂)) (exₛ₊ (wkₛ₊ ℰ)))
  thm310ₙₜ (fst 𝒟)     ℰ = thm310ₙₜ 𝒟 (∧l₁ zero (exₛ₊ (wkₛ₊ ℰ)))
  thm310ₙₜ (snd 𝒟)     ℰ = thm310ₙₜ 𝒟 (∧l₂ zero (exₛ₊ (wkₛ₊ ℰ)))
  thm310ₙₜ (enm 𝒟)     ℰ = cut (thm310ₙₘ 𝒟) ℰ


-- Theorem 3.11 (Admissibility of cut)

-- TODO

postulate
  thm311 : ∀ {A Γ B} → Γ ⟹ A → Γ , A ⟹ B
                     → Γ ⟹ B
-- thm311 𝒟 ℰ = {!!}

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


-- Theorem 3.12 (Cut elimination)

thm312 : ∀ {Γ A} → Γ ⟹₊ A
                 → Γ ⟹ A
thm312 (var i)    = var i
thm312 (⊃r 𝒟)     = ⊃r (thm312 𝒟)
thm312 (⊃l i 𝒟 ℰ) = ⊃l i (thm312 𝒟) (thm312 ℰ)
thm312 (∧r 𝒟 ℰ)   = ∧r (thm312 𝒟) (thm312 ℰ)
thm312 (∧l₁ i 𝒟)  = ∧l₁ i (thm312 𝒟)
thm312 (∧l₂ i 𝒟)  = ∧l₂ i (thm312 𝒟)
thm312 ⊤r        = ⊤r
thm312 (⊥l i)    = ⊥l i
thm312 (∨r₁ 𝒟)    = ∨r₁ (thm312 𝒟)
thm312 (∨r₂ 𝒟)    = ∨r₂ (thm312 𝒟)
thm312 (∨l i 𝒟 ℰ) = ∨l i (thm312 𝒟) (thm312 ℰ)
thm312 (cut 𝒟 ℰ)  = thm311 (thm312 𝒟) (thm312 ℰ)


-- Corollary ??? (Completeness of sequent calculus with respect to natural deduction)

cor312′ : ∀ {Γ A} → Γ ⊢ A true
                  → Γ ⟹ A
cor312′ 𝒟 = thm312 (thm310ₙₘ (thm33ₙₘ 𝒟))

cor312′ₛ : ∀ {Γ A} → Γ ⟹ A
                  → Γ ⟹ A
cor312′ₛ 𝒟 = cor312′ (cor36′ 𝒟)


-- Theorem 3.13 (Normalisation of natural deduction)

thm313 : ∀ {Γ A} → Γ ⊢ A true
                 → Γ ⊢ A normal
thm313 𝒟 = thm36 (cor312′ 𝒟)


-- Corollary 3.14 (Consistency of natural deduction)

cor314 : ¬ (∙ ⊢ ⊥ true)
cor314 𝒟 with cor312′ 𝒟
cor314 𝒟 | var ()
cor314 𝒟 | ⊃l () 𝒟′ ℰ′
cor314 𝒟 | ∧l₁ () 𝒟′
cor314 𝒟 | ∧l₂ () 𝒟′
cor314 𝒟 | ⊥l ()
cor314 𝒟 | ∨l () 𝒟′ ℰ′


-- Corollary 3.15 (Disjunction property of natural deduction)

-- TODO: Existentials for the existential property! Skulls for the skull throne!

cor315ₛ : ∀ {A B} → ∙ ⟹ A ∨ B
                  → ∙ ⟹ A ⊎ ∙ ⟹ B
cor315ₛ 𝒟 with cor312′ₛ 𝒟
cor315ₛ 𝒟 | var ()
cor315ₛ 𝒟 | ⊃l () 𝒟′ ℰ′
cor315ₛ 𝒟 | ∧l₁ () 𝒟′
cor315ₛ 𝒟 | ∧l₂ () 𝒟′
cor315ₛ 𝒟 | ⊥l ()
cor315ₛ 𝒟 | ∨r₁ 𝒟′      = inj₁ 𝒟′
cor315ₛ 𝒟 | ∨r₂ 𝒟′      = inj₂ 𝒟′
cor315ₛ 𝒟 | ∨l () 𝒟′ ℰ′

cor315 : ∀ {A B} → ∙ ⊢ A ∨ B true
                 → ∙ ⊢ A true ⊎ ∙ ⊢ B true
cor315 𝒟 with cor315ₛ (cor312′ 𝒟)
cor315 𝒟 | inj₁ ℰ = inj₁ (cor36′ ℰ)
cor315 𝒟 | inj₂ ℰ = inj₂ (cor36′ ℰ)


-- Corollary 3.16 (Independence of excluded middle)

cor316ₛ : ¬ (∙ ⟹ ι "A" ∨ (~ ι "A"))
cor316ₛ 𝒟 with cor315ₛ 𝒟
cor316ₛ 𝒟 | inj₁ (var ())
cor316ₛ 𝒟 | inj₁ (⊃l () 𝒟′ ℰ′)
cor316ₛ 𝒟 | inj₁ (∧l₁ () 𝒟′)
cor316ₛ 𝒟 | inj₁ (∧l₂ () 𝒟′)
cor316ₛ 𝒟 | inj₁ (⊥l ())
cor316ₛ 𝒟 | inj₁ (∨l () 𝒟′ ℰ′)
cor316ₛ 𝒟 | inj₂ (var ())
cor316ₛ 𝒟 | inj₂ (⊃r (var (suc ())))
cor316ₛ 𝒟 | inj₂ (⊃r (⊃l (suc ()) 𝒟′ ℰ′))
cor316ₛ 𝒟 | inj₂ (⊃r (∧l₁ (suc ()) 𝒟′))
cor316ₛ 𝒟 | inj₂ (⊃r (∧l₂ (suc ()) 𝒟′))
cor316ₛ 𝒟 | inj₂ (⊃r (⊥l (suc ())))
cor316ₛ 𝒟 | inj₂ (⊃r (∨l (suc ()) 𝒟′ ℰ′))
cor316ₛ 𝒟 | inj₂ (⊃l () 𝒟′ ℰ′)
cor316ₛ 𝒟 | inj₂ (∧l₁ () 𝒟′)
cor316ₛ 𝒟 | inj₂ (∧l₂ () 𝒟′)
cor316ₛ 𝒟 | inj₂ (⊥l ())
cor316ₛ 𝒟 | inj₂ (∨l () 𝒟′ ℰ′)

cor316 : ¬ (∙ ⊢ ι "A" ∨ (~ ι "A") true)
cor316 𝒟 = cor316ₛ (cor312′ 𝒟)


--------------------------------------------------------------------------------
