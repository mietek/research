{-# OPTIONS --irrelevant-projections --rewriting #-}

module A201801.SequentCalculusDraftSquasha where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.FullIPLPropositions
open import A201801.FullIPLDerivations hiding (cut)


--------------------------------------------------------------------------------


record Squash {ℓ} (X : Set ℓ) : Set ℓ
  where
    constructor squash
    field
      .proof : X

open Squash public


[List] : Set → Set
[List] X = Squash (List X)


infixl 6 _[,]_
_[,]_ : ∀ {X} → [List] X → X → [List] X
Ξ [,] A = squash (proof Ξ , A)


infix 4 _[∋]_
data _[∋]_ {X} : [List] X → X → Set
  where
    zero : ∀ {A Ξ} → Ξ [,] A [∋] A

    suc : ∀ {B A Ξ} → Ξ [∋] A
                    → Ξ [,] B [∋] A


-- TODO: This is pretty bad
postulate
  [∋]→∋ : ∀ {X A} → {Ξ : List X}
                   → squash Ξ [∋] A
                   → Ξ ∋ A

∋→[∋] : ∀ {X A} → {Ξ : List X}
                 → Ξ ∋ A
                 → squash Ξ [∋] A
∋→[∋] {Ξ = Ξ} zero            = zero {Ξ = squash Ξ}
∋→[∋]         (suc {B = B} i) = suc {B = B} (∋→[∋] i)


--------------------------------------------------------------------------------


-- Function-based inclusion

infix 4 _[⊇]_
_[⊇]_ : ∀ {X} → [List] X → [List] X → Set
Ξ′ [⊇] Ξ = ∀ {A} → Ξ [∋] A → Ξ′ [∋] A

keep[⊇] : ∀ {X A} → {Ξ Ξ′ : [List] X}
                  → Ξ′ [⊇] Ξ
                  → Ξ′ [,] A [⊇] Ξ [,] A
keep[⊇] {Ξ′ = Ξ′} η zero            = zero {Ξ = Ξ′}
keep[⊇]           η (suc {B = B} i) = suc {B = B} (η i)

ex[⊇] : ∀ {X A B} → {Ξ : [List] X}
                  → Ξ [,] B [,] A [⊇] Ξ [,] A [,] B
ex[⊇] {B = B} {Ξ}     zero          = suc {B = B} (zero {Ξ = Ξ})
ex[⊇]         {Ξ = Ξ} (suc zero)    = zero {Ξ = Ξ}
ex[⊇] {B = B}         (suc (suc i)) = suc {B = B} (suc {B = B} i)

ct[⊇] : ∀ {X A} → {Ξ : [List] X}
                → Ξ [,] A [⊇] Ξ [,] A [,] A
ct[⊇] {Ξ = Ξ} zero          = zero {Ξ = Ξ}
ct[⊇] {Ξ = Ξ} (suc zero)    = zero {Ξ = Ξ}
ct[⊇] {A = A} (suc (suc i)) = suc {B = A} i

genct[⊇] : ∀ {X A} → {Ξ : [List] X}
                   → Ξ [∋] A
                   → Ξ [⊇] Ξ [,] A
genct[⊇] {Ξ = Ξ} zero    zero    = zero {Ξ = Ξ}
genct[⊇] {Ξ = Ξ} (suc i) zero    = genct[⊇] i (zero {Ξ = Ξ})
genct[⊇]         i       (suc j) = j


--------------------------------------------------------------------------------


-- Normal/neutral deductions

mutual
  infix 3 _⊢_normal
  data _⊢_normal : Squash (List Form) → Form → Set
    where
      lam : ∀ {A B Γ} → Γ [,] A ⊢ B normal
                      → Γ ⊢ A ⊃ B normal

      pair : ∀ {A B Γ} → Γ ⊢ A normal → Γ ⊢ B normal
                       → Γ ⊢ A ∧ B normal

      unit : ∀ {Γ} → Γ ⊢ 𝟏 normal

      abort : ∀ {A Γ} → Γ ⊢ 𝟎 neutral
                      → Γ ⊢ A normal

      inl : ∀ {A B Γ} → Γ ⊢ A normal
                      → Γ ⊢ A ∨ B normal

      inr : ∀ {A B Γ} → Γ ⊢ B normal
                      → Γ ⊢ A ∨ B normal

      case : ∀ {A B C Γ} → Γ ⊢ A ∨ B neutral → Γ [,] A ⊢ C normal → Γ [,] B ⊢ C normal
                         → Γ ⊢ C normal

      ent : ∀ {A Γ} → Γ ⊢ A neutral
                    → Γ ⊢ A normal

  infix 3 _⊢_neutral
  data _⊢_neutral : Squash (List Form) → Form → Set
    where
      var : ∀ {A Γ} → Γ [∋] A
                    → Γ ⊢ A neutral

      app : ∀ {A B Γ} → Γ ⊢ A ⊃ B neutral → Γ ⊢ A normal
                      → Γ ⊢ B neutral

      fst : ∀ {A B Γ} → Γ ⊢ A ∧ B neutral
                      → Γ ⊢ A neutral

      snd : ∀ {A B Γ} → Γ ⊢ A ∧ B neutral
                      → Γ ⊢ B neutral

infix 3 _⊢_allneutral
_⊢_allneutral : Squash (List Form) → List Form → Set
Γ ⊢ Ξ allneutral = All (Γ ⊢_neutral) Ξ

infix 3 _⊢_allnormal
_⊢_allnormal : Squash (List Form) → List Form → Set
Γ ⊢ Ξ allnormal = All (Γ ⊢_normal) Ξ


mutual
  renₙₘ : ∀ {Γ Γ′ A} → Γ′ [⊇] Γ → Γ ⊢ A normal
                     → Γ′ ⊢ A normal
  renₙₘ η (lam {A} 𝒟)          = lam (renₙₘ (keep[⊇] {A = A} η) 𝒟)
  renₙₘ η (pair 𝒟 ℰ)           = pair (renₙₘ η 𝒟) (renₙₘ η ℰ)
  renₙₘ η unit                 = unit
  renₙₘ η (abort 𝒟)            = abort (renₙₜ η 𝒟)
  renₙₘ η (inl 𝒟)              = inl (renₙₘ η 𝒟)
  renₙₘ η (inr 𝒟)              = inr (renₙₘ η 𝒟)
  renₙₘ η (case {A} {B} 𝒟 ℰ ℱ) = case (renₙₜ η 𝒟) (renₙₘ (keep[⊇] {A = A} η) ℰ) (renₙₘ (keep[⊇] {A = B} η) ℱ)
  renₙₘ η (ent 𝒟)              = ent (renₙₜ η 𝒟)

  renₙₜ : ∀ {Γ Γ′ A} → Γ′ [⊇] Γ → Γ ⊢ A neutral
                     → Γ′ ⊢ A neutral
  renₙₜ η (var i)   = var (η i)
  renₙₜ η (app 𝒟 ℰ) = app (renₙₜ η 𝒟) (renₙₘ η ℰ)
  renₙₜ η (fst 𝒟)   = fst (renₙₜ η 𝒟)
  renₙₜ η (snd 𝒟)   = snd (renₙₜ η 𝒟)


rensₙₜ : ∀ {Γ Γ′ Ξ} → Γ′ [⊇] Γ → Γ ⊢ Ξ allneutral
                    → Γ′ ⊢ Ξ allneutral
rensₙₜ η ξ = maps (renₙₜ η) ξ

wkₙₜ : ∀ {B Γ A} → Γ ⊢ A neutral
                 → Γ [,] B ⊢ A neutral
wkₙₜ {B} 𝒟 = renₙₜ (suc {B = B}) 𝒟

exₙₜ : ∀ {A B Γ C} → Γ [,] A [,] B ⊢ C neutral
                   → Γ [,] B [,] A ⊢ C neutral
exₙₜ {A} {B} {Γ} 𝒟 = renₙₜ (ex[⊇] {A = A} {B} {Γ}) 𝒟

ctₙₜ : ∀ {A Γ C} → Γ [,] A [,] A ⊢ C neutral
                 → Γ [,] A ⊢ C neutral
ctₙₜ {A} {Γ} 𝒟 = renₙₜ (ct[⊇] {A = A} {Γ}) 𝒟

wksₙₜ : ∀ {A Γ Ξ} → Γ ⊢ Ξ allneutral
                  → Γ [,] A ⊢ Ξ allneutral
wksₙₜ {A} ξ = rensₙₜ (suc {B = A}) ξ

vzₙₜ : ∀ {Γ A} → Γ [,] A ⊢ A neutral
vzₙₜ {Γ} = var (zero {Ξ = Γ})

liftsₙₜ : ∀ {A Γ Ξ} → Γ ⊢ Ξ allneutral
                    → Γ [,] A ⊢ Ξ , A allneutral
liftsₙₜ {A} {Γ} ξ = wksₙₜ {A} ξ , vzₙₜ {Γ}

idsₙₜ : ∀ {Γ} → squash Γ ⊢ Γ allneutral
idsₙₜ {∙}     = ∙
idsₙₜ {Γ , A} = liftsₙₜ idsₙₜ


rensₙₘ : ∀ {Γ Γ′ Ξ} → Γ′ [⊇] Γ → Γ ⊢ Ξ allnormal
                    → Γ′ ⊢ Ξ allnormal
rensₙₘ η ξ = maps (renₙₘ η) ξ

wkₙₘ : ∀ {B Γ A} → Γ ⊢ A normal
                 → Γ [,] B ⊢ A normal
wkₙₘ {B} 𝒟 = renₙₘ (suc {B = B}) 𝒟

exₙₘ : ∀ {A B Γ C} → Γ [,] A [,] B ⊢ C normal
                   → Γ [,] B [,] A ⊢ C normal
exₙₘ {A} {B} {Γ} 𝒟 = renₙₘ (ex[⊇] {A = A} {B} {Γ}) 𝒟

ctₙₘ : ∀ {A Γ C} → Γ [,] A [,] A ⊢ C normal
                 → Γ [,] A ⊢ C normal
ctₙₘ {A} {Γ} 𝒟 = renₙₘ (ct[⊇] {A = A} {Γ}) 𝒟

wksₙₘ : ∀ {A Γ Ξ} → Γ ⊢ Ξ allnormal
                  → Γ [,] A ⊢ Ξ allnormal
wksₙₘ {A} ξ = rensₙₘ (suc {B = A}) ξ

vzₙₘ : ∀ {Γ A} → Γ [,] A ⊢ A normal
vzₙₘ {Γ} = ent (vzₙₜ {Γ})

liftsₙₘ : ∀ {A Γ Ξ} → Γ ⊢ Ξ allnormal
                    → Γ [,] A ⊢ Ξ , A allnormal
liftsₙₘ {A} {Γ} ξ = wksₙₘ {A} ξ , vzₙₘ {Γ}

idsₙₘ : ∀ {Γ} → squash Γ ⊢ Γ allnormal
idsₙₘ {∙}     = ∙
idsₙₘ {Γ , A} = liftsₙₘ idsₙₘ


-- Lemma 3.5 (Substitution property of normal/neutral deductions)

mutual
  subₙₘ : ∀ {Γ Ξ A} → Γ ⊢ Ξ allneutral → squash Ξ ⊢ A normal
                    → Γ ⊢ A normal
  subₙₘ ξ (lam {A} 𝒟)          = lam (subₙₘ (liftsₙₜ {A} ξ) 𝒟)
  subₙₘ ξ (pair 𝒟 ℰ)           = pair (subₙₘ ξ 𝒟) (subₙₘ ξ ℰ)
  subₙₘ ξ unit                 = unit
  subₙₘ ξ (abort 𝒟)            = abort (subₙₜ ξ 𝒟)
  subₙₘ ξ (inl 𝒟)              = inl (subₙₘ ξ 𝒟)
  subₙₘ ξ (inr 𝒟)              = inr (subₙₘ ξ 𝒟)
  subₙₘ ξ (case {A} {B} 𝒟 ℰ ℱ) = case (subₙₜ ξ 𝒟) (subₙₘ (liftsₙₜ {A} ξ) ℰ) (subₙₘ (liftsₙₜ {B} ξ) ℱ)
  subₙₘ ξ (ent 𝒟)              = ent (subₙₜ ξ 𝒟)

  subₙₜ : ∀ {Γ Ξ A} → Γ ⊢ Ξ allneutral → squash Ξ ⊢ A neutral
                    → Γ ⊢ A neutral
  subₙₜ ξ (var i)   = get ξ ([∋]→∋ i)
  subₙₜ ξ (app 𝒟 ℰ) = app (subₙₜ ξ 𝒟) (subₙₘ ξ ℰ)
  subₙₜ ξ (fst 𝒟)   = fst (subₙₜ ξ 𝒟)
  subₙₜ ξ (snd 𝒟)   = snd (subₙₜ ξ 𝒟)

cutₙₘ : ∀ {Γ A B} → squash Γ ⊢ A neutral → squash Γ [,] A ⊢ B normal
                  → squash Γ ⊢ B normal
cutₙₘ {Γ} 𝒟 ℰ = subₙₘ (_,_ {Ξ = Γ} idsₙₜ 𝒟) ℰ


-- Theorem 3.1 (Soundness of normal/neutral deductions with respect to natural deduction)

mutual
  thm31ₙₘ : ∀ {Γ A} → squash Γ ⊢ A normal
                    → Γ ⊢ A true
  thm31ₙₘ (lam 𝒟)      = lam (thm31ₙₘ 𝒟)
  thm31ₙₘ (pair 𝒟 ℰ)   = pair (thm31ₙₘ 𝒟) (thm31ₙₘ ℰ)
  thm31ₙₘ unit         = unit
  thm31ₙₘ (abort 𝒟)    = abort (thm31ₙₜ 𝒟)
  thm31ₙₘ (inl 𝒟)      = inl (thm31ₙₘ 𝒟)
  thm31ₙₘ (inr 𝒟)      = inr (thm31ₙₘ 𝒟)
  thm31ₙₘ (case 𝒟 ℰ ℱ) = case (thm31ₙₜ 𝒟) (thm31ₙₘ ℰ) (thm31ₙₘ ℱ)
  thm31ₙₘ (ent 𝒟)      = thm31ₙₜ 𝒟

  thm31ₙₜ : ∀ {Γ A} → squash Γ ⊢ A neutral
                    → Γ ⊢ A true
  thm31ₙₜ (var i)   = var ([∋]→∋ i)
  thm31ₙₜ (app 𝒟 ℰ) = app (thm31ₙₜ 𝒟) (thm31ₙₘ ℰ)
  thm31ₙₜ (fst 𝒟)   = fst (thm31ₙₜ 𝒟)
  thm31ₙₜ (snd 𝒟)   = snd (thm31ₙₜ 𝒟)


--------------------------------------------------------------------------------


-- Annotated normal/neutral deductions

mutual
  infix 3 _⊢₊_normal
  data _⊢₊_normal : [List] Form → Form → Set
    where
      lam : ∀ {A B Γ} → Γ [,] A ⊢₊ B normal
                      → Γ ⊢₊ A ⊃ B normal

      pair : ∀ {A B Γ} → Γ ⊢₊ A normal → Γ ⊢₊ B normal
                       → Γ ⊢₊ A ∧ B normal

      unit : ∀ {Γ} → Γ ⊢₊ 𝟏 normal

      abort : ∀ {A Γ} → Γ ⊢₊ 𝟎 neutral
                      → Γ ⊢₊ A normal

      inl : ∀ {A B Γ} → Γ ⊢₊ A normal
                      → Γ ⊢₊ A ∨ B normal

      inr : ∀ {A B Γ} → Γ ⊢₊ B normal
                      → Γ ⊢₊ A ∨ B normal

      case : ∀ {A B C Γ} → Γ ⊢₊ A ∨ B neutral → Γ [,] A ⊢₊ C normal → Γ [,] B ⊢₊ C normal
                         → Γ ⊢₊ C normal

      ent : ∀ {A Γ} → Γ ⊢₊ A neutral
                    → Γ ⊢₊ A normal

  infix 3 _⊢₊_neutral
  data _⊢₊_neutral : [List] Form → Form → Set
    where
      var : ∀ {A Γ} → Γ [∋] A
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
_⊢₊_allneutral : [List] Form → List Form → Set
Γ ⊢₊ Ξ allneutral = All (Γ ⊢₊_neutral) Ξ

infix 3 _⊢₊_allnormal
_⊢₊_allnormal : [List] Form → List Form → Set
Γ ⊢₊ Ξ allnormal = All (Γ ⊢₊_normal) Ξ


mutual
  renₙₘ₊ : ∀ {Γ Γ′ A} → Γ′ [⊇] Γ → Γ ⊢₊ A normal
                      → Γ′ ⊢₊ A normal
  renₙₘ₊ η (lam {A} 𝒟)          = lam (renₙₘ₊ (keep[⊇] {A = A}η) 𝒟)
  renₙₘ₊ η (pair 𝒟 ℰ)           = pair (renₙₘ₊ η 𝒟) (renₙₘ₊ η ℰ)
  renₙₘ₊ η unit                 = unit
  renₙₘ₊ η (abort 𝒟)            = abort (renₙₜ₊ η 𝒟)
  renₙₘ₊ η (inl 𝒟)              = inl (renₙₘ₊ η 𝒟)
  renₙₘ₊ η (inr 𝒟)              = inr (renₙₘ₊ η 𝒟)
  renₙₘ₊ η (case {A} {B} 𝒟 ℰ ℱ) = case (renₙₜ₊ η 𝒟) (renₙₘ₊ (keep[⊇] {A = A} η) ℰ) (renₙₘ₊ (keep[⊇] {A = B} η) ℱ)
  renₙₘ₊ η (ent 𝒟)              = ent (renₙₜ₊ η 𝒟)

  renₙₜ₊ : ∀ {Γ Γ′ A} → Γ′ [⊇] Γ → Γ ⊢₊ A neutral
                      → Γ′ ⊢₊ A neutral
  renₙₜ₊ η (var i)   = var (η i)
  renₙₜ₊ η (app 𝒟 ℰ) = app (renₙₜ₊ η 𝒟) (renₙₘ₊ η ℰ)
  renₙₜ₊ η (fst 𝒟)   = fst (renₙₜ₊ η 𝒟)
  renₙₜ₊ η (snd 𝒟)   = snd (renₙₜ₊ η 𝒟)
  renₙₜ₊ η (enm 𝒟)   = enm (renₙₘ₊ η 𝒟)


rensₙₜ₊ : ∀ {Γ Γ′ Ξ} → Γ′ [⊇] Γ → Γ ⊢₊ Ξ allneutral
                     → Γ′ ⊢₊ Ξ allneutral
rensₙₜ₊ η ξ = maps (renₙₜ₊ η) ξ

wkₙₜ₊ : ∀ {B Γ A} → Γ ⊢₊ A neutral
                  → Γ [,] B ⊢₊ A neutral
wkₙₜ₊ {B} 𝒟 = renₙₜ₊ (suc {B = B}) 𝒟

exₙₜ₊ : ∀ {A B Γ C} → Γ [,] A [,] B ⊢₊ C neutral
                    → Γ [,] B [,] A ⊢₊ C neutral
exₙₜ₊ {A} {B} {Γ} 𝒟 = renₙₜ₊ (ex[⊇] {A = A} {B} {Γ}) 𝒟

ctₙₜ₊ : ∀ {A Γ C} → Γ [,] A [,] A ⊢₊ C neutral
                  → Γ [,] A ⊢₊ C neutral
ctₙₜ₊ {A} {Γ} 𝒟 = renₙₜ₊ (ct[⊇] {A = A} {Γ}) 𝒟

wksₙₜ₊ : ∀ {A Γ Ξ} → Γ ⊢₊ Ξ allneutral
                   → Γ [,] A ⊢₊ Ξ allneutral
wksₙₜ₊ {A} ξ = rensₙₜ₊ (suc {B = A}) ξ

vzₙₜ₊ : ∀ {Γ A} → Γ [,] A ⊢₊ A neutral
vzₙₜ₊ {Γ} = var (zero {Ξ = Γ})

liftsₙₜ₊ : ∀ {A Γ Ξ} → Γ ⊢₊ Ξ allneutral
                     → Γ [,] A ⊢₊ Ξ , A allneutral
liftsₙₜ₊ {A} {Γ} ξ = wksₙₜ₊ {A} ξ , vzₙₜ₊ {Γ}

idsₙₜ₊ : ∀ {Γ} → squash Γ ⊢₊ Γ allneutral
idsₙₜ₊ {∙}     = ∙
idsₙₜ₊ {Γ , A} = liftsₙₜ₊ idsₙₜ₊


rensₙₘ₊ : ∀ {Γ Γ′ Ξ} → Γ′ [⊇] Γ → Γ ⊢₊ Ξ allnormal
                     → Γ′ ⊢₊ Ξ allnormal
rensₙₘ₊ η ξ = maps (renₙₘ₊ η) ξ

wkₙₘ₊ : ∀ {B Γ A} → Γ ⊢₊ A normal
                  → Γ [,] B ⊢₊ A normal
wkₙₘ₊ {B} 𝒟 = renₙₘ₊ (suc {B = B}) 𝒟

exₙₘ₊ : ∀ {A B Γ C} → Γ [,] A [,] B ⊢₊ C normal
                    → Γ [,] B [,] A ⊢₊ C normal
exₙₘ₊ {A} {B} {Γ} 𝒟 = renₙₘ₊ (ex[⊇] {A = A} {B} {Γ}) 𝒟

ctₙₘ₊ : ∀ {A Γ C} → Γ [,] A [,] A ⊢₊ C normal
                  → Γ [,] A ⊢₊ C normal
ctₙₘ₊ {A} {Γ} 𝒟 = renₙₘ₊ (ct[⊇] {A = A} {Γ}) 𝒟

wksₙₘ₊ : ∀ {A Γ Ξ} → Γ ⊢₊ Ξ allnormal
                   → Γ [,] A ⊢₊ Ξ allnormal
wksₙₘ₊ {A} ξ = rensₙₘ₊ (suc {B = A}) ξ

vzₙₘ₊ : ∀ {Γ A} → Γ [,] A ⊢₊ A normal
vzₙₘ₊ {Γ} = ent (vzₙₜ₊ {Γ})

liftsₙₘ₊ : ∀ {A Γ Ξ} → Γ ⊢₊ Ξ allnormal
                     → Γ [,] A ⊢₊ Ξ , A allnormal
liftsₙₘ₊ {A} {Γ} ξ = wksₙₘ₊ {A} ξ , vzₙₘ₊ {Γ}

idsₙₘ₊ : ∀ {Γ} → squash Γ ⊢₊ Γ allnormal
idsₙₘ₊ {∙}     = ∙
idsₙₘ₊ {Γ , A} = liftsₙₘ₊ idsₙₘ₊


-- Lemma ??? (Substitution property of annotated normal/neutral deductions)

mutual
  subₙₘ₊ : ∀ {Γ Ξ A} → Γ ⊢₊ Ξ allneutral → squash Ξ ⊢₊ A normal
                     → Γ ⊢₊ A normal
  subₙₘ₊ ξ (lam {A} 𝒟)          = lam (subₙₘ₊ (liftsₙₜ₊ {A} ξ) 𝒟)
  subₙₘ₊ ξ (pair 𝒟 ℰ)           = pair (subₙₘ₊ ξ 𝒟) (subₙₘ₊ ξ ℰ)
  subₙₘ₊ ξ unit                 = unit
  subₙₘ₊ ξ (abort 𝒟)            = abort (subₙₜ₊ ξ 𝒟)
  subₙₘ₊ ξ (inl 𝒟)              = inl (subₙₘ₊ ξ 𝒟)
  subₙₘ₊ ξ (inr 𝒟)              = inr (subₙₘ₊ ξ 𝒟)
  subₙₘ₊ ξ (case {A} {B} 𝒟 ℰ ℱ) = case (subₙₜ₊ ξ 𝒟) (subₙₘ₊ (liftsₙₜ₊ {A} ξ) ℰ) (subₙₘ₊ (liftsₙₜ₊ {B} ξ) ℱ)
  subₙₘ₊ ξ (ent 𝒟)              = ent (subₙₜ₊ ξ 𝒟)

  subₙₜ₊ : ∀ {Γ Ξ A} → Γ ⊢₊ Ξ allneutral → squash Ξ ⊢₊ A neutral
                     → Γ ⊢₊ A neutral
  subₙₜ₊ ξ (var i)   = get ξ ([∋]→∋ i)
  subₙₜ₊ ξ (app 𝒟 ℰ) = app (subₙₜ₊ ξ 𝒟) (subₙₘ₊ ξ ℰ)
  subₙₜ₊ ξ (fst 𝒟)   = fst (subₙₜ₊ ξ 𝒟)
  subₙₜ₊ ξ (snd 𝒟)   = snd (subₙₜ₊ ξ 𝒟)
  subₙₜ₊ ξ (enm 𝒟)   = enm (subₙₘ₊ ξ 𝒟)

cutₙₘ₊ : ∀ {Γ A B} → squash Γ ⊢₊ A neutral → squash Γ [,] A ⊢₊ B normal
                   → squash Γ ⊢₊ B normal
cutₙₘ₊ {Γ} 𝒟 ℰ = subₙₘ₊ (_,_ {Ξ = Γ} idsₙₜ₊ 𝒟) ℰ

pseudocutₙₘ₊ : ∀ {Γ A B} → squash Γ ⊢₊ A normal → squash Γ [,] A ⊢₊ B normal
                         → squash Γ ⊢₊ B normal
pseudocutₙₘ₊ 𝒟 ℰ = ent (app (enm (lam ℰ)) 𝒟)


-- Theorem 3.2 (Soundness of annotated normal/neutral deductions with respect to natural deduction)

mutual
  thm32ₙₘ : ∀ {Γ A} → squash Γ ⊢₊ A normal
                    → Γ ⊢ A true
  thm32ₙₘ (lam 𝒟)      = lam (thm32ₙₘ 𝒟)
  thm32ₙₘ (pair 𝒟 ℰ)   = pair (thm32ₙₘ 𝒟) (thm32ₙₘ ℰ)
  thm32ₙₘ unit         = unit
  thm32ₙₘ (abort 𝒟)    = abort (thm32ₙₜ 𝒟)
  thm32ₙₘ (inl 𝒟)      = inl (thm32ₙₘ 𝒟)
  thm32ₙₘ (inr 𝒟)      = inr (thm32ₙₘ 𝒟)
  thm32ₙₘ (case 𝒟 ℰ ℱ) = case (thm32ₙₜ 𝒟) (thm32ₙₘ ℰ) (thm32ₙₘ ℱ)
  thm32ₙₘ (ent 𝒟)      = thm32ₙₜ 𝒟

  thm32ₙₜ : ∀ {Γ A} → squash Γ ⊢₊ A neutral
                    → Γ ⊢ A true
  thm32ₙₜ (var i)   = var ([∋]→∋ i)
  thm32ₙₜ (app 𝒟 ℰ) = app (thm32ₙₜ 𝒟) (thm32ₙₘ ℰ)
  thm32ₙₜ (fst 𝒟)   = fst (thm32ₙₜ 𝒟)
  thm32ₙₜ (snd 𝒟)   = snd (thm32ₙₜ 𝒟)
  thm32ₙₜ (enm 𝒟)   = thm32ₙₘ 𝒟


-- Theorem 3.3 (Completeness of annotated normal/neutral deductions with respect to natural deduction)

thm33ₙₘ : ∀ {Γ A} → Γ ⊢ A true
                  → squash Γ ⊢₊ A normal
thm33ₙₘ (var i)      = ent (var (∋→[∋] i))
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
                  → squash Γ ⊢₊ A neutral
thm33ₙₜ (var i)      = var (∋→[∋] i)
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
