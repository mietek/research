-- Based on http://www.cs.cmu.edu/~fp/courses/atp/handouts/ch3-seqcalc.pdf

-- NOTE: The direction of ₗ/ᵣ in previous code is wrong compared to Pfenning

-- NOTE: The direction of ⇑/⇓ in previous code is wrong compared to Filinski 

module IPLBidirectionalDerivationsForCutElimination where

open import Prelude
open import Category
open import List
open import ListLemmas
-- open import IPLPropositions
-- open import IPLDerivations


--------------------------------------------------------------------------------


infixr 8 _⊃_
data Prop : Set
  where
    ι_  : String → Prop
    _⊃_ : Prop → Prop → Prop
    _∧_ : Prop → Prop → Prop
    ⊤  : Prop
    ⊥  : Prop
    _∨_ : Prop → Prop → Prop


infix 3 _⊢_true
data _⊢_true : List Prop → Prop → Set
  where
    var : ∀ {A Γ} → Γ ∋ A
                  → Γ ⊢ A true

    lam : ∀ {A B Γ} → Γ , A ⊢ B true
                    → Γ ⊢ A ⊃ B true

    app : ∀ {A B Γ} → Γ ⊢ A ⊃ B true → Γ ⊢ A true
                    → Γ ⊢ B true


--------------------------------------------------------------------------------


-- Normal/neutral deductions

mutual
  infix 3 _⊢_normal
  data _⊢_normal : List Prop → Prop → Set
    where
      lam : ∀ {A B Γ} → Γ , A ⊢ B normal
                      → Γ ⊢ A ⊃ B normal

      neu : ∀ {A Γ} → Γ ⊢ A neutral
                    → Γ ⊢ A normal

  infix 3 _⊢_neutral
  data _⊢_neutral : List Prop → Prop → Set
    where
      var : ∀ {A Γ} → Γ ∋ A
                    → Γ ⊢ A neutral

      app : ∀ {A B Γ} → Γ ⊢ A ⊃ B neutral → Γ ⊢ A normal
                      → Γ ⊢ B neutral


mutual
  renᵣ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A normal
                    → Γ′ ⊢ A normal
  renᵣ η (lam 𝒟) = lam (renᵣ (keep η) 𝒟)
  renᵣ η (neu 𝒟) = neu (renₗ η 𝒟)

  renₗ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A neutral
                    → Γ′ ⊢ A neutral
  renₗ η (var i)   = var (ren∋ η i)
  renₗ η (app 𝒟 ℰ) = app (renₗ η 𝒟) (renᵣ η ℰ)


wkₗ : ∀ {B Γ A} → Γ ⊢ A neutral
                → Γ , B ⊢ A neutral
wkₗ 𝒟 = renₗ (drop id) 𝒟


vzₗ : ∀ {Γ A} → Γ , A ⊢ A neutral
vzₗ = var zero


-- Theorem 3.1 (Soundness of normal/neutral deductions with respect to natural deduction)

mutual
  thm31ᵣ : ∀ {Γ A} → Γ ⊢ A normal
                   → Γ ⊢ A true
  thm31ᵣ (lam 𝒟) = lam (thm31ᵣ 𝒟)
  thm31ᵣ (neu 𝒟) = thm31ₗ 𝒟

  thm31ₗ : ∀ {Γ A} → Γ ⊢ A neutral
                   → Γ ⊢ A true
  thm31ₗ (var i)   = var i
  thm31ₗ (app 𝒟 ℰ) = app (thm31ₗ 𝒟) (thm31ᵣ ℰ)


--------------------------------------------------------------------------------


-- Annotated normal/neutral deductions

mutual
  infix 3 _⊢₊_normal
  data _⊢₊_normal : List Prop → Prop → Set
    where
      lam : ∀ {A B Γ} → Γ , A ⊢₊ B normal
                      → Γ ⊢₊ A ⊃ B normal

      neu : ∀ {A Γ} → Γ ⊢₊ A neutral
                    → Γ ⊢₊ A normal

  infix 3 _⊢₊_neutral
  data _⊢₊_neutral : List Prop → Prop → Set
    where
      var : ∀ {A Γ} → Γ ∋ A
                    → Γ ⊢₊ A neutral

      app : ∀ {A B Γ} → Γ ⊢₊ A ⊃ B neutral → Γ ⊢₊ A normal
                      → Γ ⊢₊ B neutral

      ann : ∀ {A Γ} → Γ ⊢₊ A normal
                    → Γ ⊢₊ A neutral


mutual
  renᵣ₊ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢₊ A normal
                     → Γ′ ⊢₊ A normal
  renᵣ₊ η (lam 𝒟) = lam (renᵣ₊ (keep η) 𝒟)
  renᵣ₊ η (neu 𝒟) = neu (renₗ₊ η 𝒟)

  renₗ₊ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢₊ A neutral
                     → Γ′ ⊢₊ A neutral
  renₗ₊ η (var i)   = var (ren∋ η i)
  renₗ₊ η (app 𝒟 ℰ) = app (renₗ₊ η 𝒟) (renᵣ₊ η ℰ)
  renₗ₊ η (ann 𝒟)   = ann (renᵣ₊ η 𝒟)


wkₗ₊ : ∀ {B Γ A} → Γ ⊢₊ A neutral
                 → Γ , B ⊢₊ A neutral
wkₗ₊ 𝒟 = renₗ₊ (drop id) 𝒟


vzₗ₊ : ∀ {Γ A} → Γ , A ⊢₊ A neutral
vzₗ₊ = var zero


-- Theorem 3.2 (Soundness of annotated normal/neutral deductions with respect to natural deduction)

mutual
  thm32ᵣ₊ : ∀ {Γ A} → Γ ⊢₊ A normal
                    → Γ ⊢ A true
  thm32ᵣ₊ (lam 𝒟) = lam (thm32ᵣ₊ 𝒟)
  thm32ᵣ₊ (neu 𝒟) = thm32ₗ₊ 𝒟

  thm32ₗ₊ : ∀ {Γ A} → Γ ⊢₊ A neutral
                    → Γ ⊢ A true
  thm32ₗ₊ (var i)   = var i
  thm32ₗ₊ (app 𝒟 ℰ) = app (thm32ₗ₊ 𝒟) (thm32ᵣ₊ ℰ)
  thm32ₗ₊ (ann 𝒟)   = thm32ᵣ₊ 𝒟


-- Theorem 3.3 (Completeness of annotated normal/neutral deductions with respect to natural deduction)

thm33ᵣ₊ : ∀ {Γ A} → Γ ⊢ A true
                  → Γ ⊢₊ A normal
thm33ᵣ₊ (var i)   = neu (var i)
thm33ᵣ₊ (lam 𝒟)   = lam (thm33ᵣ₊ 𝒟)
thm33ᵣ₊ (app 𝒟 ℰ) = neu (app (ann (thm33ᵣ₊ 𝒟)) (thm33ᵣ₊ ℰ))

thm33ₗ₊ : ∀ {Γ A} → Γ ⊢ A true
                  → Γ ⊢₊ A neutral
thm33ₗ₊ (var i)   = var i
thm33ₗ₊ (lam 𝒟)   = ann (lam (neu (thm33ₗ₊ 𝒟)))
thm33ₗ₊ (app 𝒟 ℰ) = app (thm33ₗ₊ 𝒟) (neu (thm33ₗ₊ ℰ))


--------------------------------------------------------------------------------


-- McBride's context deletions

_-_ : ∀ {X A} → (Ξ : List X) → Ξ ∋ A → List X
∙       - ()
(Ξ , A) - zero  = Ξ
(Ξ , B) - suc i = (Ξ - i) , B


del⊇ : ∀ {X A} → {Ξ : List X}
               → (i : Ξ ∋ A)
               → Ξ ⊇ Ξ - i
del⊇ zero    = drop id⊇
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


--------------------------------------------------------------------------------


-- Sequent calculus

mutual
  infix 3 _⟹_
  data _⟹_ : List Prop → Prop → Set
    where
      vzₛ : ∀ {A Γ} → Γ , A ⟹ A 
      
      ⊃r : ∀ {A B Γ} → Γ , A ⟹ B
                     → Γ ⟹ A ⊃ B

      ⊃l : ∀ {A B C Γ} → Γ , A ⊃ B ⟹ A → Γ , A ⊃ B , B ⟹ C
                       → Γ , A ⊃ B ⟹ C


-- Lemma 3.5 (Substitution property for normal/neutral deductions)

mutual
  subᵣ : ∀ {Γ A B} → (i : Γ ∋ A) → Γ - i ⊢ A neutral → Γ ⊢ B normal
                   → Γ - i ⊢ B normal
  subᵣ i 𝒞 (lam 𝒟) = lam (subᵣ (suc i) (renₗ (drop id⊇) 𝒞) 𝒟)
  subᵣ i 𝒞 (neu 𝒟) = neu (subₗ i 𝒞 𝒟)

  subₗ : ∀ {Γ A B} → (i : Γ ∋ A) → Γ - i ⊢ A neutral → Γ ⊢ B neutral
                   → Γ - i ⊢ B neutral
  subₗ i 𝒞 (var j)   with i ≟∋ j
  subₗ i 𝒞 (var .i)  | same .i   = 𝒞
  subₗ i 𝒞 (var ._)  | diff .i j = var j
  subₗ i 𝒞 (app 𝒟 ℰ) = app (subₗ i 𝒞 𝒟) (subᵣ i 𝒞 ℰ)


-- Theorem 3.6 (Soundness of sequent calculus with respect to normal deduction)

thm36 : ∀ {Γ A} → Γ ⟹ A
                → Γ ⊢ A normal
thm36 vzₛ      = neu (var zero)
thm36 (⊃r 𝒟)   = lam (thm36 𝒟)
thm36 (⊃l 𝒟 ℰ) = subᵣ zero (app (var zero) (thm36 𝒟)) (thm36 ℰ)


-- Lemma 3.7 (Structural properties of sequent calculus)

-- TODO: Do we need these as primitives?

postulate
  wkₛ : ∀ {B Γ A} → Γ ⟹ A
                  → Γ , B ⟹ A

  ctₛ : ∀ {Γ A B} → Γ , A , A ⟹ B
                  → Γ , A ⟹ B

  exₛ : ∀ {Γ A B C} → Γ , A , B ⟹ C
                    → Γ , B , A ⟹ C


-- Theorem 3.8 (Completeness of sequent calculus with respect to normal/neutral deductions)

-- TODO: ???

postulate
  thm38∋ : ∀ {Γ A B} → Γ ∋ A → Γ , A ⟹ B
                     → Γ ⟹ B
-- thm38∋ zero    𝒟        = ctₛ 𝒟
-- thm38∋ (suc i) vzₛ      = wkₛ (thm38∋ i vzₛ)
-- thm38∋ (suc i) (⊃r 𝒟)   = ⊃r (thm38∋ (suc (suc i)) (exₛ 𝒟))
-- thm38∋ (suc i) (⊃l 𝒟 ℰ) = {!⊃l ? ℰ!}

mutual
  thm38ᵣ : ∀ {Γ A} → Γ ⊢ A normal
                   → Γ ⟹ A
  thm38ᵣ (lam 𝒟) = ⊃r (thm38ᵣ 𝒟)
  thm38ᵣ (neu 𝒟)  = thm38ₗ 𝒟 vzₛ

  thm38ₗ : ∀ {Γ A B} → Γ ⊢ A neutral → Γ , A ⟹ B
                     → Γ ⟹ B
  thm38ₗ (var i)     ℰ = thm38∋ i ℰ
  thm38ₗ (app 𝒟₁ 𝒟₂) ℰ = thm38ₗ 𝒟₁ (⊃l (wkₛ (thm38ᵣ 𝒟₂)) (exₛ (wkₛ ℰ)))


--------------------------------------------------------------------------------


-- Sequent calculus with cut

mutual
  infix 3 _⟹₊_
  data _⟹₊_ : List Prop → Prop → Set
    where
      vzₛ : ∀ {A Γ} → Γ , A ⟹₊ A 
      
      ⊃r : ∀ {A B Γ} → Γ , A ⟹₊ B
                     → Γ ⟹₊ A ⊃ B

      ⊃l : ∀ {A B C Γ} → Γ , A ⊃ B ⟹₊ A → Γ , A ⊃ B , B ⟹₊ C
                       → Γ , A ⊃ B ⟹₊ C

      cutₛ : ∀ {A B Γ} → Γ ⟹₊ A → Γ , A ⟹₊ B
                       → Γ ⟹₊ B


-- Lemma ??? (Substitution property for annotated normal/neutral deductions)

mutual
  subᵣ₊ : ∀ {Γ A B} → (i : Γ ∋ A) → Γ - i ⊢₊ A neutral → Γ ⊢₊ B normal
                    → Γ - i ⊢₊ B normal
  subᵣ₊ i 𝒞 (lam 𝒟) = lam (subᵣ₊ (suc i) (renₗ₊ (drop id⊇) 𝒞) 𝒟)
  subᵣ₊ i 𝒞 (neu 𝒟) = neu (subₗ₊ i 𝒞 𝒟)

  subₗ₊ : ∀ {Γ A B} → (i : Γ ∋ A) → Γ - i ⊢₊ A neutral → Γ ⊢₊ B neutral
                    → Γ - i ⊢₊ B neutral
  subₗ₊ i 𝒞 (var j)   with i ≟∋ j
  subₗ₊ i 𝒞 (var .i)  | same .i   = 𝒞
  subₗ₊ i 𝒞 (var ._)  | diff .i j = var j
  subₗ₊ i 𝒞 (app 𝒟 ℰ) = app (subₗ₊ i 𝒞 𝒟) (subᵣ₊ i 𝒞 ℰ)
  subₗ₊ i 𝒞 (ann 𝒟)   = ann (subᵣ₊ i 𝒞 𝒟)


-- Alternative?

pseudosubᵣ₊ : ∀ {Γ A B} → Γ ⊢₊ A normal → Γ , A ⊢₊ B normal
                        → Γ ⊢₊ B normal
pseudosubᵣ₊ 𝒟 ℰ = neu (app (ann (lam ℰ)) 𝒟)

pseudosubₗ₊ : ∀ {Γ A B} → Γ ⊢₊ A neutral → Γ , A ⊢₊ B neutral
                        → Γ ⊢₊ B neutral
pseudosubₗ₊ 𝒟 ℰ = app (ann (lam (neu ℰ))) (neu 𝒟)


-- Theorem 3.9 (Soundness of sequent calculus with cut with respect to annotated normal deductions)

mutual
  thm39ᵣ₊ : ∀ {Γ A} → Γ ⟹₊ A
                    → Γ ⊢₊ A normal
  thm39ᵣ₊ vzₛ        = neu vzₗ₊
  thm39ᵣ₊ (⊃r 𝒟)     = lam (thm39ᵣ₊ 𝒟)
  thm39ᵣ₊ (⊃l 𝒟 ℰ)   = subᵣ₊ zero (app (var zero) (thm39ᵣ₊ 𝒟)) (thm39ᵣ₊ ℰ)
  thm39ᵣ₊ (cutₛ 𝒟 ℰ) = subᵣ₊ zero (thm39ₗ₊ 𝒟) (thm39ᵣ₊ ℰ)
   
  thm39ₗ₊ : ∀ {Γ A} → Γ ⟹₊ A
                    → Γ ⊢₊ A neutral
  thm39ₗ₊ vzₛ        = vzₗ₊
  thm39ₗ₊ (⊃r 𝒟)     = ann (lam (neu (thm39ₗ₊ 𝒟)))
  thm39ₗ₊ (⊃l 𝒟 ℰ)   = subₗ₊ zero (app (var zero) (neu (thm39ₗ₊ 𝒟))) (thm39ₗ₊ ℰ)
  thm39ₗ₊ (cutₛ 𝒟 ℰ) = subₗ₊ zero (thm39ₗ₊ 𝒟) (thm39ₗ₊ ℰ)

module Alternative
  where
    athm39ᵣ₊ : ∀ {Γ A} → Γ ⟹₊ A
                       → Γ ⊢₊ A normal
    athm39ᵣ₊ vzₛ        = neu vzₗ₊
    athm39ᵣ₊ (⊃r 𝒟)     = lam (athm39ᵣ₊ 𝒟)
    athm39ᵣ₊ (⊃l 𝒟 ℰ)   = pseudosubᵣ₊ (neu (app (var zero) (athm39ᵣ₊ 𝒟))) (athm39ᵣ₊ ℰ)
    athm39ᵣ₊ (cutₛ 𝒟 ℰ) = pseudosubᵣ₊ (athm39ᵣ₊ 𝒟) (athm39ᵣ₊ ℰ)
     
    athm39ₗ₊ : ∀ {Γ A} → Γ ⟹₊ A
                       → Γ ⊢₊ A neutral
    athm39ₗ₊ vzₛ        = vzₗ₊
    athm39ₗ₊ (⊃r 𝒟)     = ann (lam (neu (athm39ₗ₊ 𝒟)))
    athm39ₗ₊ (⊃l 𝒟 ℰ)   = pseudosubₗ₊ (app (var zero) (neu (athm39ₗ₊ 𝒟))) (athm39ₗ₊ ℰ)
    athm39ₗ₊ (cutₛ 𝒟 ℰ) = pseudosubₗ₊ (athm39ₗ₊ 𝒟) (athm39ₗ₊ ℰ)


-- Lemma ??? (Structural properties of sequent calculus with cut)

-- TODO: Do we need these as primitives?

postulate
  wkₛ₊ : ∀ {B Γ A} → Γ ⟹₊ A
                   → Γ , B ⟹₊ A

  ctₛ₊ : ∀ {Γ A B} → Γ , A , A ⟹₊ B
                   → Γ , A ⟹₊ B

  exₛ₊ : ∀ {Γ A B C} → Γ , A , B ⟹₊ C
                     → Γ , B , A ⟹₊ C


-- Theorem 3.10 (Completeness of sequent calculus with cut with respect to annotated normal/neutral deductions)

-- TODO: ???

postulate
  thm310∋ : ∀ {Γ A B} → Γ ∋ A → Γ , A ⟹₊ B
                      → Γ ⟹₊ B
-- thm310∋ zero    𝒟          = ctₛ₊ 𝒟
-- thm310∋ (suc i) vzₛ        = wkₛ₊ (thm310∋ i vzₛ)
-- thm310∋ (suc i) (⊃r 𝒟)     = ⊃r (thm310∋ (suc (suc i)) (exₛ₊ 𝒟))
-- thm310∋ (suc i) (⊃l 𝒟 ℰ)   = {!⊃l ? ℰ!}
-- thm310∋ (suc i) (cutₛ 𝒟 ℰ) = {!cutₛ 𝒟 ℰ!}

mutual
  thm310ᵣ₊ : ∀ {Γ A} → Γ ⊢₊ A normal
                     → Γ ⟹₊ A
  thm310ᵣ₊ (lam 𝒟) = ⊃r (thm310ᵣ₊ 𝒟)
  thm310ᵣ₊ (neu 𝒟) = thm310ₗ₊ 𝒟 vzₛ

  thm310ₗ₊ : ∀ {Γ A B} → Γ ⊢₊ A neutral → Γ , A ⟹₊ B
                       → Γ ⟹₊ B
  thm310ₗ₊ (var i)     ℰ = thm310∋ i ℰ
  thm310ₗ₊ (app 𝒟₁ 𝒟₂) ℰ = thm310ₗ₊ 𝒟₁ (⊃l (wkₛ₊ (thm310ᵣ₊ 𝒟₂)) (exₛ₊ (wkₛ₊ ℰ)))
  thm310ₗ₊ (ann 𝒟)     ℰ = cutₛ (thm310ᵣ₊ 𝒟) ℰ                       


-- Theorem 3.11 (Admissibility of cut)

thm311 : ∀ {A Γ B} → Γ ⟹ A → Γ , A ⟹ B
                   → Γ ⟹ B
thm311 {A}     vzₛ        ℰ          = ctₛ ℰ
thm311 {A}     𝒟          vzₛ        = 𝒟
thm311 {ι P}   (⊃l 𝒟₁ 𝒟₂) (⊃r ℰ)     = {!!}
thm311 {A ⊃ B} (⊃r 𝒟)     (⊃r ℰ)     = {!!}
thm311 {A ⊃ B} (⊃r 𝒟)     (⊃l ℰ₁ ℰ₂) = {!!}
thm311 {A ⊃ B} (⊃l 𝒟₁ 𝒟₂) (⊃r ℰ)     = {!!}
thm311 {A ⊃ B} (⊃l 𝒟₁ 𝒟₂) (⊃l ℰ₁ ℰ₂) = {!!}
thm311 {A ∧ B} 𝒟 ℰ = {!!}
thm311 {⊤}    𝒟 ℰ = {!!}
thm311 {⊥}    𝒟 ℰ = {!!}
thm311 {A ∨ B} 𝒟 ℰ = {!!}


-- Theorem 3.12 (Cut elimination)

thm312 : ∀ {Γ A} → Γ ⟹₊ A
                 → Γ ⟹ A
thm312 vzₛ        = vzₛ
thm312 (⊃r 𝒟)     = ⊃r (thm312 𝒟)
thm312 (⊃l 𝒟 ℰ)   = ⊃l (thm312 𝒟) (thm312 ℰ)
thm312 (cutₛ 𝒟 ℰ) = thm311 (thm312 𝒟) (thm312 ℰ)


⊢→⟹ : ∀ {Γ A} → Γ ⊢ A true
                  → Γ ⟹ A
⊢→⟹ 𝒟 = thm312 (thm310ᵣ₊ (thm33ᵣ₊ 𝒟))


-- Theorem 3.13 (Normalisation for natural deduction)

thm313 : ∀ {Γ A} → Γ ⊢ A true
                 → Γ ⊢ A normal
thm313 𝒟 = thm36 (⊢→⟹ 𝒟)


-- Corollary 3.14 (Consistency)

cor314 : ¬ (∙ ⊢ ⊥ true)
cor314 𝒟 with ⊢→⟹ 𝒟
cor314 𝒟 | ()


-- Corollary 3.15 (Disjunction property)

-- TODO: Existentials for the existential property

cor315 : ∀ {A B} → ∙ ⊢ A ∨ B true
                 → ∙ ⊢ A true ⊎ ∙ ⊢ B true
cor315 𝒟 with ⊢→⟹ 𝒟
cor315 𝒟 | ()


-- Corollary 3.16 (Independence of excluded middle)

-- TODO: ???

postulate
  oops₁ : ∀ {A} → ¬ (∙ ⟹ A)
  oops₂ : ∀ {A} → ¬ (∙ ⟹ A ⊃ ⊥)

cor316 : ∀ {A} → ¬ (∙ ⊢ A ∨ (A ⊃ ⊥) true)
cor316 𝒟 with cor315 𝒟
cor316 𝒟 | inj₁ 𝒟′ with ⊢→⟹ 𝒟′
cor316 𝒟 | inj₁ 𝒟′ | 𝒟″ = oops₁ 𝒟″
cor316 𝒟 | inj₂ 𝒟′ with ⊢→⟹ 𝒟′
cor316 𝒟 | inj₂ 𝒟′ | 𝒟″ = oops₂ 𝒟″


--------------------------------------------------------------------------------

