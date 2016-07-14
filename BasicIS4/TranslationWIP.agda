module BasicIS4.TranslationWIP where

open import BasicIS4.Core public

import BasicIS4.Dual.Gentzen.Core as DG
import BasicIS4.Labelled.Gentzen.Core as LG

open DG using () renaming (_⨾_⊢_ to DG⟨_⨾_⊢_⟩) public
open LG using (_≤_ ; _⦂_) renaming (_⨾_⊢_⦂_ to LG⟨_⨾_⊢_⦂_⟩ ; _⊢_≤_ to LG⟨_⊢_≤_⟩) public


sq : Cx Ty → Cx Ty
sq ⌀       = ⌀
sq (Δ , A) = sq Δ , □ A

la : LG.La → Cx Ty → Cx LG.LaTy
la x ⌀       = ⌀
la x (Γ , A) = la x Γ , x ⦂ A

→var : ∀ {x A Γ} → A ∈ Γ → x ⦂ A ∈ la x Γ
→var top     = top
→var (pop i) = pop (→var i)

→mvar : ∀ {x A Δ} → A ∈ Δ → x ⦂ □ A ∈ la x (sq Δ)
→mvar top     = top
→mvar (pop i) = pop (→mvar i)


module Local where
  open LG

  mvar : ∀ {x A Γ Ξ}
         → x ⦂ □ A ∈ Γ
         → Γ ⨾ Ξ ⊢ x ⦂ A
  mvar i = move (var i) rrefl

  -- NOTE: This is almost certainly false.
  box-lem : ∀ {x y A Γ Ξ}
            → Γ ⨾ Ξ ⊢ x ⦂ A
            → Γ ⨾ Ξ , x ≤ y ⊢ y ⦂ A
  box-lem t = rmono⊢ weak⊆ {!!}

  box-lem′ : ∀ {x y A Γ Ξ}
             → (∀ {z} → Γ ⨾ Ξ , y ≤ z ⊢ z ⦂ A)
             → Γ ⨾ Ξ , x ≤ y ⊢ y ⦂ A
  box-lem′ t = rmono⊢ weak⊆ (move (scan t) rrefl)

  -- NOTE: This depends on an almost certainly false lemma.
  box⧺ : ∀ {x A Γ} Γ′ {Ξ}
         → Γ ⨾ Ξ ⊢ x ⦂ A
         → Γ ⧺ Γ′ ⨾ Ξ ⊢ x ⦂ □ A
  box⧺ {x} Γ′ t = scan λ {y} → mono⊢ (weak⊆⧺ₗ Γ′) (box-lem t)

  unbox : ∀ {x A C Γ Ξ}
          → Γ ⨾ Ξ ⊢ x ⦂ □ A
          → Γ , x ⦂ A ⨾ Ξ ⊢ x ⦂ C
          → Γ ⨾ Ξ ⊢ x ⦂ C
  unbox t u = app (lam u) (move t rrefl)

  unbox-lem : ∀ {x A C Γ} Γ′ {Ξ}
              → (Γ , x ⦂ □ A) ⧺ Γ′ ⨾ Ξ ⊢ x ⦂ C
              → Γ ⧺ Γ′ , x ⦂ A ⨾ Ξ ⊢ x ⦂ C
  unbox-lem Γ′ t = {!!}

  unbox⧺ : ∀ {x A C Γ} Γ′ {Ξ}
           → Γ ⧺ Γ′ ⨾ Ξ ⊢ x ⦂ □ A
           → (Γ , x ⦂ □ A) ⧺ Γ′ ⨾ Ξ ⊢ x ⦂ C
           → Γ ⧺ Γ′ ⨾ Ξ ⊢ x ⦂ C
  unbox⧺ Γ′ t u = unbox t (unbox-lem Γ′ u)


module Nonlocal where
  open LG

  mvar : ∀ {x y A Γ Ξ}
         → x ⦂ □ A ∈ Γ
         → Γ ⨾ Ξ , x ≤ y ⊢ y ⦂ A
  mvar i = move (var i) rv₀

  box-lem : ∀ {x y z A Γ Ξ}
            → Γ ⨾ Ξ , x ≤ y ⊢ y ⦂ A
            → Γ ⨾ Ξ , x ≤ y , y ≤ z ⊢ z ⦂ A
  box-lem t = {!!}

  box⧺ : ∀ {x y A Γ} Γ′ {Ξ}
         → Γ ⨾ Ξ , x ≤ y ⊢ y ⦂ A
         → Γ ⧺ Γ′ ⨾ Ξ , x ≤ y ⊢ y ⦂ □ A
  box⧺ {x} {y} Γ′ t = scan λ {z} → mono⊢ (weak⊆⧺ₗ Γ′) (box-lem t)

  unbox⧺ : ∀ {x y A C Γ} Γ′ {Ξ}
           → Γ ⧺ Γ′ ⨾ Ξ , x ≤ y ⊢ y ⦂ □ A
           → (Γ , x ⦂ □ A) ⧺ Γ′ ⨾ Ξ , x ≤ y ⊢ y ⦂ C
           → Γ ⧺ Γ′ ⨾ Ξ , x ≤ y ⊢ y ⦂ C
  unbox⧺ Γ′ t u = {!!}


dg→lg₁ : ∀ {x Γ A Δ Ξ} → DG⟨ Γ ⨾ Δ ⊢ A ⟩ → LG⟨ (la x (sq Δ) ⧺ la x Γ) ⨾ Ξ ⊢ x ⦂ A ⟩
dg→lg₁ (DG.var i)      = LG.var (mono∈ weak⊆⧺ᵣ (→var i))
dg→lg₁ (DG.lam t)      = LG.lam (dg→lg₁ t)
dg→lg₁ (DG.app t u)    = LG.app (dg→lg₁ t) (dg→lg₁ u)
dg→lg₁ {x} {Γ} (DG.mvar i)    = Local.mvar (mono∈ (weak⊆⧺ₗ (la x Γ)) (→mvar i))
dg→lg₁ {x} {Γ} (DG.box t)     = Local.box⧺ (la x Γ) (dg→lg₁ t)
dg→lg₁ {x} {Γ} (DG.unbox t u) = Local.unbox⧺ (la x Γ) (dg→lg₁ t) (dg→lg₁ u)
dg→lg₁ DG.unit         = LG.unit
dg→lg₁ (DG.pair t u)   = LG.pair (dg→lg₁ t) (dg→lg₁ u)
dg→lg₁ (DG.fst t)      = LG.fst (dg→lg₁ t)
dg→lg₁ (DG.snd t)      = LG.snd (dg→lg₁ t)


dg→lg₂ : ∀ {y Γ x A Δ Ξ} → DG⟨ Γ ⨾ Δ ⊢ A ⟩ → LG⟨ la x (sq Δ) ⧺ la y Γ ⨾ Ξ , x ≤ y ⊢ y ⦂ A ⟩
dg→lg₂ (DG.var i)      = LG.var (mono∈ weak⊆⧺ᵣ (→var i))
dg→lg₂ (DG.lam t)      = LG.lam (dg→lg₂ t)
dg→lg₂ (DG.app t u)    = LG.app (dg→lg₂ t) (dg→lg₂ u)
dg→lg₂ {y} {Γ} (DG.mvar i)    = Nonlocal.mvar (mono∈ (weak⊆⧺ₗ (la y Γ)) (→mvar i))
dg→lg₂ {y} {Γ} (DG.box t)     = Nonlocal.box⧺ (la y Γ) (dg→lg₂ t)
dg→lg₂ {y} {Γ} (DG.unbox t u) = Nonlocal.unbox⧺ (la y Γ) (dg→lg₂ t) (dg→lg₂ u)
dg→lg₂ DG.unit         = LG.unit
dg→lg₂ (DG.pair t u)   = LG.pair (dg→lg₂ t) (dg→lg₂ u)
dg→lg₂ (DG.fst t)      = LG.fst (dg→lg₂ t)
dg→lg₂ (DG.snd t)      = LG.snd (dg→lg₂ t)


-- lgr→dg : ∀ {x y Ξ} → LG⟨ Ξ ⊢ x ≤ y ⟩ → DG⟨ {!!} ⨾ {!!} ⊢ {!!} ⟩
-- lgr→dg t = {!!}

-- lg→dg : ∀ {x A Γ Ξ} → LG⟨ Γ ⨾ Ξ ⊢ x ⦂ A ⟩ → DG⟨ {!!} ⨾ {!!} ⊢ A ⟩
-- lg→dg (LG.var i)      = {!!}
-- lg→dg (LG.lam t)      = DG.lam {!!}
-- lg→dg (LG.app t u)    = DG.app (lg→dg t) (lg→dg u)
-- lg→dg (LG.scan t) =
--       let t′ = lg→dg t
--       in  DG.box {!!}
-- lg→dg (LG.move t u) =
--       let t′ = lg→dg t
--           u′ = lgr→dg u
--       in  DG.unbox {!!} {!!}
-- lg→dg LG.unit         = DG.unit
-- lg→dg (LG.pair t u)   = DG.pair (lg→dg t) (lg→dg u)
-- lg→dg (LG.fst t)      = DG.fst (lg→dg t)
-- lg→dg (LG.snd t)      = DG.snd (lg→dg t)
