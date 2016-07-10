module IS4.TranslationWIP where

open import IS4.Core public

import IS4.Gentzen.PfenningDavies as G
import IS4.Gentzen.BasinMatthewsVigano as LG

open G using () renaming (_⨾_⊢_ to G⟨_⨾_⊢_⟩) public
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


g→lg₁ : ∀ {x Γ A Δ Ξ} → G⟨ Γ ⨾ Δ ⊢ A ⟩ → LG⟨ (la x (sq Δ) ⧺ la x Γ) ⨾ Ξ ⊢ x ⦂ A ⟩
g→lg₁ (G.var i)      = LG.var (mono∈ weak⊆⧺ᵣ (→var i))
g→lg₁ (G.lam t)      = LG.lam (g→lg₁ t)
g→lg₁ (G.app t u)    = LG.app (g→lg₁ t) (g→lg₁ u)
g→lg₁ {x} {Γ} (G.mvar i)    = Local.mvar (mono∈ (weak⊆⧺ₗ (la x Γ)) (→mvar i))
g→lg₁ {x} {Γ} (G.box t)     = Local.box⧺ (la x Γ) (g→lg₁ t)
g→lg₁ {x} {Γ} (G.unbox t u) = Local.unbox⧺ (la x Γ) (g→lg₁ t) (g→lg₁ u)
g→lg₁ G.unit         = LG.unit
g→lg₁ (G.pair t u)   = LG.pair (g→lg₁ t) (g→lg₁ u)
g→lg₁ (G.fst t)      = LG.fst (g→lg₁ t)
g→lg₁ (G.snd t)      = LG.snd (g→lg₁ t)


g→lg₂ : ∀ {y Γ x A Δ Ξ} → G⟨ Γ ⨾ Δ ⊢ A ⟩ → LG⟨ la x (sq Δ) ⧺ la y Γ ⨾ Ξ , x ≤ y ⊢ y ⦂ A ⟩
g→lg₂ (G.var i)      = LG.var (mono∈ weak⊆⧺ᵣ (→var i))
g→lg₂ (G.lam t)      = LG.lam (g→lg₂ t)
g→lg₂ (G.app t u)    = LG.app (g→lg₂ t) (g→lg₂ u)
g→lg₂ {y} {Γ} (G.mvar i)    = Nonlocal.mvar (mono∈ (weak⊆⧺ₗ (la y Γ)) (→mvar i))
g→lg₂ {y} {Γ} (G.box t)     = Nonlocal.box⧺ (la y Γ) (g→lg₂ t)
g→lg₂ {y} {Γ} (G.unbox t u) = Nonlocal.unbox⧺ (la y Γ) (g→lg₂ t) (g→lg₂ u)
g→lg₂ G.unit         = LG.unit
g→lg₂ (G.pair t u)   = LG.pair (g→lg₂ t) (g→lg₂ u)
g→lg₂ (G.fst t)      = LG.fst (g→lg₂ t)
g→lg₂ (G.snd t)      = LG.snd (g→lg₂ t)


-- lgr→g : ∀ {x y Ξ} → LG⟨ Ξ ⊢ x ≤ y ⟩ → G⟨ {!!} ⨾ {!!} ⊢ {!!} ⟩
-- lgr→g t = {!!}

-- lg→g : ∀ {x A Γ Ξ} → LG⟨ Γ ⨾ Ξ ⊢ x ⦂ A ⟩ → G⟨ {!!} ⨾ {!!} ⊢ A ⟩
-- lg→g (LG.var i)      = {!!}
-- lg→g (LG.lam t)      = G.lam {!!}
-- lg→g (LG.app t u)    = G.app (lg→g t) (lg→g u)
-- lg→g (LG.scan t) =
--       let t′ = lg→g t
--       in  G.box {!!}
-- lg→g (LG.move t u) =
--       let t′ = lg→g t
--           u′ = lgr→g u
--       in  G.unbox {!!} {!!}
-- lg→g LG.unit         = G.unit
-- lg→g (LG.pair t u)   = G.pair (lg→g t) (lg→g u)
-- lg→g (LG.fst t)      = G.fst (lg→g t)
-- lg→g (LG.snd t)      = G.snd (lg→g t)
