-- Translation between different formalisations of syntax.

module BasicIS4.Syntax.Translation where

open import BasicIS4.Syntax.Common public
open import Common.ContextPair public

import BasicIS4.Syntax.ClosedHilbertSequential as CHS
import BasicIS4.Syntax.ClosedHilbert as CH
import BasicIS4.Syntax.HilbertSequential as HS
import BasicIS4.Syntax.Hilbert as H
import BasicIS4.Syntax.Gentzen as G
import BasicIS4.Syntax.DyadicHilbertSequential as DHS
import BasicIS4.Syntax.DyadicHilbert as DH
import BasicIS4.Syntax.DyadicGentzen as DG
import BasicIS4.Syntax.LabelledGentzen as LG

open HS using () renaming (_⊦⊢_ to HS⟨_⊦⊢_⟩ ; _⊢_ to HS⟨_⊢_⟩) public
open H using () renaming (_⊢_ to H⟨_⊢_⟩ ; _⊢⋆_ to H⟨_⊢⋆_⟩) public
open G using () renaming (_⊢_ to G⟨_⊢_⟩ ; _⊢⋆_ to G⟨_⊢⋆_⟩) public
open DHS using () renaming (_⊦⊢_ to DHS⟨_⊦⊢_⟩ ; _⊢_ to DHS⟨_⊢_⟩) public
open DH using () renaming (_⊢_ to DH⟨_⊢_⟩) public
open DG using () renaming (_⊢_ to DG⟨_⊢_⟩ ; _⊢⋆_ to DG⟨_⊢⋆_⟩) public
open LG using (_↝_) renaming (_⁏_⊢_◎_ to LG⟨_⁏_⊢_◎_⟩ ; _⁏_⊢⋆_◎_ to LG⟨_⁏_⊢⋆_◎_⟩) public


-- Available translations.
--
--       ┌─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┐
--       │ CHS │ CH  │ HS  │ H   │ G   │ DHS │ DH  │ DG  │ LG  │
-- ┌─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ CHS │     │ d   │ d   │ ∘   │ ∘   │ ∘   │ ∘   │ ∘   │ ∘   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ CH  │ d   │     │ ∘   │ d   │ ∘   │ ∘   │ ∘   │ ∘   │ ∘   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ HS  │ d   │ ∘   │     │ d   │ ∘   │ d   │ ∘   │ ∘   │ ∘   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ H   │ ∘   │ d   │ d   │     │ d   │ ∘   │ d   │ ∘   │ ∘   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ G   │ ∘   │ ∘   │ ∘   │ d   │     │ ∘   │ ∘   │ d   │ d   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ DHS │ ∘   │ ∘   │ d   │ ∘   │ ∘   │     │ d   │ ∘   │ ∘   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ DH  │ ∘   │ ∘   │ ∘   │ d   │ ∘   │ d   │     │ d   │ ∘   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ DG  │ ∘   │ ∘   │ ∘   │ ∘   │ ∘!  │ ∘   │ d   │     │ ∘   │
-- ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
-- │ LG  │ ∘   │ ∘   │ ∘   │ WIP │ WIP │ ∘   │ ∘   │ ∘   │     │
-- └─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┘
--
-- d   : Direct translation.
-- ∘   : Composition of translations.
-- ∘!  : Composition; direct translation fails the termination check.
-- WIP : Work in progress.


-- Translation from closed Hilbert-style linear to closed Hilbert-style.

chs→ch : ∀ {A} → CHS.⊢ A → CH.⊢ A
chs→ch (Ξ , ts) = chs⊦→ch ts top
  where
    chs⊦→ch : ∀ {A Ξ} → CHS.⊦⊢ Ξ → A ∈ Ξ → CH.⊢ A
    chs⊦→ch (CHS.mp i j ts) top     = CH.app (chs⊦→ch ts i) (chs⊦→ch ts j)
    chs⊦→ch (CHS.ci ts)     top     = CH.ci
    chs⊦→ch (CHS.ck ts)     top     = CH.ck
    chs⊦→ch (CHS.cs ts)     top     = CH.cs
    chs⊦→ch (CHS.nec ss ts) top     = CH.box (chs⊦→ch ss top)
    chs⊦→ch (CHS.cdist ts)  top     = CH.cdist
    chs⊦→ch (CHS.cup ts)    top     = CH.cup
    chs⊦→ch (CHS.cdown ts)  top     = CH.cdown
    chs⊦→ch (CHS.cpair ts)  top     = CH.cpair
    chs⊦→ch (CHS.cfst ts)   top     = CH.cfst
    chs⊦→ch (CHS.csnd ts)   top     = CH.csnd
    chs⊦→ch (CHS.tt ts)     top     = CH.tt
    chs⊦→ch (CHS.mp i j ts) (pop k) = chs⊦→ch ts k
    chs⊦→ch (CHS.ci ts)     (pop k) = chs⊦→ch ts k
    chs⊦→ch (CHS.ck ts)     (pop k) = chs⊦→ch ts k
    chs⊦→ch (CHS.cs ts)     (pop k) = chs⊦→ch ts k
    chs⊦→ch (CHS.nec ss ts) (pop k) = chs⊦→ch ts k
    chs⊦→ch (CHS.cdist ts)  (pop k) = chs⊦→ch ts k
    chs⊦→ch (CHS.cup ts)    (pop k) = chs⊦→ch ts k
    chs⊦→ch (CHS.cdown ts)  (pop k) = chs⊦→ch ts k
    chs⊦→ch (CHS.cpair ts)  (pop k) = chs⊦→ch ts k
    chs⊦→ch (CHS.cfst ts)   (pop k) = chs⊦→ch ts k
    chs⊦→ch (CHS.csnd ts)   (pop k) = chs⊦→ch ts k
    chs⊦→ch (CHS.tt ts)     (pop k) = chs⊦→ch ts k


-- Translation from closed Hilbert-style to closed Hilbert-style linear.

ch→chs : ∀ {A} → CH.⊢ A → CHS.⊢ A
ch→chs (CH.app t u) = CHS.app (ch→chs t) (ch→chs u)
ch→chs CH.ci        = ⌀ , CHS.ci CHS.nil
ch→chs CH.ck        = ⌀ , CHS.ck CHS.nil
ch→chs CH.cs        = ⌀ , CHS.cs CHS.nil
ch→chs (CH.box t)   = CHS.box (ch→chs t)
ch→chs CH.cdist     = ⌀ , CHS.cdist CHS.nil
ch→chs CH.cup       = ⌀ , CHS.cup CHS.nil
ch→chs CH.cdown     = ⌀ , CHS.cdown CHS.nil
ch→chs CH.cpair     = ⌀ , CHS.cpair CHS.nil
ch→chs CH.cfst      = ⌀ , CHS.cfst CHS.nil
ch→chs CH.csnd      = ⌀ , CHS.csnd CHS.nil
ch→chs CH.tt        = ⌀ , CHS.tt CHS.nil


-- Translation from Hilbert-style linear to Hilbert-style.

hs→h : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → H⟨ Γ ⊢ A ⟩
hs→h (Ξ , ts) = hs⊦→h ts top
  where
    hs⊦→h : ∀ {A Ξ Γ} → HS⟨ Γ ⊦⊢ Ξ ⟩ → A ∈ Ξ → H⟨ Γ ⊢ A ⟩
    hs⊦→h (HS.var i ts)  top     = H.var i
    hs⊦→h (HS.mp i j ts) top     = H.app (hs⊦→h ts i) (hs⊦→h ts j)
    hs⊦→h (HS.ci ts)     top     = H.ci
    hs⊦→h (HS.ck ts)     top     = H.ck
    hs⊦→h (HS.cs ts)     top     = H.cs
    hs⊦→h (HS.nec ss ts) top     = H.box (hs⊦→h ss top)
    hs⊦→h (HS.cdist ts)  top     = H.cdist
    hs⊦→h (HS.cup ts)    top     = H.cup
    hs⊦→h (HS.cdown ts)  top     = H.cdown
    hs⊦→h (HS.cpair ts)  top     = H.cpair
    hs⊦→h (HS.cfst ts)   top     = H.cfst
    hs⊦→h (HS.csnd ts)   top     = H.csnd
    hs⊦→h (HS.tt ts)     top     = H.tt
    hs⊦→h (HS.var i ts)  (pop k) = hs⊦→h ts k
    hs⊦→h (HS.mp i j ts) (pop k) = hs⊦→h ts k
    hs⊦→h (HS.ci ts)     (pop k) = hs⊦→h ts k
    hs⊦→h (HS.ck ts)     (pop k) = hs⊦→h ts k
    hs⊦→h (HS.cs ts)     (pop k) = hs⊦→h ts k
    hs⊦→h (HS.nec ss ts) (pop k) = hs⊦→h ts k
    hs⊦→h (HS.cdist ts)  (pop k) = hs⊦→h ts k
    hs⊦→h (HS.cup ts)    (pop k) = hs⊦→h ts k
    hs⊦→h (HS.cdown ts)  (pop k) = hs⊦→h ts k
    hs⊦→h (HS.cpair ts)  (pop k) = hs⊦→h ts k
    hs⊦→h (HS.cfst ts)   (pop k) = hs⊦→h ts k
    hs⊦→h (HS.csnd ts)   (pop k) = hs⊦→h ts k
    hs⊦→h (HS.tt ts)     (pop k) = hs⊦→h ts k


-- Translation from Hilbert-style to Hilbert-style linear.

h→hs : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → HS⟨ Γ ⊢ A ⟩
h→hs (H.var i)   = ⌀ , HS.var i HS.nil
h→hs (H.app t u) = HS.app (h→hs t) (h→hs u)
h→hs H.ci        = ⌀ , HS.ci HS.nil
h→hs H.ck        = ⌀ , HS.ck HS.nil
h→hs H.cs        = ⌀ , HS.cs HS.nil
h→hs (H.box t)   = HS.box (h→hs t)
h→hs H.cdist     = ⌀ , HS.cdist HS.nil
h→hs H.cup       = ⌀ , HS.cup HS.nil
h→hs H.cdown     = ⌀ , HS.cdown HS.nil
h→hs H.cpair     = ⌀ , HS.cpair HS.nil
h→hs H.cfst      = ⌀ , HS.cfst HS.nil
h→hs H.csnd      = ⌀ , HS.csnd HS.nil
h→hs H.tt        = ⌀ , HS.tt HS.nil


-- Translation from dyadic Hilbert-style linear to dyadic Hilbert-style.

dhs→dh : ∀ {A Γ Δ} → DHS⟨ Γ ⁏ Δ ⊢ A ⟩ → DH⟨ Γ ⁏ Δ ⊢ A ⟩
dhs→dh (Ξ , ts) = dhs⊦→dh ts top
  where
    dhs⊦→dh : ∀ {A Ξ Γ Δ} → DHS⟨ Γ ⁏ Δ ⊦⊢ Ξ ⟩ → A ∈ Ξ → DH⟨ Γ ⁏ Δ ⊢ A ⟩
    dhs⊦→dh (DHS.var i ts)  top     = DH.var i
    dhs⊦→dh (DHS.mp i j ts) top     = DH.app (dhs⊦→dh ts i) (dhs⊦→dh ts j)
    dhs⊦→dh (DHS.ci ts)     top     = DH.ci
    dhs⊦→dh (DHS.ck ts)     top     = DH.ck
    dhs⊦→dh (DHS.cs ts)     top     = DH.cs
    dhs⊦→dh (DHS.mvar i ts) top     = DH.mvar i
    dhs⊦→dh (DHS.nec ss ts) top     = DH.box (dhs⊦→dh ss top)
    dhs⊦→dh (DHS.cdist ts)  top     = DH.cdist
    dhs⊦→dh (DHS.cup ts)    top     = DH.cup
    dhs⊦→dh (DHS.cdown ts)  top     = DH.cdown
    dhs⊦→dh (DHS.cpair ts)  top     = DH.cpair
    dhs⊦→dh (DHS.cfst ts)   top     = DH.cfst
    dhs⊦→dh (DHS.csnd ts)   top     = DH.csnd
    dhs⊦→dh (DHS.tt ts)     top     = DH.tt
    dhs⊦→dh (DHS.var i ts)  (pop k) = dhs⊦→dh ts k
    dhs⊦→dh (DHS.mp i j ts) (pop k) = dhs⊦→dh ts k
    dhs⊦→dh (DHS.ci ts)     (pop k) = dhs⊦→dh ts k
    dhs⊦→dh (DHS.ck ts)     (pop k) = dhs⊦→dh ts k
    dhs⊦→dh (DHS.cs ts)     (pop k) = dhs⊦→dh ts k
    dhs⊦→dh (DHS.mvar i ts) (pop k) = dhs⊦→dh ts k
    dhs⊦→dh (DHS.nec ss ts) (pop k) = dhs⊦→dh ts k
    dhs⊦→dh (DHS.cdist ts)  (pop k) = dhs⊦→dh ts k
    dhs⊦→dh (DHS.cup ts)    (pop k) = dhs⊦→dh ts k
    dhs⊦→dh (DHS.cdown ts)  (pop k) = dhs⊦→dh ts k
    dhs⊦→dh (DHS.cpair ts)  (pop k) = dhs⊦→dh ts k
    dhs⊦→dh (DHS.cfst ts)   (pop k) = dhs⊦→dh ts k
    dhs⊦→dh (DHS.csnd ts)   (pop k) = dhs⊦→dh ts k
    dhs⊦→dh (DHS.tt ts)     (pop k) = dhs⊦→dh ts k


-- Translation from dyadic Hilbert-style to dyadic Hilbert-style linear

dh→dhs : ∀ {A Γ Δ} → DH⟨ Γ ⁏ Δ ⊢ A ⟩ → DHS⟨ Γ ⁏ Δ ⊢ A ⟩
dh→dhs (DH.var i)   = ⌀ , DHS.var i DHS.nil
dh→dhs (DH.app t u) = DHS.app (dh→dhs t) (dh→dhs u)
dh→dhs DH.ci        = ⌀ , DHS.ci DHS.nil
dh→dhs DH.ck        = ⌀ , DHS.ck DHS.nil
dh→dhs DH.cs        = ⌀ , DHS.cs DHS.nil
dh→dhs (DH.mvar i)  = ⌀ , DHS.mvar i DHS.nil
dh→dhs (DH.box t)   = DHS.box (dh→dhs t)
dh→dhs DH.cdist     = ⌀ , DHS.cdist DHS.nil
dh→dhs DH.cup       = ⌀ , DHS.cup DHS.nil
dh→dhs DH.cdown     = ⌀ , DHS.cdown DHS.nil
dh→dhs DH.cpair     = ⌀ , DHS.cpair DHS.nil
dh→dhs DH.cfst      = ⌀ , DHS.cfst DHS.nil
dh→dhs DH.csnd      = ⌀ , DHS.csnd DHS.nil
dh→dhs DH.tt        = ⌀ , DHS.tt DHS.nil


-- Deduction and detachment theorems for Hilbert-style linear.

hs-lam : ∀ {A B Γ} → HS⟨ Γ , A ⊢ B ⟩ → HS⟨ Γ ⊢ A ▻ B ⟩
hs-lam = h→hs ∘ H.lam ∘ hs→h

hs-lam⋆₀ : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → HS⟨ ⌀ ⊢ Γ ▻⋯▻ A ⟩
hs-lam⋆₀ = h→hs ∘ H.lam⋆₀ ∘ hs→h

hs-det : ∀ {A B Γ} → HS⟨ Γ ⊢ A ▻ B ⟩ → HS⟨ Γ , A ⊢ B ⟩
hs-det = h→hs ∘ H.det ∘ hs→h

hs-det⋆₀ : ∀ {A Γ} → HS⟨ ⌀ ⊢ Γ ▻⋯▻ A ⟩ → HS⟨ Γ ⊢ A ⟩
hs-det⋆₀ = h→hs ∘ H.det⋆₀ ∘ hs→h


-- Deduction and detachment theorems for dyadic Hilbert-style linear.

dhs-lam : ∀ {A B Γ Δ} → DHS⟨ Γ , A ⁏ Δ ⊢ B ⟩ → DHS⟨ Γ ⁏ Δ ⊢ A ▻ B ⟩
dhs-lam = dh→dhs ∘ DH.lam ∘ dhs→dh

dhs-lam⋆₀ : ∀ {A Γ Δ} → DHS⟨ Γ ⁏ Δ ⊢ A ⟩ → DHS⟨ ⌀ ⁏ Δ ⊢ Γ ▻⋯▻ A ⟩
dhs-lam⋆₀ = dh→dhs ∘ DH.lam⋆₀ ∘ dhs→dh

dhs-mlam : ∀ {A B Γ Δ} → DHS⟨ Γ ⁏ Δ , A ⊢ B ⟩ → DHS⟨ Γ ⁏ Δ ⊢ □ A ▻ B ⟩
dhs-mlam = dh→dhs ∘ DH.mlam ∘ dhs→dh

dhs-mlam⋆₀ : ∀ {Δ A Γ} → DHS⟨ Γ ⁏ Δ ⊢ A ⟩ → DHS⟨ Γ ⁏ ⌀ ⊢ □⋆ Δ ▻⋯▻ A ⟩
dhs-mlam⋆₀ = dh→dhs ∘ DH.mlam⋆₀ ∘ dhs→dh

dhs-det : ∀ {A B Γ Δ} → DHS⟨ Γ ⁏ Δ ⊢ A ▻ B ⟩ → DHS⟨ Γ , A ⁏ Δ ⊢ B ⟩
dhs-det = dh→dhs ∘ DH.det ∘ dhs→dh

dhs-det⋆₀ : ∀ {A Γ Δ} → DHS⟨ ⌀ ⁏ Δ ⊢ Γ ▻⋯▻ A ⟩ → DHS⟨ Γ ⁏ Δ ⊢ A ⟩
dhs-det⋆₀ = dh→dhs ∘ DH.det⋆₀ ∘ dhs→dh

dhs-mdet : ∀ {A B Γ Δ} → DHS⟨ Γ ⁏ Δ ⊢ □ A ▻ B ⟩ → DHS⟨ Γ ⁏ Δ , A ⊢ B ⟩
dhs-mdet = dh→dhs ∘ DH.mdet ∘ dhs→dh

dhs-mdet⋆₀ : ∀ {Δ A Γ} → DHS⟨ Γ ⁏ ⌀ ⊢ □⋆ Δ ▻⋯▻ A ⟩ → DHS⟨ Γ ⁏ Δ ⊢ A ⟩
dhs-mdet⋆₀ = dh→dhs ∘ DH.mdet⋆₀ ∘ dhs→dh


-- Context manipulation for dyadic Hilbert-style linear.

dhs-merge : ∀ {Δ A Γ} → DHS⟨ Γ ⁏ Δ ⊢ A ⟩ → DHS⟨ Γ ⧺ (□⋆ Δ) ⁏ ⌀ ⊢ A ⟩
dhs-merge {Δ} = dh→dhs ∘ DH.merge ∘ dhs→dh

dhs-split : ∀ {Δ A Γ} → DHS⟨ Γ ⧺ (□⋆ Δ) ⁏ ⌀ ⊢ A ⟩ → DHS⟨ Γ ⁏ Δ ⊢ A ⟩
dhs-split {Δ} = dh→dhs ∘ DH.split ∘ dhs→dh


-- Translation from closed Hilbert-style linear to Hilbert-style linear.

chs→hs₀ : ∀ {A} → CHS.⊢ A → HS⟨ ⌀ ⊢ A ⟩
chs→hs₀ (Ξ , ts) = Ξ , chs⊦→hs⊦ ts
  where
    chs⊦→hs⊦ : ∀ {Ξ} → CHS.⊦⊢ Ξ → HS⟨ ⌀ ⊦⊢ Ξ ⟩
    chs⊦→hs⊦ CHS.nil         = HS.nil
    chs⊦→hs⊦ (CHS.mp i j ts) = HS.mp i j (chs⊦→hs⊦ ts)
    chs⊦→hs⊦ (CHS.ci ts)     = HS.ci (chs⊦→hs⊦ ts)
    chs⊦→hs⊦ (CHS.ck ts)     = HS.ck (chs⊦→hs⊦ ts)
    chs⊦→hs⊦ (CHS.cs ts)     = HS.cs (chs⊦→hs⊦ ts)
    chs⊦→hs⊦ (CHS.cpair ts)  = HS.cpair (chs⊦→hs⊦ ts)
    chs⊦→hs⊦ (CHS.cfst ts)   = HS.cfst (chs⊦→hs⊦ ts)
    chs⊦→hs⊦ (CHS.csnd ts)   = HS.csnd (chs⊦→hs⊦ ts)
    chs⊦→hs⊦ (CHS.tt ts)     = HS.tt (chs⊦→hs⊦ ts)
    chs⊦→hs⊦ (CHS.nec ss ts) = HS.nec (chs⊦→hs⊦ ss) (chs⊦→hs⊦ ts)
    chs⊦→hs⊦ (CHS.cdist ts)  = HS.cdist (chs⊦→hs⊦ ts)
    chs⊦→hs⊦ (CHS.cup ts)    = HS.cup (chs⊦→hs⊦ ts)
    chs⊦→hs⊦ (CHS.cdown ts)  = HS.cdown (chs⊦→hs⊦ ts)

chs→hs : ∀ {A Γ} → CHS.⊢ Γ ▻⋯▻ A → HS⟨ Γ ⊢ A ⟩
chs→hs t = hs-det⋆₀ (chs→hs₀ t)


-- Translation from Hilbert-style linear to closed Hilbert-style linear.

hs₀→chs : ∀ {A} → HS⟨ ⌀ ⊢ A ⟩ → CHS.⊢ A
hs₀→chs (Ξ , ts) = Ξ , hs₀⊦→chs⊦ ts
  where
    hs₀⊦→chs⊦ : ∀ {Ξ} → HS⟨ ⌀ ⊦⊢ Ξ ⟩ → CHS.⊦⊢ Ξ
    hs₀⊦→chs⊦ HS.nil         = CHS.nil
    hs₀⊦→chs⊦ (HS.var () ts)
    hs₀⊦→chs⊦ (HS.mp i j ts) = CHS.mp i j (hs₀⊦→chs⊦ ts)
    hs₀⊦→chs⊦ (HS.ci ts)     = CHS.ci (hs₀⊦→chs⊦ ts)
    hs₀⊦→chs⊦ (HS.ck ts)     = CHS.ck (hs₀⊦→chs⊦ ts)
    hs₀⊦→chs⊦ (HS.cs ts)     = CHS.cs (hs₀⊦→chs⊦ ts)
    hs₀⊦→chs⊦ (HS.cpair ts)  = CHS.cpair (hs₀⊦→chs⊦ ts)
    hs₀⊦→chs⊦ (HS.cfst ts)   = CHS.cfst (hs₀⊦→chs⊦ ts)
    hs₀⊦→chs⊦ (HS.csnd ts)   = CHS.csnd (hs₀⊦→chs⊦ ts)
    hs₀⊦→chs⊦ (HS.tt ts)     = CHS.tt (hs₀⊦→chs⊦ ts)
    hs₀⊦→chs⊦ (HS.nec ss ts) = CHS.nec (hs₀⊦→chs⊦ ss) (hs₀⊦→chs⊦ ts)
    hs₀⊦→chs⊦ (HS.cdist ts)  = CHS.cdist (hs₀⊦→chs⊦ ts)
    hs₀⊦→chs⊦ (HS.cup ts)    = CHS.cup (hs₀⊦→chs⊦ ts)
    hs₀⊦→chs⊦ (HS.cdown ts)  = CHS.cdown (hs₀⊦→chs⊦ ts)

hs→chs : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → CHS.⊢ Γ ▻⋯▻ A
hs→chs t = hs₀→chs (hs-lam⋆₀ t)


-- Translation from dyadic Hilbert-style linear to Hilbert-style linear.

dhs₀→hs : ∀ {A Γ} → DHS⟨ Γ ⁏ ⌀ ⊢ A ⟩ → HS⟨ Γ ⊢ A ⟩
dhs₀→hs (Ξ , ts) = Ξ , dhs₀⊦→hs⊦ ts
  where
    dhs₀⊦→hs⊦ : ∀ {Ξ Γ} → DHS⟨ Γ ⁏ ⌀ ⊦⊢ Ξ ⟩ → HS⟨ Γ ⊦⊢ Ξ ⟩
    dhs₀⊦→hs⊦ DHS.nil          = HS.nil
    dhs₀⊦→hs⊦ (DHS.var i ts)   = HS.var i (dhs₀⊦→hs⊦ ts)
    dhs₀⊦→hs⊦ (DHS.mp i j ts)  = HS.mp i j (dhs₀⊦→hs⊦ ts)
    dhs₀⊦→hs⊦ (DHS.ci ts)      = HS.ci (dhs₀⊦→hs⊦ ts)
    dhs₀⊦→hs⊦ (DHS.ck ts)      = HS.ck (dhs₀⊦→hs⊦ ts)
    dhs₀⊦→hs⊦ (DHS.cs ts)      = HS.cs (dhs₀⊦→hs⊦ ts)
    dhs₀⊦→hs⊦ (DHS.mvar () ts)
    dhs₀⊦→hs⊦ (DHS.nec ss ts)  = HS.nec (dhs₀⊦→hs⊦ ss) (dhs₀⊦→hs⊦ ts)
    dhs₀⊦→hs⊦ (DHS.cdist ts)   = HS.cdist (dhs₀⊦→hs⊦ ts)
    dhs₀⊦→hs⊦ (DHS.cup ts)     = HS.cup (dhs₀⊦→hs⊦ ts)
    dhs₀⊦→hs⊦ (DHS.cdown ts)   = HS.cdown (dhs₀⊦→hs⊦ ts)
    dhs₀⊦→hs⊦ (DHS.cpair ts)   = HS.cpair (dhs₀⊦→hs⊦ ts)
    dhs₀⊦→hs⊦ (DHS.cfst ts)    = HS.cfst (dhs₀⊦→hs⊦ ts)
    dhs₀⊦→hs⊦ (DHS.csnd ts)    = HS.csnd (dhs₀⊦→hs⊦ ts)
    dhs₀⊦→hs⊦ (DHS.tt ts)      = HS.tt (dhs₀⊦→hs⊦ ts)

dhs→hs : ∀ {A Γ Δ} → DHS⟨ Γ ⁏ Δ ⊢ A ⟩ → HS⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dhs→hs = dhs₀→hs ∘ dhs-merge


-- Translation from Hilbert-style linear to dyadic Hilbert-style linear.

hs→dhs₀ : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → DHS⟨ Γ ⁏ ⌀ ⊢ A ⟩
hs→dhs₀ (Ξ , ts) = Ξ , hs⊦→dhs₀⊦ ts
  where
    hs⊦→dhs₀⊦ : ∀ {Ξ Γ} → HS⟨ Γ ⊦⊢ Ξ ⟩ → DHS⟨ Γ ⁏ ⌀ ⊦⊢ Ξ ⟩
    hs⊦→dhs₀⊦ HS.nil         = DHS.nil
    hs⊦→dhs₀⊦ (HS.var i ts)  = DHS.var i (hs⊦→dhs₀⊦ ts)
    hs⊦→dhs₀⊦ (HS.mp i j ts) = DHS.mp i j (hs⊦→dhs₀⊦ ts)
    hs⊦→dhs₀⊦ (HS.ci ts)     = DHS.ci (hs⊦→dhs₀⊦ ts)
    hs⊦→dhs₀⊦ (HS.ck ts)     = DHS.ck (hs⊦→dhs₀⊦ ts)
    hs⊦→dhs₀⊦ (HS.cs ts)     = DHS.cs (hs⊦→dhs₀⊦ ts)
    hs⊦→dhs₀⊦ (HS.nec ss ts) = DHS.nec (hs⊦→dhs₀⊦ ss) (hs⊦→dhs₀⊦ ts)
    hs⊦→dhs₀⊦ (HS.cdist ts)  = DHS.cdist (hs⊦→dhs₀⊦ ts)
    hs⊦→dhs₀⊦ (HS.cup ts)    = DHS.cup (hs⊦→dhs₀⊦ ts)
    hs⊦→dhs₀⊦ (HS.cdown ts)  = DHS.cdown (hs⊦→dhs₀⊦ ts)
    hs⊦→dhs₀⊦ (HS.cpair ts)  = DHS.cpair (hs⊦→dhs₀⊦ ts)
    hs⊦→dhs₀⊦ (HS.cfst ts)   = DHS.cfst (hs⊦→dhs₀⊦ ts)
    hs⊦→dhs₀⊦ (HS.csnd ts)   = DHS.csnd (hs⊦→dhs₀⊦ ts)
    hs⊦→dhs₀⊦ (HS.tt ts)     = DHS.tt (hs⊦→dhs₀⊦ ts)

hs→dhs : ∀ {A Γ Δ} → HS⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DHS⟨ Γ ⁏ Δ ⊢ A ⟩
hs→dhs = dhs-split ∘ hs→dhs₀


-- Translation from closed Hilbert-style to Hilbert-style.

ch→h₀ : ∀ {A} → CH.⊢ A → H⟨ ⌀ ⊢ A ⟩
ch→h₀ (CH.app t u) = H.app (ch→h₀ t) (ch→h₀ u)
ch→h₀ CH.ci        = H.ci
ch→h₀ CH.ck        = H.ck
ch→h₀ CH.cs        = H.cs
ch→h₀ CH.cpair     = H.cpair
ch→h₀ CH.cfst      = H.cfst
ch→h₀ CH.csnd      = H.csnd
ch→h₀ CH.tt        = H.tt
ch→h₀ (CH.box t)   = H.box (ch→h₀ t)
ch→h₀ CH.cdist     = H.cdist
ch→h₀ CH.cup       = H.cup
ch→h₀ CH.cdown     = H.cdown

ch→h : ∀ {A Γ} → CH.⊢ Γ ▻⋯▻ A → H⟨ Γ ⊢ A ⟩
ch→h t = H.det⋆₀ (ch→h₀ t)


-- Translation from Hilbert-style to closed Hilbert-style.

h₀→ch : ∀ {A} → H⟨ ⌀ ⊢ A ⟩ → CH.⊢ A
h₀→ch (H.var ())
h₀→ch (H.app t u) = CH.app (h₀→ch t) (h₀→ch u)
h₀→ch H.ci        = CH.ci
h₀→ch H.ck        = CH.ck
h₀→ch H.cs        = CH.cs
h₀→ch H.cpair     = CH.cpair
h₀→ch H.cfst      = CH.cfst
h₀→ch H.csnd      = CH.csnd
h₀→ch H.tt        = CH.tt
h₀→ch (H.box t)   = CH.box (h₀→ch t)
h₀→ch H.cdist     = CH.cdist
h₀→ch H.cup       = CH.cup
h₀→ch H.cdown     = CH.cdown

h→ch : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → CH.⊢ Γ ▻⋯▻ A
h→ch t = h₀→ch (H.lam⋆₀ t)


-- Translation from dyadic Hilbert-style to Hilbert-style.

dh₀→h : ∀ {A Γ} → DH⟨ Γ ⁏ ⌀ ⊢ A ⟩ → H⟨ Γ ⊢ A ⟩
dh₀→h (DH.var i)   = H.var i
dh₀→h (DH.app t u) = H.app (dh₀→h t) (dh₀→h u)
dh₀→h DH.ci        = H.ci
dh₀→h DH.ck        = H.ck
dh₀→h DH.cs        = H.cs
dh₀→h (DH.mvar ())
dh₀→h (DH.box t)   = H.box (dh₀→h t)
dh₀→h DH.cdist     = H.cdist
dh₀→h DH.cup       = H.cup
dh₀→h DH.cdown     = H.cdown
dh₀→h DH.cpair     = H.cpair
dh₀→h DH.cfst      = H.cfst
dh₀→h DH.csnd      = H.csnd
dh₀→h DH.tt        = H.tt

dh→h : ∀ {A Γ Δ} → DH⟨ Γ ⁏ Δ ⊢ A ⟩ → H⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dh→h = dh₀→h ∘ DH.merge


-- Translation from Hilbert-style to dyadic Hilbert-style.

h→dh₀ : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → DH⟨ Γ ⁏ ⌀ ⊢ A ⟩
h→dh₀ (H.var i)   = DH.var i
h→dh₀ (H.app t u) = DH.app (h→dh₀ t) (h→dh₀ u)
h→dh₀ H.ci        = DH.ci
h→dh₀ H.ck        = DH.ck
h→dh₀ H.cs        = DH.cs
h→dh₀ (H.box t)   = DH.box (h→dh₀ t)
h→dh₀ H.cdist     = DH.cdist
h→dh₀ H.cup       = DH.cup
h→dh₀ H.cdown     = DH.cdown
h→dh₀ H.cpair     = DH.cpair
h→dh₀ H.cfst      = DH.cfst
h→dh₀ H.csnd      = DH.csnd
h→dh₀ H.tt        = DH.tt

h→dh : ∀ {A Γ Δ} → H⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DH⟨ Γ ⁏ Δ ⊢ A ⟩
h→dh = DH.split ∘ h→dh₀


-- Translation from Hilbert-style to Gentzen-style.

h→g : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
h→g (H.var i)   = G.var i
h→g (H.app t u) = G.app (h→g t) (h→g u)
h→g H.ci        = G.ci
h→g H.ck        = G.ck
h→g H.cs        = G.cs
h→g (H.box t)   = G.box (h→g t)
h→g H.cdist     = G.cdist
h→g H.cup       = G.cup
h→g H.cdown     = G.cdown
h→g H.cpair     = G.cpair
h→g H.cfst      = G.cfst
h→g H.csnd      = G.csnd
h→g H.tt        = G.tt


-- Translation from Gentzen-style to Hilbert-style.

mutual
  g→h : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → H⟨ Γ ⊢ A ⟩
  g→h (G.var i)         = H.var i
  g→h (G.lam t)         = H.lam (g→h t)
  g→h (G.app t u)       = H.app (g→h t) (g→h u)
  g→h (G.multibox ts u) = H.multibox (g→h⋆ ts) (g→h u)
  g→h (G.down t)        = H.down (g→h t)
  g→h (G.pair t u)      = H.pair (g→h t) (g→h u)
  g→h (G.fst t)         = H.fst (g→h t)
  g→h (G.snd t)         = H.snd (g→h t)
  g→h G.tt              = H.tt

  g→h⋆ : ∀ {Ξ Γ} → G⟨ Γ ⊢⋆ Ξ ⟩ → H⟨ Γ ⊢⋆ Ξ ⟩
  g→h⋆ {⌀}     ∙        = ∙
  g→h⋆ {Ξ , A} (ts , t) = g→h⋆ ts , g→h t


-- Translation from dyadic Hilbert-style to dyadic Gentzen-style.

dh→dg : ∀ {A Γ Δ} → DH⟨ Γ ⁏ Δ ⊢ A ⟩ → DG⟨ Γ ⁏ Δ ⊢ A ⟩
dh→dg (DH.var i)   = DG.var i
dh→dg (DH.app t u) = DG.app (dh→dg t) (dh→dg u)
dh→dg DH.ci        = DG.ci
dh→dg DH.ck        = DG.ck
dh→dg DH.cs        = DG.cs
dh→dg (DH.mvar i)  = DG.mvar i
dh→dg (DH.box t)   = DG.box (dh→dg t)
dh→dg DH.cdist     = DG.cdist
dh→dg DH.cup       = DG.cup
dh→dg DH.cdown     = DG.cdown
dh→dg DH.cpair     = DG.cpair
dh→dg DH.cfst      = DG.cfst
dh→dg DH.csnd      = DG.csnd
dh→dg DH.tt        = DG.tt


-- Translation from dyadic Gentzen-style to dyadic Hilbert-style.

dg→dh : ∀ {A Γ Δ} → DG⟨ Γ ⁏ Δ ⊢ A ⟩ → DH⟨ Γ ⁏ Δ ⊢ A ⟩
dg→dh (DG.var i)     = DH.var i
dg→dh (DG.lam t)     = DH.lam (dg→dh t)
dg→dh (DG.app t u)   = DH.app (dg→dh t) (dg→dh u)
dg→dh (DG.mvar i)    = DH.mvar i
dg→dh (DG.box t)     = DH.box (dg→dh t)
dg→dh (DG.unbox t u) = DH.unbox (dg→dh t) (dg→dh u)
dg→dh (DG.pair t u)  = DH.pair (dg→dh t) (dg→dh u)
dg→dh (DG.fst t)     = DH.fst (dg→dh t)
dg→dh (DG.snd t)     = DH.snd (dg→dh t)
dg→dh DG.tt          = DH.tt


-- Translation from Gentzen-style to dyadic Gentzen-style.

mutual
  g→dg₀ : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩
  g→dg₀ (G.var i)         = DG.var i
  g→dg₀ (G.lam t)         = DG.lam (g→dg₀ t)
  g→dg₀ (G.app t u)       = DG.app (g→dg₀ t) (g→dg₀ u)
  g→dg₀ (G.multibox ts u) = DG.multibox (g→dg₀⋆ ts) (g→dg₀ u)
  g→dg₀ (G.down t)        = DG.down (g→dg₀ t)
  g→dg₀ (G.pair t u)      = DG.pair (g→dg₀ t) (g→dg₀ u)
  g→dg₀ (G.fst t)         = DG.fst (g→dg₀ t)
  g→dg₀ (G.snd t)         = DG.snd (g→dg₀ t)
  g→dg₀ G.tt              = DG.tt

  g→dg₀⋆ : ∀ {Ξ Γ} → G⟨ Γ ⊢⋆ Ξ ⟩ → DG⟨ Γ ⁏ ⌀ ⊢⋆ Ξ ⟩
  g→dg₀⋆ {⌀}     ∙        = ∙
  g→dg₀⋆ {Ξ , A} (ts , t) = g→dg₀⋆ ts , g→dg₀ t

g→dg : ∀ {A Γ Δ} → G⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DG⟨ Γ ⁏ Δ ⊢ A ⟩
g→dg = DG.split ∘ g→dg₀


-- Translation from Hilbert-style to labelled Gentzen-style.

h→lg : ∀ {x A Γ Λ} → H⟨ Γ ⊢ A ⟩ → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩
h→lg (H.var i)   = LG.var i
h→lg (H.app t u) = LG.app (h→lg t) (h→lg u)
h→lg H.ci        = LG.ci
h→lg H.ck        = LG.ck
h→lg H.cs        = LG.cs
h→lg (H.box t)   = LG.box (h→lg t)
h→lg H.cdist     = LG.cdist
h→lg H.cup       = LG.cup
h→lg H.cdown     = LG.cdown
h→lg H.cpair     = LG.cpair
h→lg H.cfst      = LG.cfst
h→lg H.csnd      = LG.csnd
h→lg H.tt        = LG.tt


-- Translation from labelled Gentzen-style to Hilbert-style.

-- FIXME: Stronger hypothesis?
postulate
  h-oops : ∀ {x A Γ Λ} → (∀ {y} → LG⟨ Γ ⁏ Λ , x ↝ y ⊢ A ◎ y ⟩) → H⟨ Γ ⊢ □ A ⟩

lg→h : ∀ {x A Γ Λ} → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩ → H⟨ Γ ⊢ A ⟩
lg→h (LG.var i)    = H.var i
lg→h (LG.lam t)    = H.lam (lg→h t)
lg→h (LG.app t u)  = H.app (lg→h t) (lg→h u)
lg→h (LG.scan t)   = h-oops t
lg→h (LG.move t u) = H.down (lg→h t)
lg→h (LG.pair t u) = H.pair (lg→h t) (lg→h u)
lg→h (LG.fst t)    = H.fst (lg→h t)
lg→h (LG.snd t)    = H.snd (lg→h t)
lg→h LG.tt         = H.tt


-- Translation from Gentzen-style to labelled Gentzen-style.

mutual
  g→lg : ∀ {x A Γ Λ} → G⟨ Γ ⊢ A ⟩ → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩
  g→lg (G.var i)         = LG.var i
  g→lg (G.lam t)         = LG.lam (g→lg t)
  g→lg (G.app t u)       = LG.app (g→lg t) (g→lg u)
  g→lg (G.multibox ts u) = LG.multibox (g→lg⋆ ts) (g→lg u)
  g→lg (G.down t)        = LG.move (g→lg t) LG.rrefl
  g→lg (G.pair t u)      = LG.pair (g→lg t) (g→lg u)
  g→lg (G.fst t)         = LG.fst (g→lg t)
  g→lg (G.snd t)         = LG.snd (g→lg t)
  g→lg G.tt              = LG.tt

  g→lg⋆ : ∀ {x Ξ Γ Λ} → G⟨ Γ ⊢⋆ Ξ ⟩ → LG⟨ Γ ⁏ Λ ⊢⋆ Ξ ◎ x ⟩
  g→lg⋆ {x} {⌀}     ∙        = ∙
  g→lg⋆ {x} {Ξ , A} (ts , t) = g→lg⋆ ts , g→lg t


-- Translation from labelled Gentzen-style to Gentzen-style.

-- FIXME: Stronger hypothesis?
postulate
  g-oops : ∀ {x A Γ Λ} → (∀ {y} → LG⟨ Γ ⁏ Λ , x ↝ y ⊢ A ◎ y ⟩) → G⟨ Γ ⊢ □ A ⟩

lg→g : ∀ {x A Γ Λ} → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩ → G⟨ Γ ⊢ A ⟩
lg→g (LG.var i)    = G.var i
lg→g (LG.lam t)    = G.lam (lg→g t)
lg→g (LG.app t u)  = G.app (lg→g t) (lg→g u)
lg→g (LG.scan t)   = g-oops t
lg→g (LG.move t u) = G.down (lg→g t)
lg→g (LG.pair t u) = G.pair (lg→g t) (lg→g u)
lg→g (LG.fst t)    = G.fst (lg→g t)
lg→g (LG.snd t)    = G.snd (lg→g t)
lg→g LG.tt         = G.tt


-- Additional translations from closed Hilbert-style linear.

chs→h₀ : ∀ {A} → CHS.⊢ A → H⟨ ⌀ ⊢ A ⟩
chs→h₀ = ch→h₀ ∘ chs→ch

chs→h : ∀ {A Γ} → CHS.⊢ Γ ▻⋯▻ A → H⟨ Γ ⊢ A ⟩
chs→h = ch→h ∘ chs→ch

chs→g₀ : ∀ {A} → CHS.⊢ A → G⟨ ⌀ ⊢ A ⟩
chs→g₀ = h→g ∘ chs→h₀

chs→g : ∀ {A Γ} → CHS.⊢ Γ ▻⋯▻ A → G⟨ Γ ⊢ A ⟩
chs→g = h→g ∘ chs→h

chs→dhs₀₀ : ∀ {A} → CHS.⊢ A → DHS⟨ ⌀ ⁏ ⌀ ⊢ A ⟩
chs→dhs₀₀ = hs→dhs₀ ∘ chs→hs₀

chs→dhs₀ : ∀ {A Γ} → CHS.⊢ Γ ▻⋯▻ A → DHS⟨ Γ ⁏ ⌀ ⊢ A ⟩
chs→dhs₀ = hs→dhs₀ ∘ chs→hs

chs→dhs : ∀ {A Γ Δ} → CHS.⊢ Γ ⧺ (□⋆ Δ) ▻⋯▻ A → DHS⟨ Γ ⁏ Δ ⊢ A ⟩
chs→dhs = hs→dhs ∘ chs→hs

chs→dh₀₀ : ∀ {A} → CHS.⊢ A → DH⟨ ⌀ ⁏ ⌀ ⊢ A ⟩
chs→dh₀₀ = h→dh₀ ∘ chs→h₀

chs→dh₀ : ∀ {A Γ} → CHS.⊢ Γ ▻⋯▻ A → DH⟨ Γ ⁏ ⌀ ⊢ A ⟩
chs→dh₀ = h→dh₀ ∘ chs→h

chs→dh : ∀ {A Γ Δ} → CHS.⊢ Γ ⧺ (□⋆ Δ) ▻⋯▻ A → DH⟨ Γ ⁏ Δ ⊢ A ⟩
chs→dh = h→dh ∘ chs→h

chs→dg₀₀ : ∀ {A} → CHS.⊢ A → DG⟨ ⌀ ⁏ ⌀ ⊢ A ⟩
chs→dg₀₀ = g→dg₀ ∘ chs→g₀

chs→dg₀ : ∀ {A Γ} → CHS.⊢ Γ ▻⋯▻ A → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩
chs→dg₀ = g→dg₀ ∘ chs→g

chs→dg : ∀ {A Γ Δ} → CHS.⊢ Γ ⧺ (□⋆ Δ) ▻⋯▻ A → DG⟨ Γ ⁏ Δ ⊢ A ⟩
chs→dg = g→dg ∘ chs→g

chs→lg₀ : ∀ {x A Λ} → CHS.⊢ A → LG⟨ ⌀ ⁏ Λ ⊢ A ◎ x ⟩
chs→lg₀ = g→lg ∘ chs→g₀

chs→lg : ∀ {x A Γ Λ} → CHS.⊢ Γ ▻⋯▻ A → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩
chs→lg = g→lg ∘ chs→g


-- Additional translations from closed Hilbert-style.

ch→hs₀ : ∀ {A} → CH.⊢ A → HS⟨ ⌀ ⊢ A ⟩
ch→hs₀ = chs→hs ∘ ch→chs

ch→hs : ∀ {A Γ} → CH.⊢ Γ ▻⋯▻ A → HS⟨ Γ ⊢ A ⟩
ch→hs = chs→hs ∘ ch→chs

ch→g₀ : ∀ {A} → CH.⊢ A → G⟨ ⌀ ⊢ A ⟩
ch→g₀ = h→g ∘ ch→h₀

ch→g : ∀ {A Γ} → CH.⊢ Γ ▻⋯▻ A → G⟨ Γ ⊢ A ⟩
ch→g = h→g ∘ ch→h

ch→dhs₀₀ : ∀ {A} → CH.⊢ A → DHS⟨ ⌀ ⁏ ⌀ ⊢ A ⟩
ch→dhs₀₀ = hs→dhs₀ ∘ ch→hs₀

ch→dhs₀ : ∀ {A Γ} → CH.⊢ Γ ▻⋯▻ A → DHS⟨ Γ ⁏ ⌀ ⊢ A ⟩
ch→dhs₀ = hs→dhs₀ ∘ ch→hs

ch→dhs : ∀ {A Γ Δ} → CH.⊢ Γ ⧺ (□⋆ Δ) ▻⋯▻ A → DHS⟨ Γ ⁏ Δ ⊢ A ⟩
ch→dhs = hs→dhs ∘ ch→hs

ch→dh₀₀ : ∀ {A} → CH.⊢ A → DH⟨ ⌀ ⁏ ⌀ ⊢ A ⟩
ch→dh₀₀ = h→dh₀ ∘ ch→h₀

ch→dh₀ : ∀ {A Γ} → CH.⊢ Γ ▻⋯▻ A → DH⟨ Γ ⁏ ⌀ ⊢ A ⟩
ch→dh₀ = h→dh₀ ∘ ch→h

ch→dh : ∀ {A Γ Δ} → CH.⊢ Γ ⧺ (□⋆ Δ) ▻⋯▻ A → DH⟨ Γ ⁏ Δ ⊢ A ⟩
ch→dh = h→dh ∘ ch→h

ch→dg₀₀ : ∀ {A} → CH.⊢ A → DG⟨ ⌀ ⁏ ⌀ ⊢ A ⟩
ch→dg₀₀ = g→dg₀ ∘ ch→g₀

ch→dg₀ : ∀ {A Γ} → CH.⊢ Γ ▻⋯▻ A → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩
ch→dg₀ = g→dg₀ ∘ ch→g

ch→dg : ∀ {A Γ Δ} → CH.⊢ Γ ⧺ (□⋆ Δ) ▻⋯▻ A → DG⟨ Γ ⁏ Δ ⊢ A ⟩
ch→dg = g→dg ∘ ch→g

ch→lg₀ : ∀ {x A Λ} → CH.⊢ A → LG⟨ ⌀ ⁏ Λ ⊢ A ◎ x ⟩
ch→lg₀ = g→lg ∘ ch→g₀

ch→lg : ∀ {x A Γ Λ} → CH.⊢ Γ ▻⋯▻ A → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩
ch→lg = g→lg ∘ ch→g


-- Additional translations from Hilbert-style linear.

hs₀→ch : ∀ {A} → HS⟨ ⌀ ⊢ A ⟩ → CH.⊢ A
hs₀→ch = chs→ch ∘ hs₀→chs

hs→ch : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → CH.⊢ Γ ▻⋯▻ A
hs→ch = chs→ch ∘ hs→chs

hs→g : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
hs→g = h→g ∘ hs→h

hs→dh₀ : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → DH⟨ Γ ⁏ ⌀ ⊢ A ⟩
hs→dh₀ = h→dh₀ ∘ hs→h

hs→dh : ∀ {A Γ Δ} → HS⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DH⟨ Γ ⁏ Δ ⊢ A ⟩
hs→dh = h→dh ∘ hs→h

hs→dg₀ : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩
hs→dg₀ = dh→dg ∘ hs→dh₀

hs→dg : ∀ {A Γ Δ} → HS⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DG⟨ Γ ⁏ Δ ⊢ A ⟩
hs→dg = dh→dg ∘ hs→dh

hs→lg : ∀ {x A Γ Λ} → HS⟨ Γ ⊢ A ⟩ → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩
hs→lg = h→lg ∘ hs→h


-- Additional translations from Hilbert-style.

h₀→chs : ∀ {A} → H⟨ ⌀ ⊢ A ⟩ → CHS.⊢ A
h₀→chs = ch→chs ∘ h₀→ch

h→chs : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → CHS.⊢ Γ ▻⋯▻ A
h→chs = ch→chs ∘ h→ch

h→dhs₀ : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → DHS⟨ Γ ⁏ ⌀ ⊢ A ⟩
h→dhs₀ = hs→dhs₀ ∘ h→hs

h→dhs : ∀ {A Γ Δ} → H⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DHS⟨ Γ ⁏ Δ ⊢ A ⟩
h→dhs = hs→dhs ∘ h→hs

h→dg₀ : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩
h→dg₀ = dh→dg ∘ h→dh₀

h→dg : ∀ {A Γ Δ} → H⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DG⟨ Γ ⁏ Δ ⊢ A ⟩
h→dg = dh→dg ∘ h→dh


-- Additional translations from Gentzen-style.

g₀→chs : ∀ {A} → G⟨ ⌀ ⊢ A ⟩ → CHS.⊢ A
g₀→chs = h₀→chs ∘ g→h

g→chs : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → CHS.⊢ Γ ▻⋯▻ A
g→chs = h→chs ∘ g→h

g₀→ch : ∀ {A} → G⟨ ⌀ ⊢ A ⟩ → CH.⊢ A
g₀→ch = h₀→ch ∘ g→h

g→ch : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → CH.⊢ Γ ▻⋯▻ A
g→ch = h→ch ∘ g→h

g→hs : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HS⟨ Γ ⊢ A ⟩
g→hs = h→hs ∘ g→h

g→dhs₀ : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → DHS⟨ Γ ⁏ ⌀ ⊢ A ⟩
g→dhs₀ = h→dhs₀ ∘ g→h

g→dhs : ∀ {A Γ Δ} → G⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DHS⟨ Γ ⁏ Δ ⊢ A ⟩
g→dhs = h→dhs ∘ g→h

g→dh₀ : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → DH⟨ Γ ⁏ ⌀ ⊢ A ⟩
g→dh₀ = h→dh₀ ∘ g→h

g→dh : ∀ {A Γ Δ} → G⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DH⟨ Γ ⁏ Δ ⊢ A ⟩
g→dh = h→dh ∘ g→h


-- Additional translations from dyadic Hilbert-style linear.

dhs₀₀→chs : ∀ {A} → DHS⟨ ⌀ ⁏ ⌀ ⊢ A ⟩ → CHS.⊢ A
dhs₀₀→chs = hs₀→chs ∘ dhs₀→hs

dhs₀→chs : ∀ {A Γ} → DHS⟨ Γ ⁏ ⌀ ⊢ A ⟩ → CHS.⊢ Γ ▻⋯▻ A
dhs₀→chs = hs→chs ∘ dhs₀→hs

dhs→chs : ∀ {A Γ Δ} → DHS⟨ Γ ⁏ Δ ⊢ A ⟩ → CHS.⊢ Γ ⧺ (□⋆ Δ) ▻⋯▻ A
dhs→chs = hs→chs ∘ dhs→hs

dhs₀₀→ch : ∀ {A} → DHS⟨ ⌀ ⁏ ⌀ ⊢ A ⟩ → CH.⊢ A
dhs₀₀→ch = hs₀→ch ∘ dhs₀→hs

dhs₀→ch : ∀ {A Γ} → DHS⟨ Γ ⁏ ⌀ ⊢ A ⟩ → CH.⊢ Γ ▻⋯▻ A
dhs₀→ch = hs→ch ∘ dhs₀→hs

dhs→ch : ∀ {A Γ Δ} → DHS⟨ Γ ⁏ Δ ⊢ A ⟩ → CH.⊢ Γ ⧺ (□⋆ Δ) ▻⋯▻ A
dhs→ch = hs→ch ∘ dhs→hs

dhs₀→h : ∀ {A Γ} → DHS⟨ Γ ⁏ ⌀ ⊢ A ⟩ → H⟨ Γ ⊢ A ⟩
dhs₀→h = hs→h ∘ dhs₀→hs

dhs→h : ∀ {A Γ Δ} → DHS⟨ Γ ⁏ Δ ⊢ A ⟩ → H⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dhs→h = hs→h ∘ dhs→hs

dhs₀→g : ∀ {A Γ} → DHS⟨ Γ ⁏ ⌀ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
dhs₀→g = hs→g ∘ dhs₀→hs

dhs→g : ∀ {A Γ Δ} → DHS⟨ Γ ⁏ Δ ⊢ A ⟩ → G⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dhs→g = hs→g ∘ dhs→hs

dhs→dg : ∀ {A Γ Δ} → DHS⟨ Γ ⁏ Δ ⊢ A ⟩ → DG⟨ Γ ⁏ Δ ⊢ A ⟩
dhs→dg = dh→dg ∘ dhs→dh

dhs₀→lg : ∀ {x A Γ Λ} → DHS⟨ Γ ⁏ ⌀ ⊢ A ⟩ → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩
dhs₀→lg = hs→lg ∘ dhs₀→hs

dhs→lg : ∀ {x A Γ Δ Λ} → DHS⟨ Γ ⁏ Δ ⊢ A ⟩ → LG⟨ Γ ⧺ (□⋆ Δ) ⁏ Λ ⊢ A ◎ x ⟩
dhs→lg = hs→lg ∘ dhs→hs


-- Additional translations from dyadic Hilbert-style.

dh₀₀→chs : ∀ {A} → DH⟨ ⌀ ⁏ ⌀ ⊢ A ⟩ → CHS.⊢ A
dh₀₀→chs = h₀→chs ∘ dh₀→h

dh₀→chs : ∀ {A Γ} → DH⟨ Γ ⁏ ⌀ ⊢ A ⟩ → CHS.⊢ Γ ▻⋯▻ A
dh₀→chs = h→chs ∘ dh₀→h

dh→chs : ∀ {A Γ Δ} → DH⟨ Γ ⁏ Δ ⊢ A ⟩ → CHS.⊢ Γ ⧺ (□⋆ Δ) ▻⋯▻ A
dh→chs = h→chs ∘ dh→h

dh₀₀→ch : ∀ {A} → DH⟨ ⌀ ⁏ ⌀ ⊢ A ⟩ → CH.⊢ A
dh₀₀→ch = h₀→ch ∘ dh₀→h

dh₀→ch : ∀ {A Γ} → DH⟨ Γ ⁏ ⌀ ⊢ A ⟩ → CH.⊢ Γ ▻⋯▻ A
dh₀→ch = h→ch ∘ dh₀→h

dh→ch : ∀ {A Γ Δ} → DH⟨ Γ ⁏ Δ ⊢ A ⟩ → CH.⊢ Γ ⧺ (□⋆ Δ) ▻⋯▻ A
dh→ch = h→ch ∘ dh→h

dh₀→hs : ∀ {A Γ} → DH⟨ Γ ⁏ ⌀ ⊢ A ⟩ → HS⟨ Γ ⊢ A ⟩
dh₀→hs = h→hs ∘ dh₀→h

dh→hs : ∀ {A Γ Δ} → DH⟨ Γ ⁏ Δ ⊢ A ⟩ → HS⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dh→hs = h→hs ∘ dh→h

dh₀→g : ∀ {A Γ} → DH⟨ Γ ⁏ ⌀ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
dh₀→g = h→g ∘ dh₀→h

dh→g : ∀ {A Γ Δ} → DH⟨ Γ ⁏ Δ ⊢ A ⟩ → G⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dh→g = h→g ∘ dh→h

dh₀→lg : ∀ {x A Γ Λ} → DH⟨ Γ ⁏ ⌀ ⊢ A ⟩ → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩
dh₀→lg = h→lg ∘ dh₀→h

dh→lg : ∀ {x A Γ Δ Λ} → DH⟨ Γ ⁏ Δ ⊢ A ⟩ → LG⟨ Γ ⧺ (□⋆ Δ) ⁏ Λ ⊢ A ◎ x ⟩
dh→lg = h→lg ∘ dh→h


-- Additional translations from dyadic Gentzen-style.

dg₀₀→chs : ∀ {A} → DG⟨ ⌀ ⁏ ⌀ ⊢ A ⟩ → CHS.⊢ A
dg₀₀→chs = dh₀→chs ∘ dg→dh

dg₀→chs : ∀ {A Γ} → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩ → CHS.⊢ Γ ▻⋯▻ A
dg₀→chs = dh→chs ∘ dg→dh

dg→chs : ∀ {A Γ Δ} → DG⟨ Γ ⁏ Δ ⊢ A ⟩ → CHS.⊢ Γ ⧺ (□⋆ Δ) ▻⋯▻ A
dg→chs = dh→chs ∘ dg→dh

dg₀₀→ch : ∀ {A} → DG⟨ ⌀ ⁏ ⌀ ⊢ A ⟩ → CH.⊢ A
dg₀₀→ch = dh₀→ch ∘ dg→dh

dg₀→ch : ∀ {A Γ} → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩ → CH.⊢ Γ ▻⋯▻ A
dg₀→ch = dh→ch ∘ dg→dh

dg→ch : ∀ {A Γ Δ} → DG⟨ Γ ⁏ Δ ⊢ A ⟩ → CH.⊢ Γ ⧺ (□⋆ Δ) ▻⋯▻ A
dg→ch = dh→ch ∘ dg→dh

dg₀→hs : ∀ {A Γ} → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩ → HS⟨ Γ ⊢ A ⟩
dg₀→hs = dh₀→hs ∘ dg→dh

dg→hs : ∀ {A Γ Δ} → DG⟨ Γ ⁏ Δ ⊢ A ⟩ → HS⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dg→hs = dh→hs ∘ dg→dh

dg₀→h : ∀ {A Γ} → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩ → H⟨ Γ ⊢ A ⟩
dg₀→h = dh₀→h ∘ dg→dh

dg→h : ∀ {A Γ Δ} → DG⟨ Γ ⁏ Δ ⊢ A ⟩ → H⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dg→h = dh→h ∘ dg→dh

-- NOTE: Direct translation fails the termination check.
dg₀→g : ∀ {A Γ} → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
dg₀→g = h→g ∘ dg₀→h

dg→g : ∀ {A Γ Δ} → DG⟨ Γ ⁏ Δ ⊢ A ⟩ → G⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dg→g = h→g ∘ dg→h

dg→dhs : ∀ {A Γ Δ} → DG⟨ Γ ⁏ Δ ⊢ A ⟩ → DHS⟨ Γ ⁏ Δ ⊢ A ⟩
dg→dhs = dh→dhs ∘ dg→dh

dg₀→lg : ∀ {x A Γ Λ} → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩ → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩
dg₀→lg = g→lg ∘ dg₀→g

dg→lg : ∀ {x A Γ Δ Λ} → DG⟨ Γ ⁏ Δ ⊢ A ⟩ → LG⟨ Γ ⧺ (□⋆ Δ) ⁏ Λ ⊢ A ◎ x ⟩
dg→lg = g→lg ∘ dg→g


-- Additional translations from labelled Gentzen-style.

lg₀→chs : ∀ {x A Λ} → LG⟨ ⌀ ⁏ Λ ⊢ A ◎ x ⟩ → CHS.⊢ A
lg₀→chs = h₀→chs ∘ lg→h

lg→chs : ∀ {x A Γ Λ} → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩ → CHS.⊢ Γ ▻⋯▻ A
lg→chs = h→chs ∘ lg→h

lg₀→ch : ∀ {x A Λ} → LG⟨ ⌀ ⁏ Λ ⊢ A ◎ x ⟩ → CH.⊢ A
lg₀→ch = h₀→ch ∘ lg→h

lg→ch : ∀ {x A Γ Λ} → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩ → CH.⊢ Γ ▻⋯▻ A
lg→ch = h→ch ∘ lg→h

lg→hs : ∀ {x A Γ Λ} → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩ → HS⟨ Γ ⊢ A ⟩
lg→hs = h→hs ∘ lg→h

lg→dhs₀ : ∀ {x A Γ Λ} → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩ → DHS⟨ Γ ⁏ ⌀ ⊢ A ⟩
lg→dhs₀ = h→dhs₀ ∘ lg→h

lg→dhs : ∀ {x A Γ Δ Λ} → LG⟨ Γ ⧺ (□⋆ Δ) ⁏ Λ ⊢ A ◎ x ⟩ → DHS⟨ Γ ⁏ Δ ⊢ A ⟩
lg→dhs = h→dhs ∘ lg→h

lg→dh₀ : ∀ {x A Γ Λ} → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩ → DH⟨ Γ ⁏ ⌀ ⊢ A ⟩
lg→dh₀ = h→dh₀ ∘ lg→h

lg→dh : ∀ {x A Γ Δ Λ} → LG⟨ Γ ⧺ (□⋆ Δ) ⁏ Λ ⊢ A ◎ x ⟩ → DH⟨ Γ ⁏ Δ ⊢ A ⟩
lg→dh = h→dh ∘ lg→h

lg→dg₀ : ∀ {x A Γ Λ} → LG⟨ Γ ⁏ Λ ⊢ A ◎ x ⟩ → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩
lg→dg₀ = h→dg₀ ∘ lg→h

lg→dg : ∀ {x A Γ Δ Λ} → LG⟨ Γ ⧺ (□⋆ Δ) ⁏ Λ ⊢ A ◎ x ⟩ → DG⟨ Γ ⁏ Δ ⊢ A ⟩
lg→dg = h→dg ∘ lg→h
