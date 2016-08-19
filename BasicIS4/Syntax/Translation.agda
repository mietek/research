-- Translation between different formalisations of syntax.

module BasicIS4.Syntax.Translation where

open import BasicIS4.Syntax.Common public

import BasicIS4.Syntax.ClosedHilbertLinear as CHL
import BasicIS4.Syntax.ClosedHilbert as CH
import BasicIS4.Syntax.HilbertLinear as HL
import BasicIS4.Syntax.Hilbert as H
import BasicIS4.Syntax.Gentzen as G
import BasicIS4.Syntax.DyadicHilbertLinear as DHL
import BasicIS4.Syntax.DyadicHilbert as DH
import BasicIS4.Syntax.DyadicGentzen as DG

open HL using () renaming (_⊢×_ to HL⟨_⊢×_⟩ ; _⊢_ to HL⟨_⊢_⟩) public
open H using () renaming (_⊢_ to H⟨_⊢_⟩ ; _⊢⋆_ to H⟨_⊢⋆_⟩) public
open G using () renaming (_⊢_ to G⟨_⊢_⟩ ; _⊢⋆_ to G⟨_⊢⋆_⟩) public
open DHL using () renaming (_⁏_⊢×_ to DHL⟨_⁏_⊢×_⟩ ; _⁏_⊢_ to DHL⟨_⁏_⊢_⟩) public
open DH using () renaming (_⁏_⊢_ to DH⟨_⁏_⊢_⟩) public
open DG using () renaming (_⁏_⊢_ to DG⟨_⁏_⊢_⟩ ; _⁏_⊢⋆_ to DG⟨_⁏_⊢⋆_⟩) public


-- Translation from closed Hilbert-style linear to closed Hilbert-style.

chl→ch : ∀ {A} → CHL.⊢ A → CH.⊢ A
chl→ch (Π , ts) = chl×→ch ts top
  where
    chl×→ch : ∀ {A Π} → CHL.⊢× Π → A ∈ Π → CH.⊢ A
    chl×→ch (CHL.mp i j ts) top     = CH.app (chl×→ch ts i) (chl×→ch ts j)
    chl×→ch (CHL.ci ts)     top     = CH.ci
    chl×→ch (CHL.ck ts)     top     = CH.ck
    chl×→ch (CHL.cs ts)     top     = CH.cs
    chl×→ch (CHL.nec ss ts) top     = CH.box (chl×→ch ss top)
    chl×→ch (CHL.cdist ts)  top     = CH.cdist
    chl×→ch (CHL.cup ts)    top     = CH.cup
    chl×→ch (CHL.cdown ts)  top     = CH.cdown
    chl×→ch (CHL.cpair ts)  top     = CH.cpair
    chl×→ch (CHL.cfst ts)   top     = CH.cfst
    chl×→ch (CHL.csnd ts)   top     = CH.csnd
    chl×→ch (CHL.tt ts)     top     = CH.tt
    chl×→ch (CHL.mp i j ts) (pop k) = chl×→ch ts k
    chl×→ch (CHL.ci ts)     (pop k) = chl×→ch ts k
    chl×→ch (CHL.ck ts)     (pop k) = chl×→ch ts k
    chl×→ch (CHL.cs ts)     (pop k) = chl×→ch ts k
    chl×→ch (CHL.nec ss ts) (pop k) = chl×→ch ts k
    chl×→ch (CHL.cdist ts)  (pop k) = chl×→ch ts k
    chl×→ch (CHL.cup ts)    (pop k) = chl×→ch ts k
    chl×→ch (CHL.cdown ts)  (pop k) = chl×→ch ts k
    chl×→ch (CHL.cpair ts)  (pop k) = chl×→ch ts k
    chl×→ch (CHL.cfst ts)   (pop k) = chl×→ch ts k
    chl×→ch (CHL.csnd ts)   (pop k) = chl×→ch ts k
    chl×→ch (CHL.tt ts)     (pop k) = chl×→ch ts k


-- Translation from closed Hilbert-style to closed Hilbert-style linear.

ch→chl : ∀ {A} → CH.⊢ A → CHL.⊢ A
ch→chl (CH.app t u) = CHL.app (ch→chl t) (ch→chl u)
ch→chl CH.ci        = ⌀ , CHL.ci CHL.nil
ch→chl CH.ck        = ⌀ , CHL.ck CHL.nil
ch→chl CH.cs        = ⌀ , CHL.cs CHL.nil
ch→chl (CH.box t)   = CHL.box (ch→chl t)
ch→chl CH.cdist     = ⌀ , CHL.cdist CHL.nil
ch→chl CH.cup       = ⌀ , CHL.cup CHL.nil
ch→chl CH.cdown     = ⌀ , CHL.cdown CHL.nil
ch→chl CH.cpair     = ⌀ , CHL.cpair CHL.nil
ch→chl CH.cfst      = ⌀ , CHL.cfst CHL.nil
ch→chl CH.csnd      = ⌀ , CHL.csnd CHL.nil
ch→chl CH.tt        = ⌀ , CHL.tt CHL.nil


-- Translation from Hilbert-style linear to Hilbert-style.

hl→h : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → H⟨ Γ ⊢ A ⟩
hl→h (Π , ts) = hl×→h ts top
  where
    hl×→h : ∀ {A Π Γ} → HL⟨ Γ ⊢× Π ⟩ → A ∈ Π → H⟨ Γ ⊢ A ⟩
    hl×→h (HL.var i ts)  top     = H.var i
    hl×→h (HL.mp i j ts) top     = H.app (hl×→h ts i) (hl×→h ts j)
    hl×→h (HL.ci ts)     top     = H.ci
    hl×→h (HL.ck ts)     top     = H.ck
    hl×→h (HL.cs ts)     top     = H.cs
    hl×→h (HL.nec ss ts) top     = H.box (hl×→h ss top)
    hl×→h (HL.cdist ts)  top     = H.cdist
    hl×→h (HL.cup ts)    top     = H.cup
    hl×→h (HL.cdown ts)  top     = H.cdown
    hl×→h (HL.cpair ts)  top     = H.cpair
    hl×→h (HL.cfst ts)   top     = H.cfst
    hl×→h (HL.csnd ts)   top     = H.csnd
    hl×→h (HL.tt ts)     top     = H.tt
    hl×→h (HL.var i ts)  (pop k) = hl×→h ts k
    hl×→h (HL.mp i j ts) (pop k) = hl×→h ts k
    hl×→h (HL.ci ts)     (pop k) = hl×→h ts k
    hl×→h (HL.ck ts)     (pop k) = hl×→h ts k
    hl×→h (HL.cs ts)     (pop k) = hl×→h ts k
    hl×→h (HL.nec ss ts) (pop k) = hl×→h ts k
    hl×→h (HL.cdist ts)  (pop k) = hl×→h ts k
    hl×→h (HL.cup ts)    (pop k) = hl×→h ts k
    hl×→h (HL.cdown ts)  (pop k) = hl×→h ts k
    hl×→h (HL.cpair ts)  (pop k) = hl×→h ts k
    hl×→h (HL.cfst ts)   (pop k) = hl×→h ts k
    hl×→h (HL.csnd ts)   (pop k) = hl×→h ts k
    hl×→h (HL.tt ts)     (pop k) = hl×→h ts k


-- Translation from Hilbert-style to Hilbert-style linear.

h→hl : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → HL⟨ Γ ⊢ A ⟩
h→hl (H.var i)   = ⌀ , HL.var i HL.nil
h→hl (H.app t u) = HL.app (h→hl t) (h→hl u)
h→hl H.ci        = ⌀ , HL.ci HL.nil
h→hl H.ck        = ⌀ , HL.ck HL.nil
h→hl H.cs        = ⌀ , HL.cs HL.nil
h→hl (H.box t)   = HL.box (h→hl t)
h→hl H.cdist     = ⌀ , HL.cdist HL.nil
h→hl H.cup       = ⌀ , HL.cup HL.nil
h→hl H.cdown     = ⌀ , HL.cdown HL.nil
h→hl H.cpair     = ⌀ , HL.cpair HL.nil
h→hl H.cfst      = ⌀ , HL.cfst HL.nil
h→hl H.csnd      = ⌀ , HL.csnd HL.nil
h→hl H.tt        = ⌀ , HL.tt HL.nil


-- Translation from dyadic Hilbert-style linear to dyadic Hilbert-style.

dhl→dh : ∀ {A Γ Δ} → DHL⟨ Γ ⁏ Δ ⊢ A ⟩ → DH⟨ Γ ⁏ Δ ⊢ A ⟩
dhl→dh (Π , ts) = dhl×→dh ts top
  where
    dhl×→dh : ∀ {A Π Γ Δ} → DHL⟨ Γ ⁏ Δ ⊢× Π ⟩ → A ∈ Π → DH⟨ Γ ⁏ Δ ⊢ A ⟩
    dhl×→dh (DHL.var i ts)  top     = DH.var i
    dhl×→dh (DHL.mp i j ts) top     = DH.app (dhl×→dh ts i) (dhl×→dh ts j)
    dhl×→dh (DHL.ci ts)     top     = DH.ci
    dhl×→dh (DHL.ck ts)     top     = DH.ck
    dhl×→dh (DHL.cs ts)     top     = DH.cs
    dhl×→dh (DHL.mvar i ts) top     = DH.mvar i
    dhl×→dh (DHL.nec ss ts) top     = DH.box (dhl×→dh ss top)
    dhl×→dh (DHL.cdist ts)  top     = DH.cdist
    dhl×→dh (DHL.cup ts)    top     = DH.cup
    dhl×→dh (DHL.cdown ts)  top     = DH.cdown
    dhl×→dh (DHL.cpair ts)  top     = DH.cpair
    dhl×→dh (DHL.cfst ts)   top     = DH.cfst
    dhl×→dh (DHL.csnd ts)   top     = DH.csnd
    dhl×→dh (DHL.tt ts)     top     = DH.tt
    dhl×→dh (DHL.var i ts)  (pop k) = dhl×→dh ts k
    dhl×→dh (DHL.mp i j ts) (pop k) = dhl×→dh ts k
    dhl×→dh (DHL.ci ts)     (pop k) = dhl×→dh ts k
    dhl×→dh (DHL.ck ts)     (pop k) = dhl×→dh ts k
    dhl×→dh (DHL.cs ts)     (pop k) = dhl×→dh ts k
    dhl×→dh (DHL.mvar i ts) (pop k) = dhl×→dh ts k
    dhl×→dh (DHL.nec ss ts) (pop k) = dhl×→dh ts k
    dhl×→dh (DHL.cdist ts)  (pop k) = dhl×→dh ts k
    dhl×→dh (DHL.cup ts)    (pop k) = dhl×→dh ts k
    dhl×→dh (DHL.cdown ts)  (pop k) = dhl×→dh ts k
    dhl×→dh (DHL.cpair ts)  (pop k) = dhl×→dh ts k
    dhl×→dh (DHL.cfst ts)   (pop k) = dhl×→dh ts k
    dhl×→dh (DHL.csnd ts)   (pop k) = dhl×→dh ts k
    dhl×→dh (DHL.tt ts)     (pop k) = dhl×→dh ts k


-- Translation from dyadic Hilbert-style to dyadic Hilbert-style linear

dh→dhl : ∀ {A Γ Δ} → DH⟨ Γ ⁏ Δ ⊢ A ⟩ → DHL⟨ Γ ⁏ Δ ⊢ A ⟩
dh→dhl (DH.var i)   = ⌀ , DHL.var i DHL.nil
dh→dhl (DH.app t u) = DHL.app (dh→dhl t) (dh→dhl u)
dh→dhl DH.ci        = ⌀ , DHL.ci DHL.nil
dh→dhl DH.ck        = ⌀ , DHL.ck DHL.nil
dh→dhl DH.cs        = ⌀ , DHL.cs DHL.nil
dh→dhl (DH.mvar i)  = ⌀ , DHL.mvar i DHL.nil
dh→dhl (DH.box t)   = DHL.box (dh→dhl t)
dh→dhl DH.cdist     = ⌀ , DHL.cdist DHL.nil
dh→dhl DH.cup       = ⌀ , DHL.cup DHL.nil
dh→dhl DH.cdown     = ⌀ , DHL.cdown DHL.nil
dh→dhl DH.cpair     = ⌀ , DHL.cpair DHL.nil
dh→dhl DH.cfst      = ⌀ , DHL.cfst DHL.nil
dh→dhl DH.csnd      = ⌀ , DHL.csnd DHL.nil
dh→dhl DH.tt        = ⌀ , DHL.tt DHL.nil


-- Deduction and detachment theorems for Hilbert-style linear.

hl-lam : ∀ {A B Γ} → HL⟨ Γ , A ⊢ B ⟩ → HL⟨ Γ ⊢ A ▻ B ⟩
hl-lam = h→hl ∘ H.lam ∘ hl→h

hl-lam⋆₀ : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → HL⟨ ⌀ ⊢ Γ ▻⋯▻ A ⟩
hl-lam⋆₀ = h→hl ∘ H.lam⋆₀ ∘ hl→h

hl-det : ∀ {A B Γ} → HL⟨ Γ ⊢ A ▻ B ⟩ → HL⟨ Γ , A ⊢ B ⟩
hl-det = h→hl ∘ H.det ∘ hl→h

hl-det⋆₀ : ∀ {A Γ} → HL⟨ ⌀ ⊢ Γ ▻⋯▻ A ⟩ → HL⟨ Γ ⊢ A ⟩
hl-det⋆₀ = h→hl ∘ H.det⋆₀ ∘ hl→h


-- Deduction and detachment theorems for dyadic Hilbert-style linear.

dhl-lam : ∀ {A B Γ Δ} → DHL⟨ Γ , A ⁏ Δ ⊢ B ⟩ → DHL⟨ Γ ⁏ Δ ⊢ A ▻ B ⟩
dhl-lam = dh→dhl ∘ DH.lam ∘ dhl→dh

dhl-lam⋆₀ : ∀ {A Γ Δ} → DHL⟨ Γ ⁏ Δ ⊢ A ⟩ → DHL⟨ ⌀ ⁏ Δ ⊢ Γ ▻⋯▻ A ⟩
dhl-lam⋆₀ = dh→dhl ∘ DH.lam⋆₀ ∘ dhl→dh

dhl-mlam : ∀ {A B Γ Δ} → DHL⟨ Γ ⁏ Δ , A ⊢ B ⟩ → DHL⟨ Γ ⁏ Δ ⊢ □ A ▻ B ⟩
dhl-mlam = dh→dhl ∘ DH.mlam ∘ dhl→dh

dhl-mlam⋆₀ : ∀ {Δ A Γ} → DHL⟨ Γ ⁏ Δ ⊢ A ⟩ → DHL⟨ Γ ⁏ ⌀ ⊢ □⋆ Δ ▻⋯▻ A ⟩
dhl-mlam⋆₀ = dh→dhl ∘ DH.mlam⋆₀ ∘ dhl→dh

dhl-det : ∀ {A B Γ Δ} → DHL⟨ Γ ⁏ Δ ⊢ A ▻ B ⟩ → DHL⟨ Γ , A ⁏ Δ ⊢ B ⟩
dhl-det = dh→dhl ∘ DH.det ∘ dhl→dh

dhl-det⋆₀ : ∀ {A Γ Δ} → DHL⟨ ⌀ ⁏ Δ ⊢ Γ ▻⋯▻ A ⟩ → DHL⟨ Γ ⁏ Δ ⊢ A ⟩
dhl-det⋆₀ = dh→dhl ∘ DH.det⋆₀ ∘ dhl→dh

dhl-mdet : ∀ {A B Γ Δ} → DHL⟨ Γ ⁏ Δ ⊢ □ A ▻ B ⟩ → DHL⟨ Γ ⁏ Δ , A ⊢ B ⟩
dhl-mdet = dh→dhl ∘ DH.mdet ∘ dhl→dh

dhl-mdet⋆₀ : ∀ {Δ A Γ} → DHL⟨ Γ ⁏ ⌀ ⊢ □⋆ Δ ▻⋯▻ A ⟩ → DHL⟨ Γ ⁏ Δ ⊢ A ⟩
dhl-mdet⋆₀ = dh→dhl ∘ DH.mdet⋆₀ ∘ dhl→dh


-- Context manipulation for dyadic Hilbert-style linear.

dhl-merge : ∀ {Δ A Γ} → DHL⟨ Γ ⁏ Δ ⊢ A ⟩ → DHL⟨ Γ ⧺ (□⋆ Δ) ⁏ ⌀ ⊢ A ⟩
dhl-merge {Δ} = dh→dhl ∘ DH.merge ∘ dhl→dh

dhl-split : ∀ {Δ A Γ} → DHL⟨ Γ ⧺ (□⋆ Δ) ⁏ ⌀ ⊢ A ⟩ → DHL⟨ Γ ⁏ Δ ⊢ A ⟩
dhl-split {Δ} = dh→dhl ∘ DH.split ∘ dhl→dh


-- Translation from closed Hilbert-style linear to Hilbert-style linear.

chl→hl₀ : ∀ {A} → CHL.⊢ A → HL⟨ ⌀ ⊢ A ⟩
chl→hl₀ (Π , ts) = Π , chl×→hl× ts
  where
    chl×→hl× : ∀ {Π} → CHL.⊢× Π → HL⟨ ⌀ ⊢× Π ⟩
    chl×→hl× CHL.nil         = HL.nil
    chl×→hl× (CHL.mp i j ts) = HL.mp i j (chl×→hl× ts)
    chl×→hl× (CHL.ci ts)     = HL.ci (chl×→hl× ts)
    chl×→hl× (CHL.ck ts)     = HL.ck (chl×→hl× ts)
    chl×→hl× (CHL.cs ts)     = HL.cs (chl×→hl× ts)
    chl×→hl× (CHL.cpair ts)  = HL.cpair (chl×→hl× ts)
    chl×→hl× (CHL.cfst ts)   = HL.cfst (chl×→hl× ts)
    chl×→hl× (CHL.csnd ts)   = HL.csnd (chl×→hl× ts)
    chl×→hl× (CHL.tt ts)     = HL.tt (chl×→hl× ts)
    chl×→hl× (CHL.nec ss ts) = HL.nec (chl×→hl× ss) (chl×→hl× ts)
    chl×→hl× (CHL.cdist ts)  = HL.cdist (chl×→hl× ts)
    chl×→hl× (CHL.cup ts)    = HL.cup (chl×→hl× ts)
    chl×→hl× (CHL.cdown ts)  = HL.cdown (chl×→hl× ts)

chl→hl : ∀ {A Γ} → CHL.⊢ Γ ▻⋯▻ A → HL⟨ Γ ⊢ A ⟩
chl→hl t = hl-det⋆₀ (chl→hl₀ t)


-- Translation from Hilbert-style linear to closed Hilbert-style linear.

hl₀→chl : ∀ {A} → HL⟨ ⌀ ⊢ A ⟩ → CHL.⊢ A
hl₀→chl (Π , ts) = Π , hl₀×→chl× ts
  where
    hl₀×→chl× : ∀ {Π} → HL⟨ ⌀ ⊢× Π ⟩ → CHL.⊢× Π
    hl₀×→chl× HL.nil         = CHL.nil
    hl₀×→chl× (HL.var () ts)
    hl₀×→chl× (HL.mp i j ts) = CHL.mp i j (hl₀×→chl× ts)
    hl₀×→chl× (HL.ci ts)     = CHL.ci (hl₀×→chl× ts)
    hl₀×→chl× (HL.ck ts)     = CHL.ck (hl₀×→chl× ts)
    hl₀×→chl× (HL.cs ts)     = CHL.cs (hl₀×→chl× ts)
    hl₀×→chl× (HL.cpair ts)  = CHL.cpair (hl₀×→chl× ts)
    hl₀×→chl× (HL.cfst ts)   = CHL.cfst (hl₀×→chl× ts)
    hl₀×→chl× (HL.csnd ts)   = CHL.csnd (hl₀×→chl× ts)
    hl₀×→chl× (HL.tt ts)     = CHL.tt (hl₀×→chl× ts)
    hl₀×→chl× (HL.nec ss ts) = CHL.nec (hl₀×→chl× ss) (hl₀×→chl× ts)
    hl₀×→chl× (HL.cdist ts)  = CHL.cdist (hl₀×→chl× ts)
    hl₀×→chl× (HL.cup ts)    = CHL.cup (hl₀×→chl× ts)
    hl₀×→chl× (HL.cdown ts)  = CHL.cdown (hl₀×→chl× ts)

hl→chl : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → CHL.⊢ Γ ▻⋯▻ A
hl→chl t = hl₀→chl (hl-lam⋆₀ t)


-- Translation from Hilbert-style linear to dyadic Hilbert-style linear.

hl→dhl₀ : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → DHL⟨ Γ ⁏ ⌀ ⊢ A ⟩
hl→dhl₀ (Π , ts) = Π , hl×→dhl₀× ts
  where
    hl×→dhl₀× : ∀ {Π Γ} → HL⟨ Γ ⊢× Π ⟩ → DHL⟨ Γ ⁏ ⌀ ⊢× Π ⟩
    hl×→dhl₀× HL.nil         = DHL.nil
    hl×→dhl₀× (HL.var i ts)  = DHL.var i (hl×→dhl₀× ts)
    hl×→dhl₀× (HL.mp i j ts) = DHL.mp i j (hl×→dhl₀× ts)
    hl×→dhl₀× (HL.ci ts)     = DHL.ci (hl×→dhl₀× ts)
    hl×→dhl₀× (HL.ck ts)     = DHL.ck (hl×→dhl₀× ts)
    hl×→dhl₀× (HL.cs ts)     = DHL.cs (hl×→dhl₀× ts)
    hl×→dhl₀× (HL.nec ss ts) = DHL.nec (hl×→dhl₀× ss) (hl×→dhl₀× ts)
    hl×→dhl₀× (HL.cdist ts)  = DHL.cdist (hl×→dhl₀× ts)
    hl×→dhl₀× (HL.cup ts)    = DHL.cup (hl×→dhl₀× ts)
    hl×→dhl₀× (HL.cdown ts)  = DHL.cdown (hl×→dhl₀× ts)
    hl×→dhl₀× (HL.cpair ts)  = DHL.cpair (hl×→dhl₀× ts)
    hl×→dhl₀× (HL.cfst ts)   = DHL.cfst (hl×→dhl₀× ts)
    hl×→dhl₀× (HL.csnd ts)   = DHL.csnd (hl×→dhl₀× ts)
    hl×→dhl₀× (HL.tt ts)     = DHL.tt (hl×→dhl₀× ts)

hl→dhl : ∀ {A Γ Δ} → HL⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DHL⟨ Γ ⁏ Δ ⊢ A ⟩
hl→dhl = dhl-split ∘ hl→dhl₀


-- Translation from dyadic Hilbert-style linear to Hilbert-style linear.

dhl₀→hl : ∀ {A Γ} → DHL⟨ Γ ⁏ ⌀ ⊢ A ⟩ → HL⟨ Γ ⊢ A ⟩
dhl₀→hl (Π , ts) = Π , dhl₀×→hl× ts
  where
    dhl₀×→hl× : ∀ {Π Γ} → DHL⟨ Γ ⁏ ⌀ ⊢× Π ⟩ → HL⟨ Γ ⊢× Π ⟩
    dhl₀×→hl× DHL.nil          = HL.nil
    dhl₀×→hl× (DHL.var i ts)   = HL.var i (dhl₀×→hl× ts)
    dhl₀×→hl× (DHL.mp i j ts)  = HL.mp i j (dhl₀×→hl× ts)
    dhl₀×→hl× (DHL.ci ts)      = HL.ci (dhl₀×→hl× ts)
    dhl₀×→hl× (DHL.ck ts)      = HL.ck (dhl₀×→hl× ts)
    dhl₀×→hl× (DHL.cs ts)      = HL.cs (dhl₀×→hl× ts)
    dhl₀×→hl× (DHL.mvar () ts)
    dhl₀×→hl× (DHL.nec ss ts)  = HL.nec (dhl₀×→hl× ss) (dhl₀×→hl× ts)
    dhl₀×→hl× (DHL.cdist ts)   = HL.cdist (dhl₀×→hl× ts)
    dhl₀×→hl× (DHL.cup ts)     = HL.cup (dhl₀×→hl× ts)
    dhl₀×→hl× (DHL.cdown ts)   = HL.cdown (dhl₀×→hl× ts)
    dhl₀×→hl× (DHL.cpair ts)   = HL.cpair (dhl₀×→hl× ts)
    dhl₀×→hl× (DHL.cfst ts)    = HL.cfst (dhl₀×→hl× ts)
    dhl₀×→hl× (DHL.csnd ts)    = HL.csnd (dhl₀×→hl× ts)
    dhl₀×→hl× (DHL.tt ts)      = HL.tt (dhl₀×→hl× ts)

dhl→hl : ∀ {A Γ Δ} → DHL⟨ Γ ⁏ Δ ⊢ A ⟩ → HL⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dhl→hl = dhl₀→hl ∘ dhl-merge


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


-- Composition of Hilbert-style translations.

h₀→chl : ∀ {A} → H⟨ ⌀ ⊢ A ⟩ → CHL.⊢ A
h₀→chl = ch→chl ∘ h₀→ch

h→chl : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → CHL.⊢ Γ ▻⋯▻ A
h→chl = ch→chl ∘ h→ch

hl₀→ch : ∀ {A} → HL⟨ ⌀ ⊢ A ⟩ → CH.⊢ A
hl₀→ch = chl→ch ∘ hl₀→chl

hl→ch : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → CH.⊢ Γ ▻⋯▻ A
hl→ch = chl→ch ∘ hl→chl

chl→h₀ : ∀ {A} → CHL.⊢ A → H⟨ ⌀ ⊢ A ⟩
chl→h₀ = ch→h₀ ∘ chl→ch

chl→h : ∀ {A Γ} → CHL.⊢ Γ ▻⋯▻ A → H⟨ Γ ⊢ A ⟩
chl→h = ch→h ∘ chl→ch

ch→hl₀ : ∀ {A} → CH.⊢ A → HL⟨ ⌀ ⊢ A ⟩
ch→hl₀ = chl→hl ∘ ch→chl

ch→hl : ∀ {A Γ} → CH.⊢ Γ ▻⋯▻ A → HL⟨ Γ ⊢ A ⟩
ch→hl = chl→hl ∘ ch→chl


-- Composition of dyadic Hilbert-style translations.

dh₀→hl : ∀ {A Γ} → DH⟨ Γ ⁏ ⌀ ⊢ A ⟩ → HL⟨ Γ ⊢ A ⟩
dh₀→hl = h→hl ∘ dh₀→h

dh→hl : ∀ {A Γ Δ} → DH⟨ Γ ⁏ Δ ⊢ A ⟩ → HL⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dh→hl = h→hl ∘ dh→h

dhl₀→h : ∀ {A Γ} → DHL⟨ Γ ⁏ ⌀ ⊢ A ⟩ → H⟨ Γ ⊢ A ⟩
dhl₀→h = hl→h ∘ dhl₀→hl

dhl→h : ∀ {A Γ Δ} → DHL⟨ Γ ⁏ Δ ⊢ A ⟩ → H⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dhl→h = hl→h ∘ dhl→hl

hl→dh₀ : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → DH⟨ Γ ⁏ ⌀ ⊢ A ⟩
hl→dh₀ = h→dh₀ ∘ hl→h

hl→dh : ∀ {A Γ Δ} → HL⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DH⟨ Γ ⁏ Δ ⊢ A ⟩
hl→dh = h→dh ∘ hl→h

h→dhl₀ : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → DHL⟨ Γ ⁏ ⌀ ⊢ A ⟩
h→dhl₀ = hl→dhl₀ ∘ h→hl

h→dhl : ∀ {A Γ Δ} → H⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DHL⟨ Γ ⁏ Δ ⊢ A ⟩
h→dhl = hl→dhl ∘ h→hl


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

hl→g : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
hl→g = h→g ∘ hl→h

ch→g₀ : ∀ {A} → CH.⊢ A → G⟨ ⌀ ⊢ A ⟩
ch→g₀ = h→g ∘ ch→h₀

ch→g : ∀ {A Γ} → CH.⊢ Γ ▻⋯▻ A → G⟨ Γ ⊢ A ⟩
ch→g = h→g ∘ ch→h

chl→g₀ : ∀ {A} → CHL.⊢ A → G⟨ ⌀ ⊢ A ⟩
chl→g₀ = h→g ∘ chl→h₀

chl→g : ∀ {A Γ} → CHL.⊢ Γ ▻⋯▻ A → G⟨ Γ ⊢ A ⟩
chl→g = h→g ∘ chl→h


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

  g→h⋆ : ∀ {Π Γ} → G⟨ Γ ⊢⋆ Π ⟩ → H⟨ Γ ⊢⋆ Π ⟩
  g→h⋆ {⌀}     ∙        = ∙
  g→h⋆ {Π , A} (ts , t) = g→h⋆ ts , g→h t

g→hl : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HL⟨ Γ ⊢ A ⟩
g→hl = h→hl ∘ g→h

g₀→ch : ∀ {A} → G⟨ ⌀ ⊢ A ⟩ → CH.⊢ A
g₀→ch = h₀→ch ∘ g→h

g→ch : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → CH.⊢ Γ ▻⋯▻ A
g→ch = h→ch ∘ g→h

g₀→chl : ∀ {A} → G⟨ ⌀ ⊢ A ⟩ → CHL.⊢ A
g₀→chl = h₀→chl ∘ g→h

g→chl : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → CHL.⊢ Γ ▻⋯▻ A
g→chl = h→chl ∘ g→h


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

dhl→dg : ∀ {A Γ Δ} → DHL⟨ Γ ⁏ Δ ⊢ A ⟩ → DG⟨ Γ ⁏ Δ ⊢ A ⟩
dhl→dg = dh→dg ∘ dhl→dh

h→dg₀ : ∀ {A Γ} → H⟨ Γ ⊢ A ⟩ → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩
h→dg₀ = dh→dg ∘ h→dh₀

h→dg : ∀ {A Γ Δ} → H⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DG⟨ Γ ⁏ Δ ⊢ A ⟩
h→dg = dh→dg ∘ h→dh

hl→dg₀ : ∀ {A Γ} → HL⟨ Γ ⊢ A ⟩ → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩
hl→dg₀ = dh→dg ∘ hl→dh₀

hl→dg : ∀ {A Γ Δ} → HL⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DG⟨ Γ ⁏ Δ ⊢ A ⟩
hl→dg = dh→dg ∘ hl→dh


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

dg→dhl : ∀ {A Γ Δ} → DG⟨ Γ ⁏ Δ ⊢ A ⟩ → DHL⟨ Γ ⁏ Δ ⊢ A ⟩
dg→dhl = dh→dhl ∘ dg→dh

dg₀→h : ∀ {A Γ} → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩ → H⟨ Γ ⊢ A ⟩
dg₀→h = dh₀→h ∘ dg→dh

dg→h : ∀ {A Γ Δ} → DG⟨ Γ ⁏ Δ ⊢ A ⟩ → H⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dg→h = dh→h ∘ dg→dh

dg₀→hl : ∀ {A Γ} → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩ → HL⟨ Γ ⊢ A ⟩
dg₀→hl = dh₀→hl ∘ dg→dh

dg→hl : ∀ {A Γ Δ} → DG⟨ Γ ⁏ Δ ⊢ A ⟩ → HL⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dg→hl = dh→hl ∘ dg→dh


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

  g→dg₀⋆ : ∀ {Π Γ} → G⟨ Γ ⊢⋆ Π ⟩ → DG⟨ Γ ⁏ ⌀ ⊢⋆ Π ⟩
  g→dg₀⋆ {⌀}     ∙        = ∙
  g→dg₀⋆ {Π , A} (ts , t) = g→dg₀⋆ ts , g→dg₀ t

g→dg : ∀ {A Γ Δ} → G⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → DG⟨ Γ ⁏ Δ ⊢ A ⟩
g→dg = DG.split ∘ g→dg₀


-- Translation from dyadic Gentzen-style to Gentzen-style.

-- NOTE: Direct translation fails the termination check.
dg→g₀ : ∀ {A Γ} → DG⟨ Γ ⁏ ⌀ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
dg→g₀ = h→g ∘ dg→h

dg→g : ∀ {A Γ Δ} → DG⟨ Γ ⁏ Δ ⊢ A ⟩ → G⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dg→g = dg→g₀ ∘ DG.merge
