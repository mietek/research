-- Translation between different formalisations of syntax.

module New.BasicIS4.Syntax.Translation where

open import New.BasicIS4.Syntax.Common public

import New.BasicIS4.Syntax.ClosedHilbertLinear as L
import New.BasicIS4.Syntax.ClosedHilbert as T
import New.BasicIS4.Syntax.OpenHilbertLinear as LC
import New.BasicIS4.Syntax.OpenHilbert as TC
import New.BasicIS4.Syntax.OpenGentzen as GTC
import New.BasicIS4.Syntax.OpenDyadicHilbertLinear as LCP
import New.BasicIS4.Syntax.OpenDyadicHilbert as TCP
import New.BasicIS4.Syntax.OpenDyadicGentzen as GTCP

open LC using () renaming (_⊢×_ to LC⟨_⊢×_⟩ ; _⊢_ to LC⟨_⊢_⟩) public
open TC using () renaming (_⊢_ to TC⟨_⊢_⟩ ; _⊢⋆_ to TC⟨_⊢⋆_⟩) public
open GTC using () renaming (_⊢_ to GTC⟨_⊢_⟩ ; _⊢⋆_ to GTC⟨_⊢⋆_⟩) public
open LCP using () renaming (_⁏_⊢×_ to LCP⟨_⁏_⊢×_⟩ ; _⁏_⊢_ to LCP⟨_⁏_⊢_⟩) public
open TCP using () renaming (_⁏_⊢_ to TCP⟨_⁏_⊢_⟩) public
open GTCP using () renaming (_⁏_⊢_ to GTCP⟨_⁏_⊢_⟩ ; _⁏_⊢⋆_ to GTCP⟨_⁏_⊢⋆_⟩) public


-- Translation from list-shaped to tree-shaped variant.

l→t : ∀ {A} → L.⊢ A → T.⊢ A
l→t (Π , ts) = l×→t ts top
  where
    l×→t : ∀ {A Π} → L.⊢× Π → A ∈ Π → T.⊢ A
    l×→t (L.mp i j ts) top     = T.app (l×→t ts i) (l×→t ts j)
    l×→t (L.ci ts)     top     = T.ci
    l×→t (L.ck ts)     top     = T.ck
    l×→t (L.cs ts)     top     = T.cs
    l×→t (L.nec ss ts) top     = T.box (l×→t ss top)
    l×→t (L.cdist ts)  top     = T.cdist
    l×→t (L.cup ts)    top     = T.cup
    l×→t (L.cdown ts)  top     = T.cdown
    l×→t (L.cpair ts)  top     = T.cpair
    l×→t (L.cfst ts)   top     = T.cfst
    l×→t (L.csnd ts)   top     = T.csnd
    l×→t (L.tt ts)     top     = T.tt
    l×→t (L.mp i j ts) (pop k) = l×→t ts k
    l×→t (L.ci ts)     (pop k) = l×→t ts k
    l×→t (L.ck ts)     (pop k) = l×→t ts k
    l×→t (L.cs ts)     (pop k) = l×→t ts k
    l×→t (L.nec ss ts) (pop k) = l×→t ts k
    l×→t (L.cdist ts)  (pop k) = l×→t ts k
    l×→t (L.cup ts)    (pop k) = l×→t ts k
    l×→t (L.cdown ts)  (pop k) = l×→t ts k
    l×→t (L.cpair ts)  (pop k) = l×→t ts k
    l×→t (L.cfst ts)   (pop k) = l×→t ts k
    l×→t (L.csnd ts)   (pop k) = l×→t ts k
    l×→t (L.tt ts)     (pop k) = l×→t ts k


-- Translation from tree-shaped to list-shaped variant.

t→l : ∀ {A} → T.⊢ A → L.⊢ A
t→l (T.app t u) = L.app (t→l t) (t→l u)
t→l T.ci        = ⌀ , L.ci L.nil
t→l T.ck        = ⌀ , L.ck L.nil
t→l T.cs        = ⌀ , L.cs L.nil
t→l (T.box t)   = L.box (t→l t)
t→l T.cdist     = ⌀ , L.cdist L.nil
t→l T.cup       = ⌀ , L.cup L.nil
t→l T.cdown     = ⌀ , L.cdown L.nil
t→l T.cpair     = ⌀ , L.cpair L.nil
t→l T.cfst      = ⌀ , L.cfst L.nil
t→l T.csnd      = ⌀ , L.csnd L.nil
t→l T.tt        = ⌀ , L.tt L.nil


-- Translation from list-shaped to tree-shaped variant, with context.

lc→tc : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → TC⟨ Γ ⊢ A ⟩
lc→tc (Π , ts) = lc×→tc ts top
  where
    lc×→tc : ∀ {A Π Γ} → LC⟨ Γ ⊢× Π ⟩ → A ∈ Π → TC⟨ Γ ⊢ A ⟩
    lc×→tc (LC.var i ts)  top     = TC.var i
    lc×→tc (LC.mp i j ts) top     = TC.app (lc×→tc ts i) (lc×→tc ts j)
    lc×→tc (LC.ci ts)     top     = TC.ci
    lc×→tc (LC.ck ts)     top     = TC.ck
    lc×→tc (LC.cs ts)     top     = TC.cs
    lc×→tc (LC.nec ss ts) top     = TC.box (lc×→tc ss top)
    lc×→tc (LC.cdist ts)  top     = TC.cdist
    lc×→tc (LC.cup ts)    top     = TC.cup
    lc×→tc (LC.cdown ts)  top     = TC.cdown
    lc×→tc (LC.cpair ts)  top     = TC.cpair
    lc×→tc (LC.cfst ts)   top     = TC.cfst
    lc×→tc (LC.csnd ts)   top     = TC.csnd
    lc×→tc (LC.tt ts)     top     = TC.tt
    lc×→tc (LC.var i ts)  (pop k) = lc×→tc ts k
    lc×→tc (LC.mp i j ts) (pop k) = lc×→tc ts k
    lc×→tc (LC.ci ts)     (pop k) = lc×→tc ts k
    lc×→tc (LC.ck ts)     (pop k) = lc×→tc ts k
    lc×→tc (LC.cs ts)     (pop k) = lc×→tc ts k
    lc×→tc (LC.nec ss ts) (pop k) = lc×→tc ts k
    lc×→tc (LC.cdist ts)  (pop k) = lc×→tc ts k
    lc×→tc (LC.cup ts)    (pop k) = lc×→tc ts k
    lc×→tc (LC.cdown ts)  (pop k) = lc×→tc ts k
    lc×→tc (LC.cpair ts)  (pop k) = lc×→tc ts k
    lc×→tc (LC.cfst ts)   (pop k) = lc×→tc ts k
    lc×→tc (LC.csnd ts)   (pop k) = lc×→tc ts k
    lc×→tc (LC.tt ts)     (pop k) = lc×→tc ts k


-- Translation from tree-shaped to list-shaped variant, with context.

tc→lc : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → LC⟨ Γ ⊢ A ⟩
tc→lc (TC.var i)   = ⌀ , LC.var i LC.nil
tc→lc (TC.app t u) = LC.app (tc→lc t) (tc→lc u)
tc→lc TC.ci        = ⌀ , LC.ci LC.nil
tc→lc TC.ck        = ⌀ , LC.ck LC.nil
tc→lc TC.cs        = ⌀ , LC.cs LC.nil
tc→lc (TC.box t)   = LC.box (tc→lc t)
tc→lc TC.cdist     = ⌀ , LC.cdist LC.nil
tc→lc TC.cup       = ⌀ , LC.cup LC.nil
tc→lc TC.cdown     = ⌀ , LC.cdown LC.nil
tc→lc TC.cpair     = ⌀ , LC.cpair LC.nil
tc→lc TC.cfst      = ⌀ , LC.cfst LC.nil
tc→lc TC.csnd      = ⌀ , LC.csnd LC.nil
tc→lc TC.tt        = ⌀ , LC.tt LC.nil


-- Translation from list-shaped to tree-shaped variant, with context pair.

lcp→tcp : ∀ {A Γ Δ} → LCP⟨ Γ ⁏ Δ ⊢ A ⟩ → TCP⟨ Γ ⁏ Δ ⊢ A ⟩
lcp→tcp (Π , ts) = lcp×→tcp ts top
  where
    lcp×→tcp : ∀ {A Π Γ Δ} → LCP⟨ Γ ⁏ Δ ⊢× Π ⟩ → A ∈ Π → TCP⟨ Γ ⁏ Δ ⊢ A ⟩
    lcp×→tcp (LCP.var i ts)  top     = TCP.var i
    lcp×→tcp (LCP.mp i j ts) top     = TCP.app (lcp×→tcp ts i) (lcp×→tcp ts j)
    lcp×→tcp (LCP.ci ts)     top     = TCP.ci
    lcp×→tcp (LCP.ck ts)     top     = TCP.ck
    lcp×→tcp (LCP.cs ts)     top     = TCP.cs
    lcp×→tcp (LCP.mvar i ts) top     = TCP.mvar i
    lcp×→tcp (LCP.nec ss ts) top     = TCP.box (lcp×→tcp ss top)
    lcp×→tcp (LCP.cdist ts)  top     = TCP.cdist
    lcp×→tcp (LCP.cup ts)    top     = TCP.cup
    lcp×→tcp (LCP.cdown ts)  top     = TCP.cdown
    lcp×→tcp (LCP.cpair ts)  top     = TCP.cpair
    lcp×→tcp (LCP.cfst ts)   top     = TCP.cfst
    lcp×→tcp (LCP.csnd ts)   top     = TCP.csnd
    lcp×→tcp (LCP.tt ts)     top     = TCP.tt
    lcp×→tcp (LCP.var i ts)  (pop k) = lcp×→tcp ts k
    lcp×→tcp (LCP.mp i j ts) (pop k) = lcp×→tcp ts k
    lcp×→tcp (LCP.ci ts)     (pop k) = lcp×→tcp ts k
    lcp×→tcp (LCP.ck ts)     (pop k) = lcp×→tcp ts k
    lcp×→tcp (LCP.cs ts)     (pop k) = lcp×→tcp ts k
    lcp×→tcp (LCP.mvar i ts) (pop k) = lcp×→tcp ts k
    lcp×→tcp (LCP.nec ss ts) (pop k) = lcp×→tcp ts k
    lcp×→tcp (LCP.cdist ts)  (pop k) = lcp×→tcp ts k
    lcp×→tcp (LCP.cup ts)    (pop k) = lcp×→tcp ts k
    lcp×→tcp (LCP.cdown ts)  (pop k) = lcp×→tcp ts k
    lcp×→tcp (LCP.cpair ts)  (pop k) = lcp×→tcp ts k
    lcp×→tcp (LCP.cfst ts)   (pop k) = lcp×→tcp ts k
    lcp×→tcp (LCP.csnd ts)   (pop k) = lcp×→tcp ts k
    lcp×→tcp (LCP.tt ts)     (pop k) = lcp×→tcp ts k


-- Translation from tree-shaped to list-shaped variant, with context pair.

tcp→lcp : ∀ {A Γ Δ} → TCP⟨ Γ ⁏ Δ ⊢ A ⟩ → LCP⟨ Γ ⁏ Δ ⊢ A ⟩
tcp→lcp (TCP.var i)   = ⌀ , LCP.var i LCP.nil
tcp→lcp (TCP.app t u) = LCP.app (tcp→lcp t) (tcp→lcp u)
tcp→lcp TCP.ci        = ⌀ , LCP.ci LCP.nil
tcp→lcp TCP.ck        = ⌀ , LCP.ck LCP.nil
tcp→lcp TCP.cs        = ⌀ , LCP.cs LCP.nil
tcp→lcp (TCP.mvar i)  = ⌀ , LCP.mvar i LCP.nil
tcp→lcp (TCP.box t)   = LCP.box (tcp→lcp t)
tcp→lcp TCP.cdist     = ⌀ , LCP.cdist LCP.nil
tcp→lcp TCP.cup       = ⌀ , LCP.cup LCP.nil
tcp→lcp TCP.cdown     = ⌀ , LCP.cdown LCP.nil
tcp→lcp TCP.cpair     = ⌀ , LCP.cpair LCP.nil
tcp→lcp TCP.cfst      = ⌀ , LCP.cfst LCP.nil
tcp→lcp TCP.csnd      = ⌀ , LCP.csnd LCP.nil
tcp→lcp TCP.tt        = ⌀ , LCP.tt LCP.nil


-- Deduction and detachment theorems for list-shaped variant, with context.

lc-lam : ∀ {A B Γ} → LC⟨ Γ , A ⊢ B ⟩ → LC⟨ Γ ⊢ A ▻ B ⟩
lc-lam = tc→lc ∘ TC.lam ∘ lc→tc

lc-lam⋆₀ : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → LC⟨ ⌀ ⊢ Γ ▻⋯▻ A ⟩
lc-lam⋆₀ = tc→lc ∘ TC.lam⋆₀ ∘ lc→tc

lc-det : ∀ {A B Γ} → LC⟨ Γ ⊢ A ▻ B ⟩ → LC⟨ Γ , A ⊢ B ⟩
lc-det = tc→lc ∘ TC.det ∘ lc→tc

lc-det⋆₀ : ∀ {A Γ} → LC⟨ ⌀ ⊢ Γ ▻⋯▻ A ⟩ → LC⟨ Γ ⊢ A ⟩
lc-det⋆₀ = tc→lc ∘ TC.det⋆₀ ∘ lc→tc


-- Deduction and detachment theorems for list-shaped variant, with context pair.

lcp-lam : ∀ {A B Γ Δ} → LCP⟨ Γ , A ⁏ Δ ⊢ B ⟩ → LCP⟨ Γ ⁏ Δ ⊢ A ▻ B ⟩
lcp-lam = tcp→lcp ∘ TCP.lam ∘ lcp→tcp

lcp-lam⋆₀ : ∀ {A Γ Δ} → LCP⟨ Γ ⁏ Δ ⊢ A ⟩ → LCP⟨ ⌀ ⁏ Δ ⊢ Γ ▻⋯▻ A ⟩
lcp-lam⋆₀ = tcp→lcp ∘ TCP.lam⋆₀ ∘ lcp→tcp

lcp-mlam : ∀ {A B Γ Δ} → LCP⟨ Γ ⁏ Δ , A ⊢ B ⟩ → LCP⟨ Γ ⁏ Δ ⊢ □ A ▻ B ⟩
lcp-mlam = tcp→lcp ∘ TCP.mlam ∘ lcp→tcp

lcp-mlam⋆₀ : ∀ {Δ A Γ} → LCP⟨ Γ ⁏ Δ ⊢ A ⟩ → LCP⟨ Γ ⁏ ⌀ ⊢ □⋆ Δ ▻⋯▻ A ⟩
lcp-mlam⋆₀ = tcp→lcp ∘ TCP.mlam⋆₀ ∘ lcp→tcp

lcp-det : ∀ {A B Γ Δ} → LCP⟨ Γ ⁏ Δ ⊢ A ▻ B ⟩ → LCP⟨ Γ , A ⁏ Δ ⊢ B ⟩
lcp-det = tcp→lcp ∘ TCP.det ∘ lcp→tcp

lcp-det⋆₀ : ∀ {A Γ Δ} → LCP⟨ ⌀ ⁏ Δ ⊢ Γ ▻⋯▻ A ⟩ → LCP⟨ Γ ⁏ Δ ⊢ A ⟩
lcp-det⋆₀ = tcp→lcp ∘ TCP.det⋆₀ ∘ lcp→tcp

lcp-mdet : ∀ {A B Γ Δ} → LCP⟨ Γ ⁏ Δ ⊢ □ A ▻ B ⟩ → LCP⟨ Γ ⁏ Δ , A ⊢ B ⟩
lcp-mdet = tcp→lcp ∘ TCP.mdet ∘ lcp→tcp

lcp-mdet⋆₀ : ∀ {Δ A Γ} → LCP⟨ Γ ⁏ ⌀ ⊢ □⋆ Δ ▻⋯▻ A ⟩ → LCP⟨ Γ ⁏ Δ ⊢ A ⟩
lcp-mdet⋆₀ = tcp→lcp ∘ TCP.mdet⋆₀ ∘ lcp→tcp


-- Context manipulation for list-shaped variant.

lcp-merge : ∀ {Δ A Γ} → LCP⟨ Γ ⁏ Δ ⊢ A ⟩ → LCP⟨ Γ ⧺ (□⋆ Δ) ⁏ ⌀ ⊢ A ⟩
lcp-merge {Δ} = tcp→lcp ∘ TCP.merge ∘ lcp→tcp

lcp-split : ∀ {Δ A Γ} → LCP⟨ Γ ⧺ (□⋆ Δ) ⁏ ⌀ ⊢ A ⟩ → LCP⟨ Γ ⁏ Δ ⊢ A ⟩
lcp-split {Δ} = tcp→lcp ∘ TCP.split ∘ lcp→tcp


-- Translation between list-shaped variants, with and without context.

l→lc₀ : ∀ {A} → L.⊢ A → LC⟨ ⌀ ⊢ A ⟩
l→lc₀ (Π , ts) = Π , l×→lc₀× ts
  where
    l×→lc₀× : ∀ {Π} → L.⊢× Π → LC⟨ ⌀ ⊢× Π ⟩
    l×→lc₀× L.nil         = LC.nil
    l×→lc₀× (L.mp i j ts) = LC.mp i j (l×→lc₀× ts)
    l×→lc₀× (L.ci ts)     = LC.ci (l×→lc₀× ts)
    l×→lc₀× (L.ck ts)     = LC.ck (l×→lc₀× ts)
    l×→lc₀× (L.cs ts)     = LC.cs (l×→lc₀× ts)
    l×→lc₀× (L.cpair ts)  = LC.cpair (l×→lc₀× ts)
    l×→lc₀× (L.cfst ts)   = LC.cfst (l×→lc₀× ts)
    l×→lc₀× (L.csnd ts)   = LC.csnd (l×→lc₀× ts)
    l×→lc₀× (L.tt ts)     = LC.tt (l×→lc₀× ts)
    l×→lc₀× (L.nec ss ts) = LC.nec (l×→lc₀× ss) (l×→lc₀× ts)
    l×→lc₀× (L.cdist ts)  = LC.cdist (l×→lc₀× ts)
    l×→lc₀× (L.cup ts)    = LC.cup (l×→lc₀× ts)
    l×→lc₀× (L.cdown ts)  = LC.cdown (l×→lc₀× ts)

l→lc : ∀ {A Γ} → L.⊢ Γ ▻⋯▻ A → LC⟨ Γ ⊢ A ⟩
l→lc t = lc-det⋆₀ (l→lc₀ t)

lc₀→l : ∀ {A} → LC⟨ ⌀ ⊢ A ⟩ → L.⊢ A
lc₀→l (Π , ts) = Π , lc₀×→lc× ts
  where
    lc₀×→lc× : ∀ {Π} → LC⟨ ⌀ ⊢× Π ⟩ → L.⊢× Π
    lc₀×→lc× LC.nil         = L.nil
    lc₀×→lc× (LC.var () ts)
    lc₀×→lc× (LC.mp i j ts) = L.mp i j (lc₀×→lc× ts)
    lc₀×→lc× (LC.ci ts)     = L.ci (lc₀×→lc× ts)
    lc₀×→lc× (LC.ck ts)     = L.ck (lc₀×→lc× ts)
    lc₀×→lc× (LC.cs ts)     = L.cs (lc₀×→lc× ts)
    lc₀×→lc× (LC.cpair ts)  = L.cpair (lc₀×→lc× ts)
    lc₀×→lc× (LC.cfst ts)   = L.cfst (lc₀×→lc× ts)
    lc₀×→lc× (LC.csnd ts)   = L.csnd (lc₀×→lc× ts)
    lc₀×→lc× (LC.tt ts)     = L.tt (lc₀×→lc× ts)
    lc₀×→lc× (LC.nec ss ts) = L.nec (lc₀×→lc× ss) (lc₀×→lc× ts)
    lc₀×→lc× (LC.cdist ts)  = L.cdist (lc₀×→lc× ts)
    lc₀×→lc× (LC.cup ts)    = L.cup (lc₀×→lc× ts)
    lc₀×→lc× (LC.cdown ts)  = L.cdown (lc₀×→lc× ts)

lc→l : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → L.⊢ Γ ▻⋯▻ A
lc→l t = lc₀→l (lc-lam⋆₀ t)


-- Translation between list-shaped variants, with context and with context pair.

lc→mlcp₀ : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → LCP⟨ Γ ⁏ ⌀ ⊢ A ⟩
lc→mlcp₀ (Π , ts) = Π , lc×→mlcp₀× ts
  where
    lc×→mlcp₀× : ∀ {Π Γ} → LC⟨ Γ ⊢× Π ⟩ → LCP⟨ Γ ⁏ ⌀ ⊢× Π ⟩
    lc×→mlcp₀× LC.nil         = LCP.nil
    lc×→mlcp₀× (LC.var i ts)  = LCP.var i (lc×→mlcp₀× ts)
    lc×→mlcp₀× (LC.mp i j ts) = LCP.mp i j (lc×→mlcp₀× ts)
    lc×→mlcp₀× (LC.ci ts)     = LCP.ci (lc×→mlcp₀× ts)
    lc×→mlcp₀× (LC.ck ts)     = LCP.ck (lc×→mlcp₀× ts)
    lc×→mlcp₀× (LC.cs ts)     = LCP.cs (lc×→mlcp₀× ts)
    lc×→mlcp₀× (LC.nec ss ts) = LCP.nec (lc×→mlcp₀× ss) (lc×→mlcp₀× ts)
    lc×→mlcp₀× (LC.cdist ts)  = LCP.cdist (lc×→mlcp₀× ts)
    lc×→mlcp₀× (LC.cup ts)    = LCP.cup (lc×→mlcp₀× ts)
    lc×→mlcp₀× (LC.cdown ts)  = LCP.cdown (lc×→mlcp₀× ts)
    lc×→mlcp₀× (LC.cpair ts)  = LCP.cpair (lc×→mlcp₀× ts)
    lc×→mlcp₀× (LC.cfst ts)   = LCP.cfst (lc×→mlcp₀× ts)
    lc×→mlcp₀× (LC.csnd ts)   = LCP.csnd (lc×→mlcp₀× ts)
    lc×→mlcp₀× (LC.tt ts)     = LCP.tt (lc×→mlcp₀× ts)

lc→lcp : ∀ {A Γ Δ} → LC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → LCP⟨ Γ ⁏ Δ ⊢ A ⟩
lc→lcp = lcp-split ∘ lc→mlcp₀

mlcp₀→lc : ∀ {A Γ} → LCP⟨ Γ ⁏ ⌀ ⊢ A ⟩ → LC⟨ Γ ⊢ A ⟩
mlcp₀→lc (Π , ts) = Π , mlcp₀×→lc× ts
  where
    mlcp₀×→lc× : ∀ {Π Γ} → LCP⟨ Γ ⁏ ⌀ ⊢× Π ⟩ → LC⟨ Γ ⊢× Π ⟩
    mlcp₀×→lc× LCP.nil          = LC.nil
    mlcp₀×→lc× (LCP.var i ts)   = LC.var i (mlcp₀×→lc× ts)
    mlcp₀×→lc× (LCP.mp i j ts)  = LC.mp i j (mlcp₀×→lc× ts)
    mlcp₀×→lc× (LCP.ci ts)      = LC.ci (mlcp₀×→lc× ts)
    mlcp₀×→lc× (LCP.ck ts)      = LC.ck (mlcp₀×→lc× ts)
    mlcp₀×→lc× (LCP.cs ts)      = LC.cs (mlcp₀×→lc× ts)
    mlcp₀×→lc× (LCP.mvar () ts)
    mlcp₀×→lc× (LCP.nec ss ts)  = LC.nec (mlcp₀×→lc× ss) (mlcp₀×→lc× ts)
    mlcp₀×→lc× (LCP.cdist ts)   = LC.cdist (mlcp₀×→lc× ts)
    mlcp₀×→lc× (LCP.cup ts)     = LC.cup (mlcp₀×→lc× ts)
    mlcp₀×→lc× (LCP.cdown ts)   = LC.cdown (mlcp₀×→lc× ts)
    mlcp₀×→lc× (LCP.cpair ts)   = LC.cpair (mlcp₀×→lc× ts)
    mlcp₀×→lc× (LCP.cfst ts)    = LC.cfst (mlcp₀×→lc× ts)
    mlcp₀×→lc× (LCP.csnd ts)    = LC.csnd (mlcp₀×→lc× ts)
    mlcp₀×→lc× (LCP.tt ts)      = LC.tt (mlcp₀×→lc× ts)

lcp→lc : ∀ {A Γ Δ} → LCP⟨ Γ ⁏ Δ ⊢ A ⟩ → LC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
lcp→lc = mlcp₀→lc ∘ lcp-merge


-- Translation between tree-shaped variants, with and without context.

t→tc₀ : ∀ {A} → T.⊢ A → TC⟨ ⌀ ⊢ A ⟩
t→tc₀ (T.app t u) = TC.app (t→tc₀ t) (t→tc₀ u)
t→tc₀ T.ci        = TC.ci
t→tc₀ T.ck        = TC.ck
t→tc₀ T.cs        = TC.cs
t→tc₀ T.cpair     = TC.cpair
t→tc₀ T.cfst      = TC.cfst
t→tc₀ T.csnd      = TC.csnd
t→tc₀ T.tt        = TC.tt
t→tc₀ (T.box t)   = TC.box (t→tc₀ t)
t→tc₀ T.cdist     = TC.cdist
t→tc₀ T.cup       = TC.cup
t→tc₀ T.cdown     = TC.cdown

t→tc : ∀ {A Γ} → T.⊢ Γ ▻⋯▻ A → TC⟨ Γ ⊢ A ⟩
t→tc t = TC.det⋆₀ (t→tc₀ t)

tc₀→t : ∀ {A} → TC⟨ ⌀ ⊢ A ⟩ → T.⊢ A
tc₀→t (TC.var ())
tc₀→t (TC.app t u) = T.app (tc₀→t t) (tc₀→t u)
tc₀→t TC.ci        = T.ci
tc₀→t TC.ck        = T.ck
tc₀→t TC.cs        = T.cs
tc₀→t TC.cpair     = T.cpair
tc₀→t TC.cfst      = T.cfst
tc₀→t TC.csnd      = T.csnd
tc₀→t TC.tt        = T.tt
tc₀→t (TC.box t)   = T.box (tc₀→t t)
tc₀→t TC.cdist     = T.cdist
tc₀→t TC.cup       = T.cup
tc₀→t TC.cdown     = T.cdown

tc→t : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → T.⊢ Γ ▻⋯▻ A
tc→t t = tc₀→t (TC.lam⋆₀ t)


-- Translation between tree-shaped variants, with context and with context pair.

tc→mtcp₀ : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → TCP⟨ Γ ⁏ ⌀ ⊢ A ⟩
tc→mtcp₀ (TC.var i)   = TCP.var i
tc→mtcp₀ (TC.app t u) = TCP.app (tc→mtcp₀ t) (tc→mtcp₀ u)
tc→mtcp₀ TC.ci        = TCP.ci
tc→mtcp₀ TC.ck        = TCP.ck
tc→mtcp₀ TC.cs        = TCP.cs
tc→mtcp₀ (TC.box t)   = TCP.box (tc→mtcp₀ t)
tc→mtcp₀ TC.cdist     = TCP.cdist
tc→mtcp₀ TC.cup       = TCP.cup
tc→mtcp₀ TC.cdown     = TCP.cdown
tc→mtcp₀ TC.cpair     = TCP.cpair
tc→mtcp₀ TC.cfst      = TCP.cfst
tc→mtcp₀ TC.csnd      = TCP.csnd
tc→mtcp₀ TC.tt        = TCP.tt

tc→tcp : ∀ {A Γ Δ} → TC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → TCP⟨ Γ ⁏ Δ ⊢ A ⟩
tc→tcp = TCP.split ∘ tc→mtcp₀

mtcp₀→tc : ∀ {A Γ} → TCP⟨ Γ ⁏ ⌀ ⊢ A ⟩ → TC⟨ Γ ⊢ A ⟩
mtcp₀→tc (TCP.var i)   = TC.var i
mtcp₀→tc (TCP.app t u) = TC.app (mtcp₀→tc t) (mtcp₀→tc u)
mtcp₀→tc TCP.ci        = TC.ci
mtcp₀→tc TCP.ck        = TC.ck
mtcp₀→tc TCP.cs        = TC.cs
mtcp₀→tc (TCP.mvar ())
mtcp₀→tc (TCP.box t)   = TC.box (mtcp₀→tc t)
mtcp₀→tc TCP.cdist     = TC.cdist
mtcp₀→tc TCP.cup       = TC.cup
mtcp₀→tc TCP.cdown     = TC.cdown
mtcp₀→tc TCP.cpair     = TC.cpair
mtcp₀→tc TCP.cfst      = TC.cfst
mtcp₀→tc TCP.csnd      = TC.csnd
mtcp₀→tc TCP.tt        = TC.tt

tcp→tc : ∀ {A Γ Δ} → TCP⟨ Γ ⁏ Δ ⊢ A ⟩ → TC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
tcp→tc = mtcp₀→tc ∘ TCP.merge


-- Additional useful translations, with and without context.

tc₀→l : ∀ {A} → TC⟨ ⌀ ⊢ A ⟩ → L.⊢ A
tc₀→l = t→l ∘ tc₀→t

tc→l : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → L.⊢ Γ ▻⋯▻ A
tc→l = t→l ∘ tc→t

lc₀→t : ∀ {A} → LC⟨ ⌀ ⊢ A ⟩ → T.⊢ A
lc₀→t = l→t ∘ lc₀→l

lc→t : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → T.⊢ Γ ▻⋯▻ A
lc→t = l→t ∘ lc→l

l→tc₀ : ∀ {A} → L.⊢ A → TC⟨ ⌀ ⊢ A ⟩
l→tc₀ = t→tc₀ ∘ l→t

l→tc : ∀ {A Γ} → L.⊢ Γ ▻⋯▻ A → TC⟨ Γ ⊢ A ⟩
l→tc = t→tc ∘ l→t

t→lc₀ : ∀ {A} → T.⊢ A → LC⟨ ⌀ ⊢ A ⟩
t→lc₀ = l→lc₀ ∘ t→l

t→lc : ∀ {A Γ} → T.⊢ Γ ▻⋯▻ A → LC⟨ Γ ⊢ A ⟩
t→lc = l→lc ∘ t→l


-- Additional useful translations, with context and context pair.

mtcp₀→lc : ∀ {A Γ} → TCP⟨ Γ ⁏ ⌀ ⊢ A ⟩ → LC⟨ Γ ⊢ A ⟩
mtcp₀→lc = tc→lc ∘ mtcp₀→tc

tcp→lc : ∀ {A Γ Δ} → TCP⟨ Γ ⁏ Δ ⊢ A ⟩ → LC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
tcp→lc = tc→lc ∘ tcp→tc

mlcp₀→tc : ∀ {A Γ} → LCP⟨ Γ ⁏ ⌀ ⊢ A ⟩ → TC⟨ Γ ⊢ A ⟩
mlcp₀→tc = lc→tc ∘ mlcp₀→lc

lcp→tc : ∀ {A Γ Δ} → LCP⟨ Γ ⁏ Δ ⊢ A ⟩ → TC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
lcp→tc = lc→tc ∘ lcp→lc

lc→mtcp₀ : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → TCP⟨ Γ ⁏ ⌀ ⊢ A ⟩
lc→mtcp₀ = tc→mtcp₀ ∘ lc→tc

lc→tcp : ∀ {A Γ Δ} → LC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → TCP⟨ Γ ⁏ Δ ⊢ A ⟩
lc→tcp = tc→tcp ∘ lc→tc

tc→mlcp₀ : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → LCP⟨ Γ ⁏ ⌀ ⊢ A ⟩
tc→mlcp₀ = lc→mlcp₀ ∘ tc→lc

tc→lcp : ∀ {A Γ Δ} → TC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → LCP⟨ Γ ⁏ Δ ⊢ A ⟩
tc→lcp = lc→lcp ∘ tc→lc


-- Translation from Hilbert-style to Gentzen-style, with context.

tc→gtc : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → GTC⟨ Γ ⊢ A ⟩
tc→gtc (TC.var i)   = GTC.var i
tc→gtc (TC.app t u) = GTC.app (tc→gtc t) (tc→gtc u)
tc→gtc TC.ci        = GTC.ci
tc→gtc TC.ck        = GTC.ck
tc→gtc TC.cs        = GTC.cs
tc→gtc (TC.box t)   = GTC.box (tc→gtc t)
tc→gtc TC.cdist     = GTC.cdist
tc→gtc TC.cup       = GTC.cup
tc→gtc TC.cdown     = GTC.cdown
tc→gtc TC.cpair     = GTC.cpair
tc→gtc TC.cfst      = GTC.cfst
tc→gtc TC.csnd      = GTC.csnd
tc→gtc TC.tt        = GTC.tt

lc→gtc : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → GTC⟨ Γ ⊢ A ⟩
lc→gtc = tc→gtc ∘ lc→tc

t→gtc₀ : ∀ {A} → T.⊢ A → GTC⟨ ⌀ ⊢ A ⟩
t→gtc₀ = tc→gtc ∘ t→tc₀

t→gtc : ∀ {A Γ} → T.⊢ Γ ▻⋯▻ A → GTC⟨ Γ ⊢ A ⟩
t→gtc = tc→gtc ∘ t→tc

l→gtc₀ : ∀ {A} → L.⊢ A → GTC⟨ ⌀ ⊢ A ⟩
l→gtc₀ = tc→gtc ∘ l→tc₀

l→gtc : ∀ {A Γ} → L.⊢ Γ ▻⋯▻ A → GTC⟨ Γ ⊢ A ⟩
l→gtc = tc→gtc ∘ l→tc


-- Translation from Gentzen-style to Hilbert-style, with context.

mutual
  gtc→tc : ∀ {A Γ} → GTC⟨ Γ ⊢ A ⟩ → TC⟨ Γ ⊢ A ⟩
  gtc→tc (GTC.var i)         = TC.var i
  gtc→tc (GTC.lam t)         = TC.lam (gtc→tc t)
  gtc→tc (GTC.app t u)       = TC.app (gtc→tc t) (gtc→tc u)
  gtc→tc (GTC.multibox ts u) = TC.multibox (gtc→tc⋆ ts) (gtc→tc u)
  gtc→tc (GTC.down t)        = TC.down (gtc→tc t)
  gtc→tc (GTC.pair t u)      = TC.pair (gtc→tc t) (gtc→tc u)
  gtc→tc (GTC.fst t)         = TC.fst (gtc→tc t)
  gtc→tc (GTC.snd t)         = TC.snd (gtc→tc t)
  gtc→tc GTC.tt              = TC.tt

  gtc→tc⋆ : ∀ {Π Γ} → GTC⟨ Γ ⊢⋆ Π ⟩ → TC⟨ Γ ⊢⋆ Π ⟩
  gtc→tc⋆ {⌀}     ∙        = ∙
  gtc→tc⋆ {Π , A} (ts , t) = gtc→tc⋆ ts , gtc→tc t

gtc→lc : ∀ {A Γ} → GTC⟨ Γ ⊢ A ⟩ → LC⟨ Γ ⊢ A ⟩
gtc→lc = tc→lc ∘ gtc→tc

gtc₀→t : ∀ {A} → GTC⟨ ⌀ ⊢ A ⟩ → T.⊢ A
gtc₀→t = tc₀→t ∘ gtc→tc

gtc→t : ∀ {A Γ} → GTC⟨ Γ ⊢ A ⟩ → T.⊢ Γ ▻⋯▻ A
gtc→t = tc→t ∘ gtc→tc

gtc₀→l : ∀ {A} → GTC⟨ ⌀ ⊢ A ⟩ → L.⊢ A
gtc₀→l = tc₀→l ∘ gtc→tc

gtc→l : ∀ {A Γ} → GTC⟨ Γ ⊢ A ⟩ → L.⊢ Γ ▻⋯▻ A
gtc→l = tc→l ∘ gtc→tc


-- Translation from Hilbert-style to Gentzen-style, with context pair.

tcp→gtcp : ∀ {A Γ Δ} → TCP⟨ Γ ⁏ Δ ⊢ A ⟩ → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩
tcp→gtcp (TCP.var i)   = GTCP.var i
tcp→gtcp (TCP.app t u) = GTCP.app (tcp→gtcp t) (tcp→gtcp u)
tcp→gtcp TCP.ci        = GTCP.ci
tcp→gtcp TCP.ck        = GTCP.ck
tcp→gtcp TCP.cs        = GTCP.cs
tcp→gtcp (TCP.mvar i)  = GTCP.mvar i
tcp→gtcp (TCP.box t)   = GTCP.box (tcp→gtcp t)
tcp→gtcp TCP.cdist     = GTCP.cdist
tcp→gtcp TCP.cup       = GTCP.cup
tcp→gtcp TCP.cdown     = GTCP.cdown
tcp→gtcp TCP.cpair     = GTCP.cpair
tcp→gtcp TCP.cfst      = GTCP.cfst
tcp→gtcp TCP.csnd      = GTCP.csnd
tcp→gtcp TCP.tt        = GTCP.tt

lcp→gtcp : ∀ {A Γ Δ} → LCP⟨ Γ ⁏ Δ ⊢ A ⟩ → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩
lcp→gtcp = tcp→gtcp ∘ lcp→tcp

tc→mgtcp₀ : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → GTCP⟨ Γ ⁏ ⌀ ⊢ A ⟩
tc→mgtcp₀ = tcp→gtcp ∘ tc→mtcp₀

tc→gtcp : ∀ {A Γ Δ} → TC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩
tc→gtcp = tcp→gtcp ∘ tc→tcp

lc→mgtcp₀ : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → GTCP⟨ Γ ⁏ ⌀ ⊢ A ⟩
lc→mgtcp₀ = tcp→gtcp ∘ lc→mtcp₀

lc→gtcp : ∀ {A Γ Δ} → LC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩
lc→gtcp = tcp→gtcp ∘ lc→tcp


-- Translation from Gentzen-style to Hilbert-style, with context pair.

gtcp→tcp : ∀ {A Γ Δ} → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩ → TCP⟨ Γ ⁏ Δ ⊢ A ⟩
gtcp→tcp (GTCP.var i)     = TCP.var i
gtcp→tcp (GTCP.lam t)     = TCP.lam (gtcp→tcp t)
gtcp→tcp (GTCP.app t u)   = TCP.app (gtcp→tcp t) (gtcp→tcp u)
gtcp→tcp (GTCP.mvar i)    = TCP.mvar i
gtcp→tcp (GTCP.box t)     = TCP.box (gtcp→tcp t)
gtcp→tcp (GTCP.unbox t u) = TCP.unbox (gtcp→tcp t) (gtcp→tcp u)
gtcp→tcp (GTCP.pair t u)  = TCP.pair (gtcp→tcp t) (gtcp→tcp u)
gtcp→tcp (GTCP.fst t)     = TCP.fst (gtcp→tcp t)
gtcp→tcp (GTCP.snd t)     = TCP.snd (gtcp→tcp t)
gtcp→tcp GTCP.tt          = TCP.tt

gtcp→lcp : ∀ {A Γ Δ} → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩ → LCP⟨ Γ ⁏ Δ ⊢ A ⟩
gtcp→lcp = tcp→lcp ∘ gtcp→tcp

mgtcp₀→tc : ∀ {A Γ} → GTCP⟨ Γ ⁏ ⌀ ⊢ A ⟩ → TC⟨ Γ ⊢ A ⟩
mgtcp₀→tc = mtcp₀→tc ∘ gtcp→tcp

gtcp→tc : ∀ {A Γ Δ} → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩ → TC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
gtcp→tc = tcp→tc ∘ gtcp→tcp

mgtcp₀→lc : ∀ {A Γ} → GTCP⟨ Γ ⁏ ⌀ ⊢ A ⟩ → LC⟨ Γ ⊢ A ⟩
mgtcp₀→lc = mtcp₀→lc ∘ gtcp→tcp

gtcp→lc : ∀ {A Γ Δ} → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩ → LC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
gtcp→lc = tcp→lc ∘ gtcp→tcp


-- Translation between tree-shaped variants, with context and with context pair.

mutual
  gtc→mgtcp₀ : ∀ {A Γ} → GTC⟨ Γ ⊢ A ⟩ → GTCP⟨ Γ ⁏ ⌀ ⊢ A ⟩
  gtc→mgtcp₀ (GTC.var i)         = GTCP.var i
  gtc→mgtcp₀ (GTC.lam t)         = GTCP.lam (gtc→mgtcp₀ t)
  gtc→mgtcp₀ (GTC.app t u)       = GTCP.app (gtc→mgtcp₀ t) (gtc→mgtcp₀ u)
  gtc→mgtcp₀ (GTC.multibox ts u) = GTCP.multibox (gtc→mgtcp₀⋆ ts) (gtc→mgtcp₀ u)
  gtc→mgtcp₀ (GTC.down t)        = GTCP.down (gtc→mgtcp₀ t)
  gtc→mgtcp₀ (GTC.pair t u)      = GTCP.pair (gtc→mgtcp₀ t) (gtc→mgtcp₀ u)
  gtc→mgtcp₀ (GTC.fst t)         = GTCP.fst (gtc→mgtcp₀ t)
  gtc→mgtcp₀ (GTC.snd t)         = GTCP.snd (gtc→mgtcp₀ t)
  gtc→mgtcp₀ GTC.tt              = GTCP.tt

  gtc→mgtcp₀⋆ : ∀ {Π Γ} → GTC⟨ Γ ⊢⋆ Π ⟩ → GTCP⟨ Γ ⁏ ⌀ ⊢⋆ Π ⟩
  gtc→mgtcp₀⋆ {⌀}     ∙        = ∙
  gtc→mgtcp₀⋆ {Π , A} (ts , t) = gtc→mgtcp₀⋆ ts , gtc→mgtcp₀ t

gtc→gtcp : ∀ {A Γ Δ} → GTC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩
gtc→gtcp = GTCP.split ∘ gtc→mgtcp₀

-- NOTE: Direct translation fails the termination check.
mgtcp₀→gtc : ∀ {A Γ} → GTCP⟨ Γ ⁏ ⌀ ⊢ A ⟩ → GTC⟨ Γ ⊢ A ⟩
mgtcp₀→gtc = tc→gtc ∘ mgtcp₀→tc

gtcp→gtc : ∀ {A Γ Δ} → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩ → GTC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
gtcp→gtc = mgtcp₀→gtc ∘ GTCP.merge
