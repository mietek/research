module BasicIS4.Dual.Translation where

open import BasicIS4.Core public

import BasicIS4.Dual.Hilbert.Sequential as HS
import BasicIS4.Dual.Hilbert.Nested as HN
import BasicIS4.Dual.Gentzen.Core as G

open HS using () renaming (_⨾_⊢⋆_ to HS⟨_⨾_⊢⋆_⟩ ; _⨾_⊢_ to HS⟨_⨾_⊢_⟩) public
open HN using () renaming (_⨾_⊢_ to HN⟨_⨾_⊢_⟩) public
open G using () renaming (_⨾_⊢_ to G⟨_⨾_⊢_⟩) public


-- Translation from sequential Hilbert-style to nested.

hl→hn : ∀ {A Γ Δ} → HS⟨ Γ ⨾ Δ ⊢ A ⟩ → HN⟨ Γ ⨾ Δ ⊢ A ⟩
hl→hn (Π ∙ ts) = aux ts top
  where
    aux : ∀ {A Γ Δ Π} → HS⟨ Γ ⨾ Δ ⊢⋆ Π ⟩ → A ∈ Π → HN⟨ Γ ⨾ Δ ⊢ A ⟩
    aux (HS.var i ts)        top     = HN.var i
    aux (HS.mp i j ts)       top     = HN.app (aux ts i) (aux ts j)
    aux (HS.ci ts)           top     = HN.ci
    aux (HS.ck ts)           top     = HN.ck
    aux (HS.cs ts)           top     = HN.cs
    aux (HS.mvar i ts)       top     = HN.mvar i
    aux (HS.nec (Π ∙ ss) ts) top     = HN.box (aux ss top)
    aux (HS.cdist ts)        top     = HN.cdist
    aux (HS.cup ts)          top     = HN.cup
    aux (HS.cdown ts)        top     = HN.cdown
    aux (HS.unit ts)         top     = HN.unit
    aux (HS.cpair ts)        top     = HN.cpair
    aux (HS.cfst ts)         top     = HN.cfst
    aux (HS.csnd ts)         top     = HN.csnd
    aux (HS.var i ts)        (pop k) = aux ts k
    aux (HS.mp i j ts)       (pop k) = aux ts k
    aux (HS.ci ts)           (pop k) = aux ts k
    aux (HS.ck ts)           (pop k) = aux ts k
    aux (HS.cs ts)           (pop k) = aux ts k
    aux (HS.mvar i ts)       (pop k) = aux ts k
    aux (HS.nec ss ts)       (pop k) = aux ts k
    aux (HS.cdist ts)        (pop k) = aux ts k
    aux (HS.cup ts)          (pop k) = aux ts k
    aux (HS.cdown ts)        (pop k) = aux ts k
    aux (HS.unit ts)         (pop k) = aux ts k
    aux (HS.cpair ts)        (pop k) = aux ts k
    aux (HS.cfst ts)         (pop k) = aux ts k
    aux (HS.csnd ts)         (pop k) = aux ts k


-- Translation from nested Hilbert-style to sequential.

hn→hl : ∀ {A Γ Δ} → HN⟨ Γ ⨾ Δ ⊢ A ⟩ → HS⟨ Γ ⨾ Δ ⊢ A ⟩
hn→hl (HN.var i)   = ⌀ ∙ HS.var i HS.nil
hn→hl (HN.app t u) = HS.app (hn→hl t) (hn→hl u)
hn→hl HN.ci        = ⌀ ∙ HS.ci HS.nil
hn→hl HN.ck        = ⌀ ∙ HS.ck HS.nil
hn→hl HN.cs        = ⌀ ∙ HS.cs HS.nil
hn→hl (HN.mvar i)  = ⌀ ∙ HS.mvar i HS.nil
hn→hl (HN.box t)   = HS.box (hn→hl t)
hn→hl HN.cdist     = ⌀ ∙ HS.cdist HS.nil
hn→hl HN.cup       = ⌀ ∙ HS.cup HS.nil
hn→hl HN.cdown     = ⌀ ∙ HS.cdown HS.nil
hn→hl HN.unit      = ⌀ ∙ HS.unit HS.nil
hn→hl HN.cpair     = ⌀ ∙ HS.cpair HS.nil
hn→hl HN.cfst      = ⌀ ∙ HS.cfst HS.nil
hn→hl HN.csnd      = ⌀ ∙ HS.csnd HS.nil


-- Deduction theorems for sequential Hilbert-style.

hl-lam : ∀ {A B Γ Δ} → HS⟨ Γ , A ⨾ Δ ⊢ B ⟩ → HS⟨ Γ ⨾ Δ ⊢ A ▷ B ⟩
hl-lam = hn→hl ∘ HN.lam ∘ hl→hn

hl-mlam : ∀ {A B Γ Δ} → HS⟨ Γ ⨾ Δ , A ⊢ B ⟩ → HS⟨ Γ ⨾ Δ ⊢ □ A ▷ B ⟩
hl-mlam = hn→hl ∘ HN.mlam ∘ hl→hn


-- Translation from Hilbert-style to Gentzen-style.

hn→g : ∀ {A Γ Δ} → HN⟨ Γ ⨾ Δ ⊢ A ⟩ → G⟨ Γ ⨾ Δ ⊢ A ⟩
hn→g (HN.var i)   = G.var i
hn→g (HN.app t u) = G.app (hn→g t) (hn→g u)
hn→g HN.ci        = G.ci
hn→g HN.ck        = G.ck
hn→g HN.cs        = G.cs
hn→g (HN.mvar i)  = G.mvar i
hn→g (HN.box t)   = G.box (hn→g t)
hn→g HN.cdist     = G.cdist
hn→g HN.cup       = G.cup
hn→g HN.cdown     = G.cdown
hn→g HN.unit      = G.unit
hn→g HN.cpair     = G.cpair
hn→g HN.cfst      = G.cfst
hn→g HN.csnd      = G.csnd

hl→g : ∀ {A Γ Δ} → HS⟨ Γ ⨾ Δ ⊢ A ⟩ → G⟨ Γ ⨾ Δ ⊢ A ⟩
hl→g = hn→g ∘ hl→hn


-- Translation from Gentzen-style to Hilbert-style.

g→hn : ∀ {A Γ Δ} → G⟨ Γ ⨾ Δ ⊢ A ⟩ → HN⟨ Γ ⨾ Δ ⊢ A ⟩
g→hn (G.var i)     = HN.var i
g→hn (G.lam t)     = HN.lam (g→hn t)
g→hn (G.app t u)   = HN.app (g→hn t) (g→hn u)
g→hn (G.mvar i)    = HN.mvar i
g→hn (G.box t)     = HN.box (g→hn t)
g→hn (G.unbox t u) = HN.unbox (g→hn t) (g→hn u)
g→hn G.unit        = HN.unit
g→hn (G.pair t u)  = HN.pair (g→hn t) (g→hn u)
g→hn (G.fst t)     = HN.fst (g→hn t)
g→hn (G.snd t)     = HN.snd (g→hn t)

g→hl : ∀ {A Γ Δ} → G⟨ Γ ⨾ Δ ⊢ A ⟩ → HS⟨ Γ ⨾ Δ ⊢ A ⟩
g→hl = hn→hl ∘ g→hn
