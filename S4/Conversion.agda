module S4.Conversion where

open import S4.Core public

import S4.Hilbert.Linear as HL
import S4.Hilbert.Nested as HN
import S4.Gentzen.PfenningDavies as G

open HL using () renaming (_⨾_⊢⁺_ to HL⟨_⨾_⊢⁺_⟩ ; _⨾_⊢_ to HL⟨_⨾_⊢_⟩) public
open HN using () renaming (_⨾_⊢_ to HN⟨_⨾_⊢_⟩) public
open G using () renaming (_⨾_⊢_ to G⟨_⨾_⊢_⟩) public


-- Conversion from linear Hilbert-style proofs to nested.

hl→hn : ∀ {A Γ Δ} → HL⟨ Γ ⨾ Δ ⊢ A ⟩ → HN⟨ Γ ⨾ Δ ⊢ A ⟩
hl→hn (Π ∙ ts) = aux ts top
  where
    aux : ∀ {A Γ Δ Π} → HL⟨ Γ ⨾ Δ ⊢⁺ Π ⟩ → Π ∋ A → HN⟨ Γ ⨾ Δ ⊢ A ⟩
    aux (HL.var i ts)        top     = HN.var i
    aux (HL.mp i j ts)       top     = HN.app (aux ts i) (aux ts j)
    aux (HL.ci ts)           top     = HN.ci
    aux (HL.ck ts)           top     = HN.ck
    aux (HL.cs ts)           top     = HN.cs
    aux (HL.mvar i ts)       top     = HN.mvar i
    aux (HL.nec (Π ∙ ss) ts) top     = HN.box (aux ss top)
    aux (HL.cdist ts)        top     = HN.cdist
    aux (HL.cup ts)          top     = HN.cup
    aux (HL.cdown ts)        top     = HN.cdown
    aux (HL.cpair ts)        top     = HN.cpair
    aux (HL.cfst ts)         top     = HN.cfst
    aux (HL.csnd ts)         top     = HN.csnd
    aux (HL.cinl ts)         top     = HN.cinl
    aux (HL.cinr ts)         top     = HN.cinr
    aux (HL.ccase ts)        top     = HN.ccase
    aux (HL.cboom ts)        top     = HN.cboom
    aux (HL.var i ts)        (pop k) = aux ts k
    aux (HL.mp i j ts)       (pop k) = aux ts k
    aux (HL.ci ts)           (pop k) = aux ts k
    aux (HL.ck ts)           (pop k) = aux ts k
    aux (HL.cs ts)           (pop k) = aux ts k
    aux (HL.mvar i ts)       (pop k) = aux ts k
    aux (HL.nec ss ts)       (pop k) = aux ts k
    aux (HL.cdist ts)        (pop k) = aux ts k
    aux (HL.cup ts)          (pop k) = aux ts k
    aux (HL.cdown ts)        (pop k) = aux ts k
    aux (HL.cpair ts)        (pop k) = aux ts k
    aux (HL.cfst ts)         (pop k) = aux ts k
    aux (HL.csnd ts)         (pop k) = aux ts k
    aux (HL.cinl ts)         (pop k) = aux ts k
    aux (HL.cinr ts)         (pop k) = aux ts k
    aux (HL.ccase ts)        (pop k) = aux ts k
    aux (HL.cboom ts)        (pop k) = aux ts k


-- Conversion from nested Hilbert-style proofs to linear.

hn→hl : ∀ {A Γ Δ} → HN⟨ Γ ⨾ Δ ⊢ A ⟩ → HL⟨ Γ ⨾ Δ ⊢ A ⟩
hn→hl (HN.var i)   = [] ∙ HL.var i HL.nil
hn→hl (HN.app t u) = HL.app (hn→hl t) (hn→hl u)
hn→hl HN.ci        = [] ∙ HL.ci HL.nil
hn→hl HN.ck        = [] ∙ HL.ck HL.nil
hn→hl HN.cs        = [] ∙ HL.cs HL.nil
hn→hl (HN.mvar i)  = [] ∙ HL.mvar i HL.nil
hn→hl (HN.box t)   = HL.box (hn→hl t)
hn→hl HN.cdist     = [] ∙ HL.cdist HL.nil
hn→hl HN.cup       = [] ∙ HL.cup HL.nil
hn→hl HN.cdown     = [] ∙ HL.cdown HL.nil
hn→hl HN.cpair     = [] ∙ HL.cpair HL.nil
hn→hl HN.cfst      = [] ∙ HL.cfst HL.nil
hn→hl HN.csnd      = [] ∙ HL.csnd HL.nil
hn→hl HN.cinl      = [] ∙ HL.cinl HL.nil
hn→hl HN.cinr      = [] ∙ HL.cinr HL.nil
hn→hl HN.ccase     = [] ∙ HL.ccase HL.nil
hn→hl HN.cboom     = [] ∙ HL.cboom HL.nil


-- Deduction theorems for linear Hilbert-style proofs.

hl-lam : ∀ {A B Γ Δ} → HL⟨ Γ , A ⨾ Δ ⊢ B ⟩ → HL⟨ Γ ⨾ Δ ⊢ A ⇒ B ⟩
hl-lam = hn→hl ∘ HN.lam ∘ hl→hn

hl-mlam : ∀ {A B Γ Δ} → HL⟨ Γ ⨾ Δ , A ⊢ B ⟩ → HL⟨ Γ ⨾ Δ ⊢ □ A ⇒ B ⟩
hl-mlam = hn→hl ∘ HN.mlam ∘ hl→hn


-- Conversion from Hilbert-style proofs to Gentzen-style.

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
hn→g HN.cpair     = G.cpair
hn→g HN.cfst      = G.cfst
hn→g HN.csnd      = G.csnd
hn→g HN.cinl      = G.cinl
hn→g HN.cinr      = G.cinr
hn→g HN.ccase     = G.ccase
hn→g HN.cboom     = G.cboom

hl→g : ∀ {A Γ Δ} → HL⟨ Γ ⨾ Δ ⊢ A ⟩ → G⟨ Γ ⨾ Δ ⊢ A ⟩
hl→g = hn→g ∘ hl→hn


-- Conversion from Gentzen-style proofs to Hilbert-style.

g→hn : ∀ {A Γ Δ} → G⟨ Γ ⨾ Δ ⊢ A ⟩ → HN⟨ Γ ⨾ Δ ⊢ A ⟩
g→hn (G.var i)      = HN.var i
g→hn (G.lam t)      = HN.lam (g→hn t)
g→hn (G.app t u)    = HN.app (g→hn t) (g→hn u)
g→hn (G.mvar i)     = HN.mvar i
g→hn (G.box t)      = HN.box (g→hn t)
g→hn (G.unbox t u)  = HN.unbox (g→hn t) (g→hn u)
g→hn (G.pair t u)   = HN.pair (g→hn t) (g→hn u)
g→hn (G.fst t)      = HN.fst (g→hn t)
g→hn (G.snd t)      = HN.snd (g→hn t)
g→hn (G.inl t)      = HN.inl (g→hn t)
g→hn (G.inr t)      = HN.inr (g→hn t)
g→hn (G.case t u v) = HN.case (g→hn t) (g→hn u) (g→hn v)
g→hn (G.boom t)     = HN.boom (g→hn t)

g→hl : ∀ {A Γ Δ} → G⟨ Γ ⨾ Δ ⊢ A ⟩ → HL⟨ Γ ⨾ Δ ⊢ A ⟩
g→hl = hn→hl ∘ g→hn
