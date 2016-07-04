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
    aux (HL.nec (Π ∙ ss) ts) top     = HN.nec (aux ss top)
    aux (HL.dist ts)         top     = HN.dist
    aux (HL.up ts)           top     = HN.up
    aux (HL.down ts)         top     = HN.down
    aux (HL.pair ts)         top     = HN.pair
    aux (HL.fst ts)          top     = HN.fst
    aux (HL.snd ts)          top     = HN.snd
    aux (HL.inl ts)          top     = HN.inl
    aux (HL.inr ts)          top     = HN.inr
    aux (HL.case ts)         top     = HN.case
    aux (HL.boom ts)         top     = HN.boom
    aux (HL.var i ts)        (pop k) = aux ts k
    aux (HL.mp i j ts)       (pop k) = aux ts k
    aux (HL.ci ts)           (pop k) = aux ts k
    aux (HL.ck ts)           (pop k) = aux ts k
    aux (HL.cs ts)           (pop k) = aux ts k
    aux (HL.mvar i ts)       (pop k) = aux ts k
    aux (HL.nec ss ts)       (pop k) = aux ts k
    aux (HL.dist ts)         (pop k) = aux ts k
    aux (HL.up ts)           (pop k) = aux ts k
    aux (HL.down ts)         (pop k) = aux ts k
    aux (HL.pair ts)         (pop k) = aux ts k
    aux (HL.fst ts)          (pop k) = aux ts k
    aux (HL.snd ts)          (pop k) = aux ts k
    aux (HL.inl ts)          (pop k) = aux ts k
    aux (HL.inr ts)          (pop k) = aux ts k
    aux (HL.case ts)         (pop k) = aux ts k
    aux (HL.boom ts)         (pop k) = aux ts k


-- Conversion from nested Hilbert-style proofs to linear.

hn→hl : ∀ {A Γ Δ} → HN⟨ Γ ⨾ Δ ⊢ A ⟩ → HL⟨ Γ ⨾ Δ ⊢ A ⟩
hn→hl (HN.var i)   = [] ∙ HL.var i HL.nil
hn→hl (HN.app t u) = HL.app (hn→hl t) (hn→hl u)
hn→hl HN.ci        = [] ∙ HL.ci HL.nil
hn→hl HN.ck        = [] ∙ HL.ck HL.nil
hn→hl HN.cs        = [] ∙ HL.cs HL.nil
hn→hl (HN.mvar i)  = [] ∙ HL.mvar i HL.nil
hn→hl (HN.nec t)   = [] ∙ HL.nec (hn→hl t) HL.nil
hn→hl HN.dist      = [] ∙ HL.dist HL.nil
hn→hl HN.up        = [] ∙ HL.up HL.nil
hn→hl HN.down      = [] ∙ HL.down HL.nil
hn→hl HN.pair      = [] ∙ HL.pair HL.nil
hn→hl HN.fst       = [] ∙ HL.fst HL.nil
hn→hl HN.snd       = [] ∙ HL.snd HL.nil
hn→hl HN.inl       = [] ∙ HL.inl HL.nil
hn→hl HN.inr       = [] ∙ HL.inr HL.nil
hn→hl HN.case      = [] ∙ HL.case HL.nil
hn→hl HN.boom      = [] ∙ HL.boom HL.nil


-- Deduction theorems for linear Hilbert-style proofs.

hl-ded : ∀ {A B Γ Δ} → HL⟨ Γ , A ⨾ Δ ⊢ B ⟩ → HL⟨ Γ ⨾ Δ ⊢ A ⇒ B ⟩
hl-ded = hn→hl ∘ HN.ded ∘ hl→hn

hl-mded : ∀ {A B Γ Δ} → HL⟨ Γ ⨾ Δ , A ⊢ B ⟩ → HL⟨ Γ ⨾ Δ ⊢ □ A ⇒ B ⟩
hl-mded = hn→hl ∘ HN.mded ∘ hl→hn


-- Conversion from Hilbert-style proofs to Gentzen-style.

hn→g : ∀ {A Γ Δ} → HN⟨ Γ ⨾ Δ ⊢ A ⟩ → G⟨ Γ ⨾ Δ ⊢ A ⟩
hn→g (HN.var i)   = G.var i
hn→g (HN.app t u) = G.app (hn→g t) (hn→g u)
hn→g HN.ci        = G.ci
hn→g HN.ck        = G.ck
hn→g HN.cs        = G.cs
hn→g (HN.mvar i)  = G.mvar i
hn→g (HN.nec t)   = G.box (hn→g t)
hn→g HN.dist      = G.cdist
hn→g HN.up        = G.cup
hn→g HN.down      = G.cdown
hn→g HN.pair      = G.cpair
hn→g HN.fst       = G.cfst
hn→g HN.snd       = G.csnd
hn→g HN.inl       = G.cinl
hn→g HN.inr       = G.cinr
hn→g HN.case      = G.ccase
hn→g HN.boom      = G.cboom

hl→g : ∀ {A Γ Δ} → HL⟨ Γ ⨾ Δ ⊢ A ⟩ → G⟨ Γ ⨾ Δ ⊢ A ⟩
hl→g = hn→g ∘ hl→hn


-- Conversion from Gentzen-style proofs to Hilbert-style.

g→hn : ∀ {A Γ Δ} → G⟨ Γ ⨾ Δ ⊢ A ⟩ → HN⟨ Γ ⨾ Δ ⊢ A ⟩
g→hn (G.var i)      = HN.var i
g→hn (G.lam t)      = HN.ded (g→hn t)
g→hn (G.app t u)    = HN.app (g→hn t) (g→hn u)
g→hn (G.mvar i)     = HN.mvar i
g→hn (G.box t)      = HN.nec (g→hn t)
g→hn (G.unbox t u)  = HN.funbox (g→hn t) (g→hn u)
g→hn (G.pair t u)   = HN.fpair (g→hn t) (g→hn u)
g→hn (G.fst t)      = HN.ffst (g→hn t)
g→hn (G.snd t)      = HN.fsnd (g→hn t)
g→hn (G.inl t)      = HN.finl (g→hn t)
g→hn (G.inr t)      = HN.finr (g→hn t)
g→hn (G.case t u v) = HN.fcase (g→hn t) (g→hn u) (g→hn v)
g→hn (G.boom t)     = HN.fboom (g→hn t)

g→hl : ∀ {A Γ Δ} → G⟨ Γ ⨾ Δ ⊢ A ⟩ → HL⟨ Γ ⨾ Δ ⊢ A ⟩
g→hl = hn→hl ∘ g→hn
