module IPC.Conversion where

open import IPC.Core public

import IPC.Hilbert.Linear as HL
import IPC.Hilbert.Nested as HN
import IPC.Gentzen as G

open HL using () renaming (_⊢⁺_ to HL_⊢⁺_ ; _⊢_ to HL_⊢_) public
open HN using () renaming (_⊢_ to HN_⊢_) public
open G using () renaming (_⊢_ to G_⊢_) public


-- Conversion from linear Hilbert-style proofs to nested.

hl→hn : ∀ {A Γ} → HL Γ ⊢ A → HN Γ ⊢ A
hl→hn (Π ∙ ts) = aux ts top
  where
    aux : ∀ {A Γ Π} → HL Γ ⊢⁺ Π → Π ∋ A → HN Γ ⊢ A
    aux (HL.var i ts)  top     = HN.var i
    aux (HL.mp i j ts) top     = HN.app (aux ts i) (aux ts j)
    aux (HL.ci ts)     top     = HN.ci
    aux (HL.ck ts)     top     = HN.ck
    aux (HL.cs ts)     top     = HN.cs
    aux (HL.pair ts)   top     = HN.pair
    aux (HL.fst ts)    top     = HN.fst
    aux (HL.snd ts)    top     = HN.snd
    aux (HL.inl ts)    top     = HN.inl
    aux (HL.inr ts)    top     = HN.inr
    aux (HL.case ts)   top     = HN.case
    aux (HL.boom ts)   top     = HN.boom
    aux (HL.var i ts)  (pop k) = aux ts k
    aux (HL.mp i j ts) (pop k) = aux ts k
    aux (HL.ci ts)     (pop k) = aux ts k
    aux (HL.ck ts)     (pop k) = aux ts k
    aux (HL.cs ts)     (pop k) = aux ts k
    aux (HL.pair ts)   (pop k) = aux ts k
    aux (HL.fst ts)    (pop k) = aux ts k
    aux (HL.snd ts)    (pop k) = aux ts k
    aux (HL.inl ts)    (pop k) = aux ts k
    aux (HL.inr ts)    (pop k) = aux ts k
    aux (HL.case ts)   (pop k) = aux ts k
    aux (HL.boom ts)   (pop k) = aux ts k


-- Conversion from nested Hilbert-style proofs to linear.

hn→hl : ∀ {A Γ} → HN Γ ⊢ A → HL Γ ⊢ A
hn→hl (HN.var i)   = [] ∙ HL.var i HL.nil
hn→hl (HN.app t u) = HL.app (hn→hl t) (hn→hl u)
hn→hl HN.ci        = [] ∙ HL.ci HL.nil
hn→hl HN.ck        = [] ∙ HL.ck HL.nil
hn→hl HN.cs        = [] ∙ HL.cs HL.nil
hn→hl HN.pair      = [] ∙ HL.pair HL.nil
hn→hl HN.fst       = [] ∙ HL.fst HL.nil
hn→hl HN.snd       = [] ∙ HL.snd HL.nil
hn→hl HN.inl       = [] ∙ HL.inl HL.nil
hn→hl HN.inr       = [] ∙ HL.inr HL.nil
hn→hl HN.case      = [] ∙ HL.case HL.nil
hn→hl HN.boom      = [] ∙ HL.boom HL.nil


-- Deduction theorem for linear Hilbert-style proofs.

hl-ded : ∀ {A B Γ} → HL Γ , A ⊢ B → HL Γ ⊢ A ⇒ B
hl-ded = hn→hl ∘ HN.ded ∘ hl→hn


-- Conversion from Hilbert-style proofs to Gentzen-style.

hn→g : ∀ {A Γ} → HN Γ ⊢ A → G Γ ⊢ A
hn→g (HN.var i)   = G.var i
hn→g (HN.app t u) = G.app (hn→g t) (hn→g u)
hn→g HN.ci        = G.ci
hn→g HN.ck        = G.ck
hn→g HN.cs        = G.cs
hn→g HN.pair      = G.cpair
hn→g HN.fst       = G.cfst
hn→g HN.snd       = G.csnd
hn→g HN.inl       = G.cinl
hn→g HN.inr       = G.cinr
hn→g HN.case      = G.ccase
hn→g HN.boom      = G.cboom

hl→g : ∀ {A Γ} → HL Γ ⊢ A → G Γ ⊢ A
hl→g = hn→g ∘ hl→hn


-- Conversion from Gentzen-style proofs to Hilbert-style.

g→hn : ∀ {A Γ} → G Γ ⊢ A → HN Γ ⊢ A
g→hn (G.var i)      = HN.var i
g→hn (G.lam t)      = HN.ded (g→hn t)
g→hn (G.app t u)    = HN.app (g→hn t) (g→hn u)
g→hn (G.pair t u)   = HN.fpair (g→hn t) (g→hn u)
g→hn (G.fst t)      = HN.ffst (g→hn t)
g→hn (G.snd t)      = HN.fsnd (g→hn t)
g→hn (G.inl t)      = HN.finl (g→hn t)
g→hn (G.inr t)      = HN.finr (g→hn t)
g→hn (G.case t u v) = HN.fcase (g→hn t) (g→hn u) (g→hn v)
g→hn (G.boom t)     = HN.fboom (g→hn t)

g→hl : ∀ {A Γ} → G Γ ⊢ A → HL Γ ⊢ A
g→hl = hn→hl ∘ g→hn
