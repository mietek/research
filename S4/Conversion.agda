module S4.Conversion where

open import S4.Core public

import S4.Hilbert.Linear as HL
import S4.Hilbert.Nested as HN
import S4.Gentzen.PfenningDavies as GPD

open HL using (_++⁺_) renaming (_⨾_⊢⁺_ to HL_⨾_⊢⁺_ ; _⨾_⊢_ to HL_⨾_⊢_) public
open HN using () renaming (_⨾_⊢_ to HN_⨾_⊢_) public
open GPD using () renaming (_⨾_⊢_ to GPD_⨾_⊢_) public


-- Conversion from linear Hilbert-style proofs to nested.

hl→hn : ∀ {A Γ Δ} → HL Γ ⨾ Δ ⊢ A → HN Γ ⨾ Δ ⊢ A
hl→hn (Π ∙ ts) = aux ts top
  where
    aux : ∀ {A Γ Δ Π} → HL Γ ⨾ Δ ⊢⁺ Π → Π ∋ A → HN Γ ⨾ Δ ⊢ A
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

hn→hl : ∀ {A Γ Δ} → HN Γ ⨾ Δ ⊢ A → HL Γ ⨾ Δ ⊢ A
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

hl-ded : ∀ {A B Γ Δ} → HL Γ , A ⨾ Δ ⊢ B → HL Γ ⨾ Δ ⊢ A ⇒ B
hl-ded = hn→hl ∘ HN.ded ∘ hl→hn

hl-mded : ∀ {A B Γ Δ} → HL Γ ⨾ Δ , A ⊢ B → HL Γ ⨾ Δ ⊢ □ A ⇒ B
hl-mded = hn→hl ∘ HN.mded ∘ hl→hn


-- Conversion from Hilbert-style proofs to Gentzen-style.

hn→gpd : ∀ {A Γ Δ} → HN Γ ⨾ Δ ⊢ A → GPD Γ ⨾ Δ ⊢ A
hn→gpd (HN.var i)   = GPD.var i
hn→gpd (HN.app t u) = GPD.app (hn→gpd t) (hn→gpd u)
hn→gpd HN.ci        = GPD.ci
hn→gpd HN.ck        = GPD.ck
hn→gpd HN.cs        = GPD.cs
hn→gpd (HN.mvar i)  = GPD.mvar i
hn→gpd (HN.nec t)   = GPD.box (hn→gpd t)
hn→gpd HN.dist      = GPD.cdist
hn→gpd HN.up        = GPD.cup
hn→gpd HN.down      = GPD.cdown
hn→gpd HN.pair      = GPD.cpair
hn→gpd HN.fst       = GPD.cfst
hn→gpd HN.snd       = GPD.csnd
hn→gpd HN.inl       = GPD.cinl
hn→gpd HN.inr       = GPD.cinr
hn→gpd HN.case      = GPD.ccase
hn→gpd HN.boom      = GPD.cboom

hl→gpd : ∀ {A Γ Δ} → HL Γ ⨾ Δ ⊢ A → GPD Γ ⨾ Δ ⊢ A
hl→gpd = hn→gpd ∘ hl→hn


-- Conversion from Gentzen-style proofs to Hilbert-style.

gpd→hn : ∀ {A Γ Δ} → GPD Γ ⨾ Δ ⊢ A → HN Γ ⨾ Δ ⊢ A
gpd→hn (GPD.var i)      = HN.var i
gpd→hn (GPD.lam t)      = HN.ded (gpd→hn t)
gpd→hn (GPD.app t u)    = HN.app (gpd→hn t) (gpd→hn u)
gpd→hn (GPD.mvar i)     = HN.mvar i
gpd→hn (GPD.box t)      = HN.nec (gpd→hn t)
gpd→hn (GPD.unbox t u)  = HN.app (HN.mded (gpd→hn u)) (gpd→hn t)
gpd→hn (GPD.pair t u)   = HN.fpair (gpd→hn t) (gpd→hn u)
gpd→hn (GPD.fst t)      = HN.ffst (gpd→hn t)
gpd→hn (GPD.snd t)      = HN.fsnd (gpd→hn t)
gpd→hn (GPD.inl t)      = HN.finl (gpd→hn t)
gpd→hn (GPD.inr t)      = HN.finr (gpd→hn t)
gpd→hn (GPD.case t u v) = HN.fcase (gpd→hn t) (gpd→hn u) (gpd→hn v)
gpd→hn (GPD.boom t)     = HN.fboom (gpd→hn t)

gpd→hl : ∀ {A Γ Δ} → GPD Γ ⨾ Δ ⊢ A → HL Γ ⨾ Δ ⊢ A
gpd→hl = hn→hl ∘ gpd→hn
