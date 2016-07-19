module BasicIS4.Regular.Translation where

open import BasicIS4 public

import BasicIS4.Regular.Hilbert.Sequential as HS
import BasicIS4.Regular.Hilbert.Nested as HN
import BasicIS4.Regular.Gentzen as G

open HS using () renaming (_⊢×_ to HS⟨_⊢×_⟩ ; _⊢_ to HS⟨_⊢_⟩) public
open HN using () renaming (_⊢_ to HN⟨_⊢_⟩ ; _⊢⋆_ to HN⟨_⊢⋆_⟩) public
open G using  () renaming (_⊢_ to G⟨_⊢_⟩ ; _⊢⋆_ to G⟨_⊢⋆_⟩) public


-- Translation from sequential Hilbert-style to nested.

hs→hn : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → HN⟨ Γ ⊢ A ⟩
hs→hn (Π , ts) = aux ts top
  where
    aux : ∀ {A Γ Π} → HS⟨ Γ ⊢× Π ⟩ → A ∈ Π → HN⟨ Γ ⊢ A ⟩
    aux (HS.var i ts)  top     = HN.var i
    aux (HS.mp i j ts) top     = HN.app (aux ts i) (aux ts j)
    aux (HS.ci ts)     top     = HN.ci
    aux (HS.ck ts)     top     = HN.ck
    aux (HS.cs ts)     top     = HN.cs
    aux (HS.nec ss ts) top     = HN.box (aux ss top)
    aux (HS.cdist ts)  top     = HN.cdist
    aux (HS.cup ts)    top     = HN.cup
    aux (HS.cdown ts)  top     = HN.cdown
    aux (HS.cpair ts)  top     = HN.cpair
    aux (HS.cfst ts)   top     = HN.cfst
    aux (HS.csnd ts)   top     = HN.csnd
    aux (HS.tt ts)     top     = HN.tt
    aux (HS.var i ts)  (pop k) = aux ts k
    aux (HS.mp i j ts) (pop k) = aux ts k
    aux (HS.ci ts)     (pop k) = aux ts k
    aux (HS.ck ts)     (pop k) = aux ts k
    aux (HS.cs ts)     (pop k) = aux ts k
    aux (HS.nec ss ts) (pop k) = aux ts k
    aux (HS.cdist ts)  (pop k) = aux ts k
    aux (HS.cup ts)    (pop k) = aux ts k
    aux (HS.cdown ts)  (pop k) = aux ts k
    aux (HS.cpair ts)  (pop k) = aux ts k
    aux (HS.cfst ts)   (pop k) = aux ts k
    aux (HS.csnd ts)   (pop k) = aux ts k
    aux (HS.tt ts)     (pop k) = aux ts k


-- Translation from nested Hilbert-style to sequential.

hn→hs : ∀ {A Γ} → HN⟨ Γ ⊢ A ⟩ → HS⟨ Γ ⊢ A ⟩
hn→hs (HN.var i)   = ⌀ , HS.var i HS.nil
hn→hs (HN.app t u) = HS.app (hn→hs t) (hn→hs u)
hn→hs HN.ci        = ⌀ , HS.ci HS.nil
hn→hs HN.ck        = ⌀ , HS.ck HS.nil
hn→hs HN.cs        = ⌀ , HS.cs HS.nil
hn→hs (HN.box t)   = HS.box (hn→hs t)
hn→hs HN.cdist     = ⌀ , HS.cdist HS.nil
hn→hs HN.cup       = ⌀ , HS.cup HS.nil
hn→hs HN.cdown     = ⌀ , HS.cdown HS.nil
hn→hs HN.cpair     = ⌀ , HS.cpair HS.nil
hn→hs HN.cfst      = ⌀ , HS.cfst HS.nil
hn→hs HN.csnd      = ⌀ , HS.csnd HS.nil
hn→hs HN.tt        = ⌀ , HS.tt HS.nil


-- Deduction theorem for sequential Hilbert-style.

hs-lam : ∀ {A B Γ} → HS⟨ Γ , A ⊢ B ⟩ → HS⟨ Γ ⊢ A ▷ B ⟩
hs-lam = hn→hs ∘ HN.lam ∘ hs→hn


-- Translation from Hilbert-style to Gentzen-style.

hn→g : ∀ {A Γ} → HN⟨ Γ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
hn→g (HN.var i)   = G.var i
hn→g (HN.app t u) = G.app (hn→g t) (hn→g u)
hn→g HN.ci        = G.ci
hn→g HN.ck        = G.ck
hn→g HN.cs        = G.cs
hn→g (HN.box t)   = G.box (hn→g t)
hn→g HN.cdist     = G.cdist
hn→g HN.cup       = G.cup
hn→g HN.cdown     = G.cdown
hn→g HN.cpair     = G.cpair
hn→g HN.cfst      = G.cfst
hn→g HN.csnd      = G.csnd
hn→g HN.tt        = G.tt

hs→g : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
hs→g = hn→g ∘ hs→hn


-- Translation from Gentzen-style to Hilbert-style.

mutual
  g→hn : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HN⟨ Γ ⊢ A ⟩
  g→hn (G.var i)         = HN.var i
  g→hn (G.lam t)         = HN.lam (g→hn t)
  g→hn (G.app t u)       = HN.app (g→hn t) (g→hn u)
  g→hn (G.multibox ts u) = HN.multibox (g→hn⋆ ts) (g→hn u)
  g→hn (G.down t)        = HN.down (g→hn t)
  g→hn (G.pair t u)      = HN.pair (g→hn t) (g→hn u)
  g→hn (G.fst t)         = HN.fst (g→hn t)
  g→hn (G.snd t)         = HN.snd (g→hn t)
  g→hn G.tt              = HN.tt

  g→hn⋆ : ∀ {Π Γ} → G⟨ Γ ⊢⋆ Π ⟩ → HN⟨ Γ ⊢⋆ Π ⟩
  g→hn⋆ {⌀}     ∙        = ∙
  g→hn⋆ {Π , A} (ts , t) = g→hn⋆ ts , g→hn t

g→hs : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HS⟨ Γ ⊢ A ⟩
g→hs = hn→hs ∘ g→hn
