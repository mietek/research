module IPC.Translation where

open import IPC.Hilbert.Translation public

import IPC.Hilbert.ListWithContext as LC
import IPC.Hilbert.TreeWithContext as TC
import IPC.Gentzen as G

open LC using () renaming (_⊢×_ to LC⟨_⊢×_⟩ ; _⊢_ to LC⟨_⊢_⟩) public
open TC using () renaming (_⊢_ to TC⟨_⊢_⟩) public
open G using () renaming (_⊢_ to G⟨_⊢_⟩) public


-- Translation from Hilbert-style to Gentzen-style.

tc→g : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
tc→g (TC.var i)   = G.var i
tc→g (TC.app t u) = G.app (tc→g t) (tc→g u)
tc→g TC.ci        = G.ci
tc→g TC.ck        = G.ck
tc→g TC.cs        = G.cs
tc→g TC.cpair     = G.cpair
tc→g TC.cfst      = G.cfst
tc→g TC.csnd      = G.csnd
tc→g TC.tt        = G.tt
tc→g TC.cboom     = G.cboom
tc→g TC.cinl      = G.cinl
tc→g TC.cinr      = G.cinr
tc→g TC.ccase     = G.ccase

lc→g : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
lc→g = tc→g ∘ lc→tc


-- Translation from Gentzen-style to Hilbert-style.

g→tc : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → TC⟨ Γ ⊢ A ⟩
g→tc (G.var i)      = TC.var i
g→tc (G.lam t)      = TC.lam (g→tc t)
g→tc (G.app t u)    = TC.app (g→tc t) (g→tc u)
g→tc (G.pair t u)   = TC.pair (g→tc t) (g→tc u)
g→tc (G.fst t)      = TC.fst (g→tc t)
g→tc (G.snd t)      = TC.snd (g→tc t)
g→tc G.tt           = TC.tt
g→tc (G.boom t)     = TC.boom (g→tc t)
g→tc (G.inl t)      = TC.inl (g→tc t)
g→tc (G.inr t)      = TC.inr (g→tc t)
g→tc (G.case t u v) = TC.case (g→tc t) (g→tc u) (g→tc v)

g→lc : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → LC⟨ Γ ⊢ A ⟩
g→lc = tc→lc ∘ g→tc
