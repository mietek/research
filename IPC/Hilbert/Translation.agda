module IPC.Hilbert.Translation where

open import IPC public

import IPC.Hilbert.ListWithContext as LC
import IPC.Hilbert.TreeWithContext as TC

open LC using () renaming (_⊢×_ to LC⟨_⊢×_⟩ ; _⊢_ to LC⟨_⊢_⟩) public
open TC using () renaming (_⊢_ to TC⟨_⊢_⟩) public


-- Translation from list-shaped to tree-shaped variant, with context.

lc→tc : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → TC⟨ Γ ⊢ A ⟩
lc→tc (Π , ts) = lc×→tc ts top
  where
    lc×→tc : ∀ {A Γ Π} → LC⟨ Γ ⊢× Π ⟩ → A ∈ Π → TC⟨ Γ ⊢ A ⟩
    lc×→tc (LC.var i ts)  top     = TC.var i
    lc×→tc (LC.mp i j ts) top     = TC.app (lc×→tc ts i) (lc×→tc ts j)
    lc×→tc (LC.ci ts)     top     = TC.ci
    lc×→tc (LC.ck ts)     top     = TC.ck
    lc×→tc (LC.cs ts)     top     = TC.cs
    lc×→tc (LC.cpair ts)  top     = TC.cpair
    lc×→tc (LC.cfst ts)   top     = TC.cfst
    lc×→tc (LC.csnd ts)   top     = TC.csnd
    lc×→tc (LC.tt ts)     top     = TC.tt
    lc×→tc (LC.cboom ts)  top     = TC.cboom
    lc×→tc (LC.cinl ts)   top     = TC.cinl
    lc×→tc (LC.cinr ts)   top     = TC.cinr
    lc×→tc (LC.ccase ts)  top     = TC.ccase
    lc×→tc (LC.var i ts)  (pop k) = lc×→tc ts k
    lc×→tc (LC.mp i j ts) (pop k) = lc×→tc ts k
    lc×→tc (LC.ci ts)     (pop k) = lc×→tc ts k
    lc×→tc (LC.ck ts)     (pop k) = lc×→tc ts k
    lc×→tc (LC.cs ts)     (pop k) = lc×→tc ts k
    lc×→tc (LC.cpair ts)  (pop k) = lc×→tc ts k
    lc×→tc (LC.cfst ts)   (pop k) = lc×→tc ts k
    lc×→tc (LC.csnd ts)   (pop k) = lc×→tc ts k
    lc×→tc (LC.tt ts)     (pop k) = lc×→tc ts k
    lc×→tc (LC.cboom ts)  (pop k) = lc×→tc ts k
    lc×→tc (LC.cinl ts)   (pop k) = lc×→tc ts k
    lc×→tc (LC.cinr ts)   (pop k) = lc×→tc ts k
    lc×→tc (LC.ccase ts)  (pop k) = lc×→tc ts k


-- Translation from tree-shaped to list-shaped variant, with context.

tc→lc : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → LC⟨ Γ ⊢ A ⟩
tc→lc (TC.var i)   = ⌀ , LC.var i LC.nil
tc→lc (TC.app t u) = LC.app (tc→lc t) (tc→lc u)
tc→lc TC.ci        = ⌀ , LC.ci LC.nil
tc→lc TC.ck        = ⌀ , LC.ck LC.nil
tc→lc TC.cs        = ⌀ , LC.cs LC.nil
tc→lc TC.cpair     = ⌀ , LC.cpair LC.nil
tc→lc TC.cfst      = ⌀ , LC.cfst LC.nil
tc→lc TC.csnd      = ⌀ , LC.csnd LC.nil
tc→lc TC.tt        = ⌀ , LC.tt LC.nil
tc→lc TC.cboom     = ⌀ , LC.cboom LC.nil
tc→lc TC.cinl      = ⌀ , LC.cinl LC.nil
tc→lc TC.cinr      = ⌀ , LC.cinr LC.nil
tc→lc TC.ccase     = ⌀ , LC.ccase LC.nil


-- Deduction and detachment theorem for list-shaped variant, with context.

lc-lam : ∀ {A B Γ} → LC⟨ Γ , A ⊢ B ⟩ → LC⟨ Γ ⊢ A ▻ B ⟩
lc-lam = tc→lc ∘ TC.lam ∘ lc→tc

lc-lam⋆₀ : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → LC⟨ ⌀ ⊢ Γ ▻⋯▻ A ⟩
lc-lam⋆₀ = tc→lc ∘ TC.lam⋆₀ ∘ lc→tc

lc-det : ∀ {A B Γ} → LC⟨ Γ ⊢ A ▻ B ⟩ → LC⟨ Γ , A ⊢ B ⟩
lc-det = tc→lc ∘ TC.det ∘ lc→tc

lc-det⋆₀ : ∀ {A Γ} → LC⟨ ⌀ ⊢ Γ ▻⋯▻ A ⟩ → LC⟨ Γ ⊢ A ⟩
lc-det⋆₀ = tc→lc ∘ TC.det⋆₀ ∘ lc→tc
