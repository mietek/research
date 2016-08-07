module BasicIPC.Translation where

open import BasicIPC.Hilbert.Translation public

import BasicIPC.Hilbert.List as L
import BasicIPC.Hilbert.Tree as T
import BasicIPC.Hilbert.ListWithContext as LC
import BasicIPC.Hilbert.TreeWithContext as TC
import BasicIPC.Gentzen as G

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

lc→g : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
lc→g = tc→g ∘ lc→tc

t→g₀ : ∀ {A} → T.⊢ A → G⟨ ⌀ ⊢ A ⟩
t→g₀ = tc→g ∘ t→tc₀

t→g : ∀ {A Γ} → T.⊢ Γ ▻⋯▻ A → G⟨ Γ ⊢ A ⟩
t→g = tc→g ∘ t→tc

l→g₀ : ∀ {A} → L.⊢ A → G⟨ ⌀ ⊢ A ⟩
l→g₀ = tc→g ∘ l→tc₀

l→g : ∀ {A Γ} → L.⊢ Γ ▻⋯▻ A → G⟨ Γ ⊢ A ⟩
l→g = tc→g ∘ l→tc


-- Translation from Gentzen-style to Hilbert-style.

g→tc : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → TC⟨ Γ ⊢ A ⟩
g→tc (G.var i)    = TC.var i
g→tc (G.lam t)    = TC.lam (g→tc t)
g→tc (G.app t u)  = TC.app (g→tc t) (g→tc u)
g→tc (G.pair t u) = TC.pair (g→tc t) (g→tc u)
g→tc (G.fst t)    = TC.fst (g→tc t)
g→tc (G.snd t)    = TC.snd (g→tc t)
g→tc G.tt         = TC.tt

g→lc : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → LC⟨ Γ ⊢ A ⟩
g→lc = tc→lc ∘ g→tc

g₀→t : ∀ {A} → G⟨ ⌀ ⊢ A ⟩ → T.⊢ A
g₀→t = tc₀→t ∘ g→tc

g→t : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → T.⊢ Γ ▻⋯▻ A
g→t = tc→t ∘ g→tc

g₀→l : ∀ {A} → G⟨ ⌀ ⊢ A ⟩ → L.⊢ A
g₀→l = tc₀→l ∘ g→tc

g→l : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → L.⊢ Γ ▻⋯▻ A
g→l = tc→l ∘ g→tc
