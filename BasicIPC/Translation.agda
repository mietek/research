module BasicIPC.Translation where

open import BasicIPC.Hilbert.Translation public

import BasicIPC.Hilbert.List as L
import BasicIPC.Hilbert.ListWithContext as LC
import BasicIPC.Hilbert.Tree as T
import BasicIPC.Hilbert.TreeWithContext as TC
import BasicIPC.Gentzen as GTC

open LC using () renaming (_⊢×_ to LC⟨_⊢×_⟩ ; _⊢_ to LC⟨_⊢_⟩) public
open TC using () renaming (_⊢_ to TC⟨_⊢_⟩) public
open GTC using () renaming (_⊢_ to GTC⟨_⊢_⟩) public


-- Translation from Hilbert-style to Gentzen-style.

tc→gtc : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → GTC⟨ Γ ⊢ A ⟩
tc→gtc (TC.var i)   = GTC.var i
tc→gtc (TC.app t u) = GTC.app (tc→gtc t) (tc→gtc u)
tc→gtc TC.ci        = GTC.ci
tc→gtc TC.ck        = GTC.ck
tc→gtc TC.cs        = GTC.cs
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


-- Translation from Gentzen-style to Hilbert-style.

gtc→tc : ∀ {A Γ} → GTC⟨ Γ ⊢ A ⟩ → TC⟨ Γ ⊢ A ⟩
gtc→tc (GTC.var i)    = TC.var i
gtc→tc (GTC.lam t)    = TC.lam (gtc→tc t)
gtc→tc (GTC.app t u)  = TC.app (gtc→tc t) (gtc→tc u)
gtc→tc (GTC.pair t u) = TC.pair (gtc→tc t) (gtc→tc u)
gtc→tc (GTC.fst t)    = TC.fst (gtc→tc t)
gtc→tc (GTC.snd t)    = TC.snd (gtc→tc t)
gtc→tc GTC.tt         = TC.tt

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
