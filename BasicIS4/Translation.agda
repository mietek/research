module BasicIS4.Translation where

open import BasicIS4.Hilbert.Translation public

import BasicIS4.Hilbert.List as L
import BasicIS4.Hilbert.ListWithContext as LC
import BasicIS4.Hilbert.ListWithContextPair as LCP
import BasicIS4.Hilbert.Tree as T
import BasicIS4.Hilbert.TreeWithContext as TC
import BasicIS4.Hilbert.TreeWithContextPair as TCP
import BasicIS4.Gentzen.TreeWithContext as GTC
import BasicIS4.Gentzen.TreeWithContextPair as GTCP

open LC using () renaming (_⊢×_ to LC⟨_⊢×_⟩ ; _⊢_ to LC⟨_⊢_⟩) public
open LCP using () renaming (_⁏_⊢×_ to LCP⟨_⁏_⊢×_⟩ ; _⁏_⊢_ to LCP⟨_⁏_⊢_⟩) public
open TC using () renaming (_⊢_ to TC⟨_⊢_⟩ ; _⊢⋆_ to TC⟨_⊢⋆_⟩) public
open TCP using () renaming (_⁏_⊢_ to TCP⟨_⁏_⊢_⟩) public
open GTC using () renaming (_⊢_ to GTC⟨_⊢_⟩ ; _⊢⋆_ to GTC⟨_⊢⋆_⟩) public
open GTCP using () renaming (_⁏_⊢_ to GTCP⟨_⁏_⊢_⟩ ; _⁏_⊢⋆_ to GTCP⟨_⁏_⊢⋆_⟩) public


-- Translation from Hilbert-style to Gentzen-style, with context.

tc→gtc : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → GTC⟨ Γ ⊢ A ⟩
tc→gtc (TC.var i)   = GTC.var i
tc→gtc (TC.app t u) = GTC.app (tc→gtc t) (tc→gtc u)
tc→gtc TC.ci        = GTC.ci
tc→gtc TC.ck        = GTC.ck
tc→gtc TC.cs        = GTC.cs
tc→gtc (TC.box t)   = GTC.box (tc→gtc t)
tc→gtc TC.cdist     = GTC.cdist
tc→gtc TC.cup       = GTC.cup
tc→gtc TC.cdown     = GTC.cdown
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


-- Translation from Gentzen-style to Hilbert-style, with context.

mutual
  gtc→tc : ∀ {A Γ} → GTC⟨ Γ ⊢ A ⟩ → TC⟨ Γ ⊢ A ⟩
  gtc→tc (GTC.var i)         = TC.var i
  gtc→tc (GTC.lam t)         = TC.lam (gtc→tc t)
  gtc→tc (GTC.app t u)       = TC.app (gtc→tc t) (gtc→tc u)
  gtc→tc (GTC.multibox ts u) = TC.multibox (gtc→tc⋆ ts) (gtc→tc u)
  gtc→tc (GTC.down t)        = TC.down (gtc→tc t)
  gtc→tc (GTC.pair t u)      = TC.pair (gtc→tc t) (gtc→tc u)
  gtc→tc (GTC.fst t)         = TC.fst (gtc→tc t)
  gtc→tc (GTC.snd t)         = TC.snd (gtc→tc t)
  gtc→tc GTC.tt              = TC.tt

  gtc→tc⋆ : ∀ {Π Γ} → GTC⟨ Γ ⊢⋆ Π ⟩ → TC⟨ Γ ⊢⋆ Π ⟩
  gtc→tc⋆ {⌀}     ∙        = ∙
  gtc→tc⋆ {Π , A} (ts , t) = gtc→tc⋆ ts , gtc→tc t

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


-- Translation from Hilbert-style to Gentzen-style, with context pair.

tcp→gtcp : ∀ {A Γ Δ} → TCP⟨ Γ ⁏ Δ ⊢ A ⟩ → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩
tcp→gtcp (TCP.var i)   = GTCP.var i
tcp→gtcp (TCP.app t u) = GTCP.app (tcp→gtcp t) (tcp→gtcp u)
tcp→gtcp TCP.ci        = GTCP.ci
tcp→gtcp TCP.ck        = GTCP.ck
tcp→gtcp TCP.cs        = GTCP.cs
tcp→gtcp (TCP.mvar i)  = GTCP.mvar i
tcp→gtcp (TCP.box t)   = GTCP.box (tcp→gtcp t)
tcp→gtcp TCP.cdist     = GTCP.cdist
tcp→gtcp TCP.cup       = GTCP.cup
tcp→gtcp TCP.cdown     = GTCP.cdown
tcp→gtcp TCP.cpair     = GTCP.cpair
tcp→gtcp TCP.cfst      = GTCP.cfst
tcp→gtcp TCP.csnd      = GTCP.csnd
tcp→gtcp TCP.tt        = GTCP.tt

lcp→gtcp : ∀ {A Γ Δ} → LCP⟨ Γ ⁏ Δ ⊢ A ⟩ → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩
lcp→gtcp = tcp→gtcp ∘ lcp→tcp

tc→mgtcp₀ : ∀ {A Γ} → TC⟨ Γ ⊢ A ⟩ → GTCP⟨ Γ ⁏ ⌀ ⊢ A ⟩
tc→mgtcp₀ = tcp→gtcp ∘ tc→mtcp₀

tc→gtcp : ∀ {A Γ Δ} → TC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩
tc→gtcp = tcp→gtcp ∘ tc→tcp

lc→mgtcp₀ : ∀ {A Γ} → LC⟨ Γ ⊢ A ⟩ → GTCP⟨ Γ ⁏ ⌀ ⊢ A ⟩
lc→mgtcp₀ = tcp→gtcp ∘ lc→mtcp₀

lc→gtcp : ∀ {A Γ Δ} → LC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩
lc→gtcp = tcp→gtcp ∘ lc→tcp


-- Translation from Gentzen-style to Hilbert-style, with context pair.

gtcp→tcp : ∀ {A Γ Δ} → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩ → TCP⟨ Γ ⁏ Δ ⊢ A ⟩
gtcp→tcp (GTCP.var i)     = TCP.var i
gtcp→tcp (GTCP.lam t)     = TCP.lam (gtcp→tcp t)
gtcp→tcp (GTCP.app t u)   = TCP.app (gtcp→tcp t) (gtcp→tcp u)
gtcp→tcp (GTCP.mvar i)    = TCP.mvar i
gtcp→tcp (GTCP.box t)     = TCP.box (gtcp→tcp t)
gtcp→tcp (GTCP.unbox t u) = TCP.unbox (gtcp→tcp t) (gtcp→tcp u)
gtcp→tcp (GTCP.pair t u)  = TCP.pair (gtcp→tcp t) (gtcp→tcp u)
gtcp→tcp (GTCP.fst t)     = TCP.fst (gtcp→tcp t)
gtcp→tcp (GTCP.snd t)     = TCP.snd (gtcp→tcp t)
gtcp→tcp GTCP.tt          = TCP.tt

gtcp→lcp : ∀ {A Γ Δ} → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩ → LCP⟨ Γ ⁏ Δ ⊢ A ⟩
gtcp→lcp = tcp→lcp ∘ gtcp→tcp

mgtcp₀→tc : ∀ {A Γ} → GTCP⟨ Γ ⁏ ⌀ ⊢ A ⟩ → TC⟨ Γ ⊢ A ⟩
mgtcp₀→tc = mtcp₀→tc ∘ gtcp→tcp

gtcp→tc : ∀ {A Γ Δ} → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩ → TC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
gtcp→tc = tcp→tc ∘ gtcp→tcp

mgtcp₀→lc : ∀ {A Γ} → GTCP⟨ Γ ⁏ ⌀ ⊢ A ⟩ → LC⟨ Γ ⊢ A ⟩
mgtcp₀→lc = mtcp₀→lc ∘ gtcp→tcp

gtcp→lc : ∀ {A Γ Δ} → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩ → LC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
gtcp→lc = tcp→lc ∘ gtcp→tcp
