module BasicIS4.Gentzen.Translation where

open import BasicIS4.Translation public

import BasicIS4.Gentzen.TreeWithContext as GTC
import BasicIS4.Gentzen.TreeWithContextPair as GTCP

open GTC using () renaming (_⊢_ to GTC⟨_⊢_⟩ ; _⊢⋆_ to GTC⟨_⊢⋆_⟩) public
open GTCP using () renaming (_⁏_⊢_ to GTCP⟨_⁏_⊢_⟩ ; _⁏_⊢⋆_ to GTCP⟨_⁏_⊢⋆_⟩) public


-- Translation between tree-shaped variants, with context and with context pair.

mutual
  gtc→mgtcp₀ : ∀ {A Γ} → GTC⟨ Γ ⊢ A ⟩ → GTCP⟨ Γ ⁏ ⌀ ⊢ A ⟩
  gtc→mgtcp₀ (GTC.var i)         = GTCP.var i
  gtc→mgtcp₀ (GTC.lam t)         = GTCP.lam (gtc→mgtcp₀ t)
  gtc→mgtcp₀ (GTC.app t u)       = GTCP.app (gtc→mgtcp₀ t) (gtc→mgtcp₀ u)
  gtc→mgtcp₀ (GTC.multibox ts u) = GTCP.multibox (gtc→mgtcp₀⋆ ts) (gtc→mgtcp₀ u)
  gtc→mgtcp₀ (GTC.down t)        = GTCP.down (gtc→mgtcp₀ t)
  gtc→mgtcp₀ (GTC.pair t u)      = GTCP.pair (gtc→mgtcp₀ t) (gtc→mgtcp₀ u)
  gtc→mgtcp₀ (GTC.fst t)         = GTCP.fst (gtc→mgtcp₀ t)
  gtc→mgtcp₀ (GTC.snd t)         = GTCP.snd (gtc→mgtcp₀ t)
  gtc→mgtcp₀ GTC.tt              = GTCP.tt

  gtc→mgtcp₀⋆ : ∀ {Π Γ} → GTC⟨ Γ ⊢⋆ Π ⟩ → GTCP⟨ Γ ⁏ ⌀ ⊢⋆ Π ⟩
  gtc→mgtcp₀⋆ {⌀}     ∙        = ∙
  gtc→mgtcp₀⋆ {Π , A} (ts , t) = gtc→mgtcp₀⋆ ts , gtc→mgtcp₀ t

gtc→gtcp : ∀ {A Γ Δ} → GTC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩ → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩
gtc→gtcp = GTCP.split ∘ gtc→mgtcp₀

-- NOTE: Direct translation fails the termination check.
mgtcp₀→gtc : ∀ {A Γ} → GTCP⟨ Γ ⁏ ⌀ ⊢ A ⟩ → GTC⟨ Γ ⊢ A ⟩
mgtcp₀→gtc = tc→gtc ∘ mgtcp₀→tc

gtcp→gtc : ∀ {A Γ Δ} → GTCP⟨ Γ ⁏ Δ ⊢ A ⟩ → GTC⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
gtcp→gtc = mgtcp₀→gtc ∘ GTCP.merge
