module OlderBasicILP.Direct.Translation where

open import Common.Context public

-- import OlderBasicILP.Direct.Hilbert.Sequential as HS
import OlderBasicILP.Direct.Hilbert.Nested as HN
import OlderBasicILP.Direct.Gentzen as G

-- open HS using () renaming (_⊢×_ to HS⟨_⊢×_⟩ ; _⊢_ to HS⟨_⊢_⟩) public
open HN using () renaming (_⊢_ to HN⟨_⊢_⟩ ; _⊢⋆_ to HN⟨_⊢⋆_⟩) public
open G using  () renaming (_⊢_ to G⟨_⊢_⟩ ; _⊢⋆_ to G⟨_⊢⋆_⟩) public


-- Translation from sequential Hilbert-style to nested.

-- hs→hn : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → HN⟨ Γ ⊢ A ⟩
-- hs→hn = ?


-- Translation from nested Hilbert-style to sequential.

-- hn→hs : ∀ {A Γ} → HN⟨ Γ ⊢ A ⟩ → HS⟨ Γ ⊢ A ⟩
-- hn→hs = ?


-- Deduction theorem for sequential Hilbert-style.

-- hs-lam : ∀ {A B Γ} → HS⟨ Γ , A ⊢ B ⟩ → HS⟨ Γ ⊢ A ▻ B ⟩
-- hs-lam = hn→hs ∘ HN.lam ∘ hs→hn


-- Translation from Hilbert-style to Gentzen-style.

mutual
  hn→gᵇᵒˣ : HN.Box → G.Box
  hn→gᵇᵒˣ HN.[ t ] = {!G.[ hn→g t ]!}

  hn→gᵀ : HN.Ty → G.Ty
  hn→gᵀ (HN.α P)   = G.α P
  hn→gᵀ (A HN.▻ B) = hn→gᵀ A G.▻ hn→gᵀ B
  hn→gᵀ (T HN.⦂ A) = hn→gᵇᵒˣ T G.⦂ hn→gᵀ A
  hn→gᵀ (A HN.∧ B) = hn→gᵀ A G.∧ hn→gᵀ B
  hn→gᵀ HN.⊤      = G.⊤

  hn→gᵀ⋆ : Cx HN.Ty → Cx G.Ty
  hn→gᵀ⋆ ∅       = ∅
  hn→gᵀ⋆ (Γ , A) = hn→gᵀ⋆ Γ , hn→gᵀ A

  hn→gⁱ : ∀ {A Γ} → A ∈ Γ → hn→gᵀ A ∈ hn→gᵀ⋆ Γ
  hn→gⁱ top     = top
  hn→gⁱ (pop i) = pop (hn→gⁱ i)

  hn→g : ∀ {A Γ} → HN⟨ Γ ⊢ A ⟩ → G⟨ hn→gᵀ⋆ Γ ⊢ hn→gᵀ A ⟩
  hn→g (HN.var i)   = G.var (hn→gⁱ i)
  hn→g (HN.app t u) = G.app (hn→g t) (hn→g u)
  hn→g HN.ci        = G.ci
  hn→g HN.ck        = G.ck
  hn→g HN.cs        = G.cs
  hn→g (HN.box t)   = {!G.box (hn→g t)!}
  hn→g HN.cdist     = {!G.cdist!}
  hn→g HN.cup       = {!G.cup!}
  hn→g HN.cdown     = G.cdown
  hn→g HN.cpair     = G.cpair
  hn→g HN.cfst      = G.cfst
  hn→g HN.csnd      = G.csnd
  hn→g HN.tt        = G.tt

-- hs→g : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → G⟨ Γ ⊢ A ⟩
-- hs→g = hn→g ∘ hs→hn


-- Translation from Gentzen-style to Hilbert-style.

mutual
  g→hnᵇᵒˣ : G.Box → HN.Box
  g→hnᵇᵒˣ G.[ t ] = {!HN.[ g→hn t ]!}

  g→hnᵀ : G.Ty → HN.Ty
  g→hnᵀ (G.α P)   = HN.α P
  g→hnᵀ (A G.▻ B) = g→hnᵀ A HN.▻ g→hnᵀ B
  g→hnᵀ (T G.⦂ A) = g→hnᵇᵒˣ T HN.⦂ g→hnᵀ A
  g→hnᵀ (A G.∧ B) = g→hnᵀ A HN.∧ g→hnᵀ B
  g→hnᵀ G.⊤      = HN.⊤

  g→hnᵀ⋆ : Cx G.Ty → Cx HN.Ty
  g→hnᵀ⋆ ∅       = ∅
  g→hnᵀ⋆ (Γ , A) = g→hnᵀ⋆ Γ , g→hnᵀ A

  g→hnⁱ : ∀ {A Γ} → A ∈ Γ → g→hnᵀ A ∈ g→hnᵀ⋆ Γ
  g→hnⁱ top     = top
  g→hnⁱ (pop i) = pop (g→hnⁱ i)

  g→hn : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HN⟨ g→hnᵀ⋆ Γ ⊢ g→hnᵀ A ⟩
  g→hn (G.var i)         = HN.var (g→hnⁱ i)
  g→hn (G.lam t)         = HN.lam (g→hn t)
  g→hn (G.app t u)       = HN.app (g→hn t) (g→hn u)
--  g→hn (G.multibox ts u) = {!HN.multibox (g→hn⋆ ts) (g→hn u)!}
  g→hn (G.down t)        = HN.down (g→hn t)
  g→hn (G.pair t u)      = HN.pair (g→hn t) (g→hn u)
  g→hn (G.fst t)         = HN.fst (g→hn t)
  g→hn (G.snd t)         = HN.snd (g→hn t)
  g→hn G.tt              = HN.tt

  g→hn⋆ : ∀ {Ξ Γ} → G⟨ Γ ⊢⋆ Ξ ⟩ → HN⟨ g→hnᵀ⋆ Γ ⊢⋆ g→hnᵀ⋆ Ξ ⟩
  g→hn⋆ {∅}     ∙        = ∙
  g→hn⋆ {Ξ , A} (ts , t) = g→hn⋆ ts , g→hn t

-- g→hs : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HS⟨ Γ ⊢ A ⟩
-- g→hs = hn→hs ∘ g→hn
