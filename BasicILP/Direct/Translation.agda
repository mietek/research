module BasicILP.Direct.Translation where

open import Common.Context public

-- import BasicILP.Direct.Hilbert.Sequential as HS
import BasicILP.Direct.Hilbert.Nested as HN
import BasicILP.Direct.Gentzen as G

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

-- hs-lam : ∀ {A B Γ} → HS⟨ Γ , A ⊢ B ⟩ → HS⟨ Γ ⊢ A ▷ B ⟩
-- hs-lam = hn→hs ∘ HN.lam ∘ hs→hn


-- Translation from Hilbert-style to Gentzen-style.

mutual
  hn→gᴮᵒˣ : HN.Box → G.Box
  hn→gᴮᵒˣ HN.[ t ] = {!G.[ hn→g t ]!}

  hn→gᵀʸ : HN.Ty → G.Ty
  hn→gᵀʸ (HN.α P)   = G.α P
  hn→gᵀʸ (A HN.▷ B) = hn→gᵀʸ A G.▷ hn→gᵀʸ B
  hn→gᵀʸ (T HN.⦂ A) = hn→gᴮᵒˣ T G.⦂ hn→gᵀʸ A
  hn→gᵀʸ (A HN.∧ B) = hn→gᵀʸ A G.∧ hn→gᵀʸ B
  hn→gᵀʸ HN.⊤      = G.⊤

  hn→gᵀʸ⋆ : Cx HN.Ty → Cx G.Ty
  hn→gᵀʸ⋆ ⌀       = ⌀
  hn→gᵀʸ⋆ (Γ , A) = hn→gᵀʸ⋆ Γ , hn→gᵀʸ A

  hn→gᴵˣ : ∀ {A Γ} → A ∈ Γ → hn→gᵀʸ A ∈ hn→gᵀʸ⋆ Γ
  hn→gᴵˣ top     = top
  hn→gᴵˣ (pop i) = pop (hn→gᴵˣ i)

  hn→g : ∀ {A Γ} → HN⟨ Γ ⊢ A ⟩ → G⟨ hn→gᵀʸ⋆ Γ ⊢ hn→gᵀʸ A ⟩
  hn→g (HN.var i)   = G.var (hn→gᴵˣ i)
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
  g→hnᴮᵒˣ : G.Box → HN.Box
  g→hnᴮᵒˣ G.[ t ] = {!HN.[ g→hn t ]!}

  g→hnᵀʸ : G.Ty → HN.Ty
  g→hnᵀʸ (G.α P)   = HN.α P
  g→hnᵀʸ (A G.▷ B) = g→hnᵀʸ A HN.▷ g→hnᵀʸ B
  g→hnᵀʸ (T G.⦂ A) = g→hnᴮᵒˣ T HN.⦂ g→hnᵀʸ A
  g→hnᵀʸ (A G.∧ B) = g→hnᵀʸ A HN.∧ g→hnᵀʸ B
  g→hnᵀʸ G.⊤      = HN.⊤

  g→hnᵀʸ⋆ : Cx G.Ty → Cx HN.Ty
  g→hnᵀʸ⋆ ⌀       = ⌀
  g→hnᵀʸ⋆ (Γ , A) = g→hnᵀʸ⋆ Γ , g→hnᵀʸ A

  g→hnᴵˣ : ∀ {A Γ} → A ∈ Γ → g→hnᵀʸ A ∈ g→hnᵀʸ⋆ Γ
  g→hnᴵˣ top     = top
  g→hnᴵˣ (pop i) = pop (g→hnᴵˣ i)

  g→hn : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HN⟨ g→hnᵀʸ⋆ Γ ⊢ g→hnᵀʸ A ⟩
  g→hn (G.var i)         = HN.var (g→hnᴵˣ i)
  g→hn (G.lam t)         = HN.lam (g→hn t)
  g→hn (G.app t u)       = HN.app (g→hn t) (g→hn u)
--  g→hn (G.multibox ts u) = {!HN.multibox (g→hn⋆ ts) (g→hn u)!}
  g→hn (G.down t)        = HN.down (g→hn t)
  g→hn (G.pair t u)      = HN.pair (g→hn t) (g→hn u)
  g→hn (G.fst t)         = HN.fst (g→hn t)
  g→hn (G.snd t)         = HN.snd (g→hn t)
  g→hn G.tt              = HN.tt

  g→hn⋆ : ∀ {Π Γ} → G⟨ Γ ⊢⋆ Π ⟩ → HN⟨ g→hnᵀʸ⋆ Γ ⊢⋆ g→hnᵀʸ⋆ Π ⟩
  g→hn⋆ {⌀}     ∙        = ∙
  g→hn⋆ {Π , A} (ts , t) = g→hn⋆ ts , g→hn t

-- g→hs : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HS⟨ Γ ⊢ A ⟩
-- g→hs = hn→hs ∘ g→hn
