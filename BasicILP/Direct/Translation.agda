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

-- hs-lam : ∀ {A B Γ} → HS⟨ Γ , A ⊢ B ⟩ → HS⟨ Γ ⊢ A ▻ B ⟩
-- hs-lam = hn→hs ∘ HN.lam ∘ hs→hn


-- Translation from Hilbert-style to Gentzen-style.

mutual
  hn→gᵇᵒˣ : HN.Box → G.Box
  hn→gᵇᵒˣ HN.[ t ] = {!G.[ hn→g t ]!}

  hn→gᵗʸ : HN.Ty → G.Ty
  hn→gᵗʸ (HN.α P)   = G.α P
  hn→gᵗʸ (A HN.▻ B) = hn→gᵗʸ A G.▻ hn→gᵗʸ B
  hn→gᵗʸ (T HN.⦂ A) = hn→gᵇᵒˣ T G.⦂ hn→gᵗʸ A
  hn→gᵗʸ (A HN.∧ B) = hn→gᵗʸ A G.∧ hn→gᵗʸ B
  hn→gᵗʸ HN.⊤      = G.⊤

  hn→gᵗʸ⋆ : Cx HN.Ty → Cx G.Ty
  hn→gᵗʸ⋆ ⌀       = ⌀
  hn→gᵗʸ⋆ (Γ , A) = hn→gᵗʸ⋆ Γ , hn→gᵗʸ A

  hn→gⁱˣ : ∀ {A Γ} → A ∈ Γ → hn→gᵗʸ A ∈ hn→gᵗʸ⋆ Γ
  hn→gⁱˣ top     = top
  hn→gⁱˣ (pop i) = pop (hn→gⁱˣ i)

  hn→g : ∀ {A Γ} → HN⟨ Γ ⊢ A ⟩ → G⟨ hn→gᵗʸ⋆ Γ ⊢ hn→gᵗʸ A ⟩
  hn→g (HN.var i)   = G.var (hn→gⁱˣ i)
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

  g→hnᵗʸ : G.Ty → HN.Ty
  g→hnᵗʸ (G.α P)   = HN.α P
  g→hnᵗʸ (A G.▻ B) = g→hnᵗʸ A HN.▻ g→hnᵗʸ B
  g→hnᵗʸ (T G.⦂ A) = g→hnᵇᵒˣ T HN.⦂ g→hnᵗʸ A
  g→hnᵗʸ (A G.∧ B) = g→hnᵗʸ A HN.∧ g→hnᵗʸ B
  g→hnᵗʸ G.⊤      = HN.⊤

  g→hnᵗʸ⋆ : Cx G.Ty → Cx HN.Ty
  g→hnᵗʸ⋆ ⌀       = ⌀
  g→hnᵗʸ⋆ (Γ , A) = g→hnᵗʸ⋆ Γ , g→hnᵗʸ A

  g→hnⁱˣ : ∀ {A Γ} → A ∈ Γ → g→hnᵗʸ A ∈ g→hnᵗʸ⋆ Γ
  g→hnⁱˣ top     = top
  g→hnⁱˣ (pop i) = pop (g→hnⁱˣ i)

  g→hn : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HN⟨ g→hnᵗʸ⋆ Γ ⊢ g→hnᵗʸ A ⟩
  g→hn (G.var i)         = HN.var (g→hnⁱˣ i)
  g→hn (G.lam t)         = HN.lam (g→hn t)
  g→hn (G.app t u)       = HN.app (g→hn t) (g→hn u)
--  g→hn (G.multibox ts u) = {!HN.multibox (g→hn⋆ ts) (g→hn u)!}
  g→hn (G.down t)        = HN.down (g→hn t)
  g→hn (G.pair t u)      = HN.pair (g→hn t) (g→hn u)
  g→hn (G.fst t)         = HN.fst (g→hn t)
  g→hn (G.snd t)         = HN.snd (g→hn t)
  g→hn G.tt              = HN.tt

  g→hn⋆ : ∀ {Π Γ} → G⟨ Γ ⊢⋆ Π ⟩ → HN⟨ g→hnᵗʸ⋆ Γ ⊢⋆ g→hnᵗʸ⋆ Π ⟩
  g→hn⋆ {⌀}     ∙        = ∙
  g→hn⋆ {Π , A} (ts , t) = g→hn⋆ ts , g→hn t

-- g→hs : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HS⟨ Γ ⊢ A ⟩
-- g→hs = hn→hs ∘ g→hn
