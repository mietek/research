module BasicILP.Indirect.Translation where

open import BasicILP.Indirect public

-- import BasicILP.Indirect.Hilbert.Sequential as HS
import BasicILP.Indirect.Hilbert.Nested as HN
import BasicILP.Indirect.Gentzen as G

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

hn→gᵀᵐ : HN.Tm → G.Tm
hn→gᵀᵐ (HN.VAR I)   = G.VAR I
hn→gᵀᵐ (HN.APP T U) = G.APP (hn→gᵀᵐ T) (hn→gᵀᵐ U)
hn→gᵀᵐ HN.CI        = G.CI
hn→gᵀᵐ HN.CK        = G.CK
hn→gᵀᵐ HN.CS        = G.CS
hn→gᵀᵐ (HN.BOX T)   = G.BOX (hn→gᵀᵐ T)
hn→gᵀᵐ HN.CDIST     = G.CDIST
hn→gᵀᵐ HN.CUP       = G.CUP
hn→gᵀᵐ HN.CDOWN     = G.CDOWN
hn→gᵀᵐ HN.CPAIR     = G.CPAIR
hn→gᵀᵐ HN.CFST      = G.CFST
hn→gᵀᵐ HN.CSND      = G.CSND
hn→gᵀᵐ HN.TT        = G.TT

hn→gᵀʸ : Ty HN.Tm → Ty G.Tm
hn→gᵀʸ (α P)   = α P
hn→gᵀʸ (A ▷ B) = hn→gᵀʸ A ▷ hn→gᵀʸ B
hn→gᵀʸ (T ⦂ A) = hn→gᵀᵐ T ⦂ hn→gᵀʸ A
hn→gᵀʸ (A ∧ B) = hn→gᵀʸ A ∧ hn→gᵀʸ B
hn→gᵀʸ ⊤      = ⊤

hn→gᵀʸ⋆ : Cx (Ty HN.Tm) → Cx (Ty G.Tm)
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
  g→hnᵀᵐ : G.Tm → HN.Tm
  g→hnᵀᵐ (G.VAR I)         = HN.VAR I
  g→hnᵀᵐ (G.LAM T)         = HN.LAM (g→hnᵀᵐ T)
  g→hnᵀᵐ (G.APP T U)       = HN.APP (g→hnᵀᵐ T) (g→hnᵀᵐ U)
  g→hnᵀᵐ (G.MULTIBOX TS U) = HN.MULTIBOX (g→hnᵀᵐ⋆ TS) (g→hnᵀᵐ U)
  g→hnᵀᵐ (G.DOWN T)        = HN.DOWN (g→hnᵀᵐ T)
  g→hnᵀᵐ (G.PAIR T U)      = HN.PAIR (g→hnᵀᵐ T) (g→hnᵀᵐ U)
  g→hnᵀᵐ (G.FST T)         = HN.FST (g→hnᵀᵐ T)
  g→hnᵀᵐ (G.SND T)         = HN.SND (g→hnᵀᵐ T)
  g→hnᵀᵐ G.TT              = HN.TT

  g→hnᵀᵐ⋆ : Cx G.Tm → Cx HN.Tm
  g→hnᵀᵐ⋆ ⌀        = ⌀
  g→hnᵀᵐ⋆ (TS , T) = g→hnᵀᵐ⋆ TS , g→hnᵀᵐ T

g→hnᵀʸ : Ty G.Tm → Ty HN.Tm
g→hnᵀʸ (α P)   = α P
g→hnᵀʸ (A ▷ B) = g→hnᵀʸ A ▷ g→hnᵀʸ B
g→hnᵀʸ (T ⦂ A) = g→hnᵀᵐ T ⦂ g→hnᵀʸ A
g→hnᵀʸ (A ∧ B) = g→hnᵀʸ A ∧ g→hnᵀʸ B
g→hnᵀʸ ⊤      = ⊤

g→hnᵀʸ⋆ : Cx (Ty G.Tm) → Cx (Ty HN.Tm)
g→hnᵀʸ⋆ ⌀       = ⌀
g→hnᵀʸ⋆ (Γ , A) = g→hnᵀʸ⋆ Γ , g→hnᵀʸ A

g→hnᴵˣ : ∀ {A Γ} → A ∈ Γ → g→hnᵀʸ A ∈ g→hnᵀʸ⋆ Γ
g→hnᴵˣ top     = top
g→hnᴵˣ (pop i) = pop (g→hnᴵˣ i)

mutual
  g→hn : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HN⟨ g→hnᵀʸ⋆ Γ ⊢ g→hnᵀʸ A ⟩
  g→hn (G.var i)         = HN.var (g→hnᴵˣ i)
  g→hn (G.lam t)         = HN.lam (g→hn t)
  g→hn (G.app t u)       = HN.app (g→hn t) (g→hn u)
  g→hn (G.multibox ts u) = {!HN.multibox (g→hn⋆ ts) (g→hn u)!}
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
