module BasicILP.Indirect.Translation where

open import BasicILP.Indirect public

import BasicILP.Indirect.Hilbert.Sequential as HS
import BasicILP.Indirect.Hilbert.Nested as HN
import BasicILP.Indirect.Gentzen as G

open HS using () renaming (_⊢×_ to HS⟨_⊢×_⟩ ; _⊢_ to HS⟨_⊢_⟩) public
open HN using () renaming (_⊢_ to HN⟨_⊢_⟩ ; _⊢⋆_ to HN⟨_⊢⋆_⟩) public
open G using  () renaming (_⊢_ to G⟨_⊢_⟩ ; _⊢⋆_ to G⟨_⊢⋆_⟩) public


-- Translation from sequential Hilbert-style to nested.

hs→hnᵀᵐ : HS.Tm → HN.Tm
hs→hnᵀᵐ TS = aux TS 0
  where
    aux : HS.Tm → ℕ → HN.Tm
    aux HS.NIL         zero    = {!!}
    aux (HS.VAR I TS)  zero    = HN.VAR I
    aux (HS.MP I J TS) zero    = HN.APP (aux TS I) (aux TS J)
    aux (HS.CI TS)     zero    = HN.CI
    aux (HS.CK TS)     zero    = HN.CK
    aux (HS.CS TS)     zero    = HN.CS
    aux (HS.NEC SS TS) zero    = HN.BOX (aux SS 0)
    aux (HS.CDIST TS)  zero    = HN.CDIST
    aux (HS.CUP TS)    zero    = HN.CUP
    aux (HS.CDOWN TS)  zero    = HN.CDOWN
    aux (HS.CPAIR TS)  zero    = HN.CPAIR
    aux (HS.CFST TS)   zero    = HN.CFST
    aux (HS.CSND TS)   zero    = HN.CSND
    aux (HS.TT TS)     zero    = HN.TT
    aux HS.NIL         (suc K) = {!!}
    aux (HS.VAR I TS)  (suc K) = aux TS K
    aux (HS.MP I J TS) (suc K) = aux TS K
    aux (HS.CI TS)     (suc K) = aux TS K
    aux (HS.CK TS)     (suc K) = aux TS K
    aux (HS.CS TS)     (suc K) = aux TS K
    aux (HS.NEC SS TS) (suc K) = aux TS K
    aux (HS.CDIST TS)  (suc K) = aux TS K
    aux (HS.CUP TS)    (suc K) = aux TS K
    aux (HS.CDOWN TS)  (suc K) = aux TS K
    aux (HS.CPAIR TS)  (suc K) = aux TS K
    aux (HS.CFST TS)   (suc K) = aux TS K
    aux (HS.CSND TS)   (suc K) = aux TS K
    aux (HS.TT TS)     (suc K) = aux TS K

hs→hnᵀʸ : Ty HS.Tm → Ty HN.Tm
hs→hnᵀʸ (α P)   = α P
hs→hnᵀʸ (A ▻ B) = hs→hnᵀʸ A ▻ hs→hnᵀʸ B
hs→hnᵀʸ (T ⦂ A) = hs→hnᵀᵐ T ⦂ hs→hnᵀʸ A
hs→hnᵀʸ (A ∧ B) = hs→hnᵀʸ A ∧ hs→hnᵀʸ B
hs→hnᵀʸ ⊤      = ⊤

hs→hnᵀʸ⋆ : Cx (Ty HS.Tm) → Cx (Ty HN.Tm)
hs→hnᵀʸ⋆ ∅       = ∅
hs→hnᵀʸ⋆ (Γ , A) = hs→hnᵀʸ⋆ Γ , hs→hnᵀʸ A

hs→hnᴵˣ : ∀ {A Γ} → A ∈ Γ → hs→hnᵀʸ A ∈ hs→hnᵀʸ⋆ Γ
hs→hnᴵˣ top     = top
hs→hnᴵˣ (pop i) = pop (hs→hnᴵˣ i)

hs→hn : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → HN⟨ hs→hnᵀʸ⋆ Γ ⊢ hs→hnᵀʸ A ⟩
hs→hn (Ξ , ts) = aux ts top
  where
    aux : ∀ {A Γ Ξ} → HS⟨ Γ ⊢× Ξ ⟩ → A ∈ Ξ → HN⟨ hs→hnᵀʸ⋆ Γ ⊢ hs→hnᵀʸ A ⟩
    aux (HS.var i ts)  top     = HN.var (hs→hnᴵˣ i)
    aux (HS.mp i j ts) top     = HN.app (aux ts i) (aux ts j)
    aux (HS.ci ts)     top     = HN.ci
    aux (HS.ck ts)     top     = HN.ck
    aux (HS.cs ts)     top     = HN.cs
    aux (HS.nec ss ts) top     = {!HN.box (aux ss top)!}
    aux (HS.cdist ts)  top     = {!HN.cdist!}
    aux (HS.cup ts)    top     = {!HN.cup!}
    aux (HS.cdown ts)  top     = HN.cdown
    aux (HS.cpair ts)  top     = HN.cpair
    aux (HS.cfst ts)   top     = HN.cfst
    aux (HS.csnd ts)   top     = HN.csnd
    aux (HS.tt ts)     top     = HN.tt
    aux (HS.var i ts)  (pop k) = aux ts k
    aux (HS.mp i j ts) (pop k) = aux ts k
    aux (HS.ci ts)     (pop k) = aux ts k
    aux (HS.ck ts)     (pop k) = aux ts k
    aux (HS.cs ts)     (pop k) = aux ts k
    aux (HS.nec ss ts) (pop k) = aux ts k
    aux (HS.cdist ts)  (pop k) = aux ts k
    aux (HS.cup ts)    (pop k) = aux ts k
    aux (HS.cdown ts)  (pop k) = aux ts k
    aux (HS.cpair ts)  (pop k) = aux ts k
    aux (HS.cfst ts)   (pop k) = aux ts k
    aux (HS.csnd ts)   (pop k) = aux ts k
    aux (HS.tt ts)     (pop k) = aux ts k


-- Translation from nested Hilbert-style to sequential.

hn→hsᵀᵐ : HN.Tm → HS.Tm
hn→hsᵀᵐ (HN.VAR I)   = HS.VAR I HS.NIL
hn→hsᵀᵐ (HN.APP T U) = HS.APP (hn→hsᵀᵐ T) (hn→hsᵀᵐ U)
hn→hsᵀᵐ HN.CI        = HS.CI HS.NIL
hn→hsᵀᵐ HN.CK        = HS.CK HS.NIL
hn→hsᵀᵐ HN.CS        = HS.CS HS.NIL
hn→hsᵀᵐ (HN.BOX T)   = HS.BOX (hn→hsᵀᵐ T)
hn→hsᵀᵐ HN.CDIST     = HS.CDIST HS.NIL
hn→hsᵀᵐ HN.CUP       = HS.CUP HS.NIL
hn→hsᵀᵐ HN.CDOWN     = HS.CDOWN HS.NIL
hn→hsᵀᵐ HN.CPAIR     = HS.CPAIR HS.NIL
hn→hsᵀᵐ HN.CFST      = HS.CFST HS.NIL
hn→hsᵀᵐ HN.CSND      = HS.CSND HS.NIL
hn→hsᵀᵐ HN.TT        = HS.TT HS.NIL

hn→hsᵀʸ : Ty HN.Tm → Ty HS.Tm
hn→hsᵀʸ (α P)   = α P
hn→hsᵀʸ (A ▻ B) = hn→hsᵀʸ A ▻ hn→hsᵀʸ B
hn→hsᵀʸ (T ⦂ A) = hn→hsᵀᵐ T ⦂ hn→hsᵀʸ A
hn→hsᵀʸ (A ∧ B) = hn→hsᵀʸ A ∧ hn→hsᵀʸ B
hn→hsᵀʸ ⊤      = ⊤

hn→hsᵀʸ⋆ : Cx (Ty HN.Tm) → Cx (Ty HS.Tm)
hn→hsᵀʸ⋆ ∅       = ∅
hn→hsᵀʸ⋆ (Γ , A) = hn→hsᵀʸ⋆ Γ , hn→hsᵀʸ A

hn→hsᴵˣ : ∀ {A Γ} → A ∈ Γ → hn→hsᵀʸ A ∈ hn→hsᵀʸ⋆ Γ
hn→hsᴵˣ top     = top
hn→hsᴵˣ (pop i) = pop (hn→hsᴵˣ i)

hn→hs : ∀ {A Γ} → HN⟨ Γ ⊢ A ⟩ → HS⟨ hn→hsᵀʸ⋆ Γ ⊢ hn→hsᵀʸ A ⟩
hn→hs (HN.var i)   = ∅ , HS.var (hn→hsᴵˣ i) HS.nil
hn→hs (HN.app t u) = HS.app (hn→hs t) (hn→hs u)
hn→hs HN.ci        = ∅ , HS.ci HS.nil
hn→hs HN.ck        = ∅ , HS.ck HS.nil
hn→hs HN.cs        = ∅ , HS.cs HS.nil
hn→hs (HN.box t)   = {!HS.box (hn→hs t)!}
hn→hs HN.cdist     = ∅ , HS.cdist HS.nil
hn→hs HN.cup       = ∅ , HS.cup HS.nil
hn→hs HN.cdown     = ∅ , HS.cdown HS.nil
hn→hs HN.cpair     = ∅ , HS.cpair HS.nil
hn→hs HN.cfst      = ∅ , HS.cfst HS.nil
hn→hs HN.csnd      = ∅ , HS.csnd HS.nil
hn→hs HN.tt        = ∅ , HS.tt HS.nil


-- Deduction theorem for sequential Hilbert-style.

hs→hn→hsᵀᵐ : ∀ {TS} → hn→hsᵀᵐ (hs→hnᵀᵐ TS) ≡ TS
hs→hn→hsᵀᵐ {HS.NIL}       = {!refl!}
hs→hn→hsᵀᵐ {HS.VAR I TS}  = cong² HS.VAR refl {!!}
hs→hn→hsᵀᵐ {HS.MP I J TS} = {!!}
hs→hn→hsᵀᵐ {HS.CI TS}     = {!!}
hs→hn→hsᵀᵐ {HS.CK TS}     = {!!}
hs→hn→hsᵀᵐ {HS.CS TS}     = {!!}
hs→hn→hsᵀᵐ {HS.NEC SS TS} = {!!}
hs→hn→hsᵀᵐ {HS.CDIST TS}  = {!!}
hs→hn→hsᵀᵐ {HS.CUP TS}    = {!!}
hs→hn→hsᵀᵐ {HS.CDOWN TS}  = {!!}
hs→hn→hsᵀᵐ {HS.CPAIR TS}  = {!!}
hs→hn→hsᵀᵐ {HS.CFST TS}   = {!!}
hs→hn→hsᵀᵐ {HS.CSND TS}   = {!!}
hs→hn→hsᵀᵐ {HS.TT TS}     = {!!}

hs→hn→hsᵀʸ : ∀ {A} → hn→hsᵀʸ (hs→hnᵀʸ A) ≡ A
hs→hn→hsᵀʸ {α P}   = refl
hs→hn→hsᵀʸ {A ▻ B} = cong² _▻_ hs→hn→hsᵀʸ hs→hn→hsᵀʸ
hs→hn→hsᵀʸ {T ⦂ A} = cong² _⦂_ hs→hn→hsᵀᵐ hs→hn→hsᵀʸ
hs→hn→hsᵀʸ {A ∧ B} = cong² _∧_ hs→hn→hsᵀʸ hs→hn→hsᵀʸ
hs→hn→hsᵀʸ {⊤}    = refl

-- hs-lam : ∀ {A B Γ} → HS⟨ Γ , A ⊢ B ⟩ → HS⟨ Γ ⊢ A ▻ B ⟩
-- hs-lam t = {!hn→hs (HN.lam (hs→hn t))!}
-- hn→hs ∘ HN.lam ∘ hs→hn


-- Translation from nested Hilbert-style to Gentzen-style.

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
hn→gᵀʸ (A ▻ B) = hn→gᵀʸ A ▻ hn→gᵀʸ B
hn→gᵀʸ (T ⦂ A) = hn→gᵀᵐ T ⦂ hn→gᵀʸ A
hn→gᵀʸ (A ∧ B) = hn→gᵀʸ A ∧ hn→gᵀʸ B
hn→gᵀʸ ⊤      = ⊤

hn→gᵀʸ⋆ : Cx (Ty HN.Tm) → Cx (Ty G.Tm)
hn→gᵀʸ⋆ ∅       = ∅
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


-- Translation from sequential Hilbert-style to Gentzen-style.

hs→gᵀʸ : Ty HS.Tm → Ty G.Tm
hs→gᵀʸ = hn→gᵀʸ ∘ hs→hnᵀʸ

hs→gᵀʸ⋆ : Cx (Ty HS.Tm) → Cx (Ty G.Tm)
hs→gᵀʸ⋆ = hn→gᵀʸ⋆ ∘ hs→hnᵀʸ⋆

hs→g : ∀ {A Γ} → HS⟨ Γ ⊢ A ⟩ → G⟨ hs→gᵀʸ⋆ Γ ⊢ hs→gᵀʸ A ⟩
hs→g = hn→g ∘ hs→hn


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
  g→hnᵀᵐ⋆ ∅        = ∅
  g→hnᵀᵐ⋆ (TS , T) = g→hnᵀᵐ⋆ TS , g→hnᵀᵐ T

g→hnᵀʸ : Ty G.Tm → Ty HN.Tm
g→hnᵀʸ (α P)   = α P
g→hnᵀʸ (A ▻ B) = g→hnᵀʸ A ▻ g→hnᵀʸ B
g→hnᵀʸ (T ⦂ A) = g→hnᵀᵐ T ⦂ g→hnᵀʸ A
g→hnᵀʸ (A ∧ B) = g→hnᵀʸ A ∧ g→hnᵀʸ B
g→hnᵀʸ ⊤      = ⊤

g→hnᵀʸ⋆ : Cx (Ty G.Tm) → Cx (Ty HN.Tm)
g→hnᵀʸ⋆ ∅       = ∅
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

  g→hn⋆ : ∀ {Ξ Γ} → G⟨ Γ ⊢⋆ Ξ ⟩ → HN⟨ g→hnᵀʸ⋆ Γ ⊢⋆ g→hnᵀʸ⋆ Ξ ⟩
  g→hn⋆ {∅}     ∙        = ∙
  g→hn⋆ {Ξ , A} (ts , t) = g→hn⋆ ts , g→hn t


-- Translation from Gentzen-style to sequential Hilbert-style.

g→hsᵀʸ : Ty G.Tm → Ty HS.Tm
g→hsᵀʸ = hn→hsᵀʸ ∘ g→hnᵀʸ

g→hsᵀʸ⋆ : Cx (Ty G.Tm) → Cx (Ty HS.Tm)
g→hsᵀʸ⋆ = hn→hsᵀʸ⋆ ∘ g→hnᵀʸ⋆

g→hs : ∀ {A Γ} → G⟨ Γ ⊢ A ⟩ → HS⟨ g→hsᵀʸ⋆ Γ ⊢ g→hsᵀʸ A ⟩
g→hs = hn→hs ∘ g→hn
