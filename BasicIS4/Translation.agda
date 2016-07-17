module BasicIS4.Translation where

open import BasicIS4.Core public

import BasicIS4.Regular.Hilbert.Sequential as RHS
import BasicIS4.Regular.Hilbert.Nested as RHN
import BasicIS4.Regular.Gentzen.Core as RG
import BasicIS4.Regular.Translation as RT
import BasicIS4.Dual.Hilbert.Sequential as DHS
import BasicIS4.Dual.Hilbert.Nested as DHN
import BasicIS4.Dual.Gentzen.Core as DG
import BasicIS4.Dual.Translation as DT

open RHS using () renaming (_⊢_ to RHS⟨_⊢_⟩) public
open RHN using () renaming (_⊢_ to RHN⟨_⊢_⟩) public
open RG  using () renaming (_⊢_ to RG⟨_⊢_⟩ ; _⊢⋆_ to RG⟨_⊢⋆_⟩) public
open DHS using () renaming (_⨾_⊢_ to DHS⟨_⨾_⊢_⟩) public
open DHN using () renaming (_⨾_⊢_ to DHN⟨_⨾_⊢_⟩) public
open DG  using () renaming (_⨾_⊢_ to DG⟨_⨾_⊢_⟩ ; _⨾_⊢⋆_ to DG⟨_⨾_⊢⋆_⟩) public


-- Translation from regular Hilbert-style to dual-context.

rhn→dhn : ∀ {A Γ Δ} → RHN⟨ Γ ⊢ A ⟩ → DHN⟨ Γ ⨾ Δ ⊢ A ⟩
rhn→dhn = DHN.mmono⊢ bot⊆ ∘ aux
  where
    aux : ∀ {A Γ} → RHN⟨ Γ ⊢ A ⟩ → DHN⟨ Γ ⨾ ⌀ ⊢ A ⟩
    aux (RHN.var i)   = DHN.var i
    aux (RHN.app t u) = DHN.app (aux t) (aux u)
    aux RHN.ci        = DHN.ci
    aux RHN.ck        = DHN.ck
    aux RHN.cs        = DHN.cs
    aux (RHN.box t)   = DHN.box (aux t)
    aux RHN.cdist     = DHN.cdist
    aux RHN.cup       = DHN.cup
    aux RHN.cdown     = DHN.cdown
    aux RHN.cpair     = DHN.cpair
    aux RHN.cfst      = DHN.cfst
    aux RHN.csnd      = DHN.csnd
    aux RHN.tt        = DHN.tt

rhs→dhs : ∀ {A Γ Δ} → RHS⟨ Γ ⊢ A ⟩ → DHS⟨ Γ ⨾ Δ ⊢ A ⟩
rhs→dhs = DT.hn→hs ∘ rhn→dhn ∘ RT.hs→hn


-- Translation from regular Gentzen-style to dual-context.

rg→dg : ∀ {A Γ Δ} → RG⟨ Γ ⊢ A ⟩ → DG⟨ Γ ⨾ Δ ⊢ A ⟩
rg→dg = DG.mmono⊢ bot⊆ ∘ aux
  where
    mutual
      aux : ∀ {A Γ} → RG⟨ Γ ⊢ A ⟩ → DG⟨ Γ ⨾ ⌀ ⊢ A ⟩
      aux (RG.var i)         = DG.var i
      aux (RG.lam t)         = DG.lam (aux t)
      aux (RG.app t u)       = DG.app (aux t) (aux u)
      aux (RG.multibox ts u) = DG.multibox (aux⋆ ts) (aux u)
      aux (RG.down t)        = DG.down (aux t)
      aux (RG.pair t u)      = DG.pair (aux t) (aux u)
      aux (RG.fst t)         = DG.fst (aux t)
      aux (RG.snd t)         = DG.snd (aux t)
      aux RG.tt              = DG.tt

      aux⋆ : ∀ {Π Γ} → RG⟨ Γ ⊢⋆ Π ⟩ → DG⟨ Γ ⨾ ⌀ ⊢⋆ Π ⟩
      aux⋆ {⌀}     ᴬᵍtt          = ᴬᵍtt
      aux⋆ {Π , A} (ᴬᵍpair ts t) = ᴬᵍpair (aux⋆ ts) (aux t)


-- Translation from dual-context Hilbert-style to regular.

dhn→rhn : ∀ {A Γ Δ} → DHN⟨ Γ ⨾ Δ ⊢ A ⟩ → RHN⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dhn→rhn = aux ∘ DHN.merge
  where
    aux : ∀ {A Γ} → DHN⟨ Γ ⨾ ⌀ ⊢ A ⟩ → RHN⟨ Γ ⊢ A ⟩
    aux (DHN.var i)   = RHN.var i
    aux (DHN.app t u) = RHN.app (aux t) (aux u)
    aux DHN.ci        = RHN.ci
    aux DHN.ck        = RHN.ck
    aux DHN.cs        = RHN.cs
    aux (DHN.mvar ())
    aux (DHN.box t)   = RHN.box (aux t)
    aux DHN.cdist     = RHN.cdist
    aux DHN.cup       = RHN.cup
    aux DHN.cdown     = RHN.cdown
    aux DHN.cpair     = RHN.cpair
    aux DHN.cfst      = RHN.cfst
    aux DHN.csnd      = RHN.csnd
    aux DHN.tt        = RHN.tt

dhs→rhs : ∀ {A Γ Δ} → DHS⟨ Γ ⨾ Δ ⊢ A ⟩ → RHS⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dhs→rhs = RT.hn→hs ∘ dhn→rhn ∘ DT.hs→hn


-- Translation from dual-context Gentzen-style to regular.

dg→rg : ∀ {A Γ Δ} → DG⟨ Γ ⨾ Δ ⊢ A ⟩ → RG⟨ Γ ⧺ (□⋆ Δ) ⊢ A ⟩
dg→rg = RT.hn→g ∘ dhn→rhn ∘ DT.g→hn

-- TODO:
-- dg→rg = aux ∘ DG.merge
--   where
--     aux : ∀ {A Γ} → DG⟨ Γ ⨾ ⌀ ⊢ A ⟩ → RG⟨ Γ ⊢ A ⟩
--     aux (DG.var i)     = RG.var i
--     aux (DG.lam t)     = RG.lam (aux t)
--     aux (DG.app t u)   = RG.app (aux t) (aux u)
--     aux (DG.mvar ())
--     aux (DG.box t)     = RG.box (aux t)
-- NOTE: Growing this argument fails the termination check.
--     aux (DG.unbox t u) = RG.unbox (aux t) (aux (DG.det (DG.mlam u)))
--     aux (DG.pair t u)  = RG.pair (aux t) (aux u)
--     aux (DG.fst t)     = RG.fst (aux t)
--     aux (DG.snd t)     = RG.snd (aux t)
--     aux DG.tt          = RG.tt
