module NewBasicILP.Syntax.Translation where

open import Common.Context public

import NewBasicILP.Syntax.ClosedHilbertSequential as CHS
import NewBasicILP.Syntax.ClosedHilbert as CH


-- Translation from closed Hilbert-style sequential to closed Hilbert-style.

mutual
  chs→chᵀ : CHS.Ty → CH.Ty
  chs→chᵀ (CHS.α P)     = CH.α P
  chs→chᵀ (A CHS.▻ B)   = chs→chᵀ A CH.▻ chs→chᵀ B
  chs→chᵀ (CHS.[ p ] A) = CH.[ chs→ch (_ , p) ] (chs→chᵀ A)
  chs→chᵀ (A CHS.∧ B)   = chs→chᵀ A CH.∧ chs→chᵀ B
  chs→chᵀ CHS.⊤        = CH.⊤

  chs→ch : ∀ {A} → CHS.⊢ A → CH.⊢ (chs→chᵀ A)
  chs→ch (Ξ , ts) = chs⊦→ch ts top
    where
     chs⊦→ch : ∀ {A Ξ} → CHS.⊦⊢ Ξ → A ∈ Ξ → CH.⊢ (chs→chᵀ A)
     chs⊦→ch (CHS.mp i j ts) top     = CH.app (chs⊦→ch ts i) (chs⊦→ch ts j)
     chs⊦→ch (CHS.ci ts)     top     = CH.ci
     chs⊦→ch (CHS.ck ts)     top     = CH.ck
     chs⊦→ch (CHS.cs ts)     top     = CH.cs
     chs⊦→ch (CHS.nec ps ts) top     = {!CH.box (chs⊦→ch ps top)!}
     chs⊦→ch (CHS.cdist ts)  top     = {!CH.cdist!}
     chs⊦→ch (CHS.cup ts)    top     = {!CH.cup!}
     chs⊦→ch (CHS.cdown ts)  top     = CH.cdown
     chs⊦→ch (CHS.cpair ts)  top     = CH.cpair
     chs⊦→ch (CHS.cfst ts)   top     = CH.cfst
     chs⊦→ch (CHS.csnd ts)   top     = CH.csnd
     chs⊦→ch (CHS.tt ts)     top     = CH.tt
     chs⊦→ch (CHS.mp i j ts) (pop k) = chs⊦→ch ts k
     chs⊦→ch (CHS.ci ts)     (pop k) = chs⊦→ch ts k
     chs⊦→ch (CHS.ck ts)     (pop k) = chs⊦→ch ts k
     chs⊦→ch (CHS.cs ts)     (pop k) = chs⊦→ch ts k
     chs⊦→ch (CHS.nec ps ts) (pop k) = chs⊦→ch ts k
     chs⊦→ch (CHS.cdist ts)  (pop k) = chs⊦→ch ts k
     chs⊦→ch (CHS.cup ts)    (pop k) = chs⊦→ch ts k
     chs⊦→ch (CHS.cdown ts)  (pop k) = chs⊦→ch ts k
     chs⊦→ch (CHS.cpair ts)  (pop k) = chs⊦→ch ts k
     chs⊦→ch (CHS.cfst ts)   (pop k) = chs⊦→ch ts k
     chs⊦→ch (CHS.csnd ts)   (pop k) = chs⊦→ch ts k
     chs⊦→ch (CHS.tt ts)     (pop k) = chs⊦→ch ts k


-- Translation from closed Hilbert-style to closed Hilbert-style sequential.

mutual
  ch→chsᵀ : CH.Ty → CHS.Ty
  ch→chsᵀ (CH.α P)     = CHS.α P
  ch→chsᵀ (A CH.▻ B)   = ch→chsᵀ A CHS.▻ ch→chsᵀ B
  ch→chsᵀ (CH.[ p ] A) = CHS.[ π₂ (ch→chs p) ] (ch→chsᵀ A)
  ch→chsᵀ (A CH.∧ B)   = ch→chsᵀ A CHS.∧ ch→chsᵀ B
  ch→chsᵀ CH.⊤        = CHS.⊤

  ch→chs : ∀ {A} → CH.⊢ A → CHS.⊢ (ch→chsᵀ A)
  ch→chs (CH.app t u) = CHS.app (ch→chs t) (ch→chs u)
  ch→chs CH.ci        = ⌀ , CHS.ci CHS.nil
  ch→chs CH.ck        = ⌀ , CHS.ck CHS.nil
  ch→chs CH.cs        = ⌀ , CHS.cs CHS.nil
  ch→chs (CH.box t)   = CHS.box (ch→chs t)
  ch→chs CH.cdist     = ⌀ , CHS.cdist CHS.nil
  ch→chs CH.cup       = ⌀ , CHS.cup CHS.nil
  ch→chs CH.cdown     = ⌀ , CHS.cdown CHS.nil
  ch→chs CH.cpair     = ⌀ , CHS.cpair CHS.nil
  ch→chs CH.cfst      = ⌀ , CHS.cfst CHS.nil
  ch→chs CH.csnd      = ⌀ , CHS.csnd CHS.nil
  ch→chs CH.tt        = ⌀ , CHS.tt CHS.nil
