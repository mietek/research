module NewBasicILP.UntypedSyntax.Translation where

open import NewBasicILP.UntypedSyntax.Common public

import NewBasicILP.UntypedSyntax.ClosedHilbertSequential as CHS
import NewBasicILP.UntypedSyntax.ClosedHilbert as CH


-- Translation of types parametrised by a closed, untyped representation of syntax.

_↦ᵀ_ : ∀ {Rep Rep′} → (Rep → Rep′) → ClosedSyntax.Ty Rep → ClosedSyntax.Ty Rep′
f ↦ᵀ (ClosedSyntax.α P)     = ClosedSyntax.α P
f ↦ᵀ (A ClosedSyntax.▻ B)   = f ↦ᵀ A ClosedSyntax.▻ f ↦ᵀ B
f ↦ᵀ (ClosedSyntax.[ p ] A) = ClosedSyntax.[ f p ] f ↦ᵀ A
f ↦ᵀ (A ClosedSyntax.∧ B)   = f ↦ᵀ A ClosedSyntax.∧ f ↦ᵀ B
f ↦ᵀ ClosedSyntax.⊤        = ClosedSyntax.⊤


-- Translation from closed Hilbert-style sequential to closed Hilbert-style.

chs⊦→chᴿ : ∀ {n} → CHS.Reps n → Fin n → CH.Rep
chs⊦→chᴿ (CHS.MP i j ts) zero    = CH.APP (chs⊦→chᴿ ts i) (chs⊦→chᴿ ts j)
chs⊦→chᴿ (CHS.CI ts)     zero    = CH.CI
chs⊦→chᴿ (CHS.CK ts)     zero    = CH.CK
chs⊦→chᴿ (CHS.CS ts)     zero    = CH.CS
chs⊦→chᴿ (CHS.NEC ps ts) zero    = CH.BOX (chs⊦→chᴿ ps zero)
chs⊦→chᴿ (CHS.CDIST ts)  zero    = CH.CDIST
chs⊦→chᴿ (CHS.CUP ts)    zero    = CH.CUP
chs⊦→chᴿ (CHS.CDOWN ts)  zero    = CH.CDOWN
chs⊦→chᴿ (CHS.CPAIR ts)  zero    = CH.CPAIR
chs⊦→chᴿ (CHS.CFST ts)   zero    = CH.CFST
chs⊦→chᴿ (CHS.CSND ts)   zero    = CH.CSND
chs⊦→chᴿ (CHS.TT ts)     zero    = CH.TT
chs⊦→chᴿ (CHS.MP i j ts) (suc k) = chs⊦→chᴿ ts k
chs⊦→chᴿ (CHS.CI ts)     (suc k) = chs⊦→chᴿ ts k
chs⊦→chᴿ (CHS.CK ts)     (suc k) = chs⊦→chᴿ ts k
chs⊦→chᴿ (CHS.CS ts)     (suc k) = chs⊦→chᴿ ts k
chs⊦→chᴿ (CHS.NEC ps ts) (suc k) = chs⊦→chᴿ ts k
chs⊦→chᴿ (CHS.CDIST ts)  (suc k) = chs⊦→chᴿ ts k
chs⊦→chᴿ (CHS.CUP ts)    (suc k) = chs⊦→chᴿ ts k
chs⊦→chᴿ (CHS.CDOWN ts)  (suc k) = chs⊦→chᴿ ts k
chs⊦→chᴿ (CHS.CPAIR ts)  (suc k) = chs⊦→chᴿ ts k
chs⊦→chᴿ (CHS.CFST ts)   (suc k) = chs⊦→chᴿ ts k
chs⊦→chᴿ (CHS.CSND ts)   (suc k) = chs⊦→chᴿ ts k
chs⊦→chᴿ (CHS.TT ts)     (suc k) = chs⊦→chᴿ ts k

chs→chᴿ : CHS.Rep → CH.Rep
chs→chᴿ (n , ts) = chs⊦→chᴿ ts zero

chs→chᵀ : CHS.Ty → CH.Ty
chs→chᵀ A = chs→chᴿ ↦ᵀ A

chs⊦→ch : ∀ {A Ξ} → CHS.⊦⊢ Ξ → A ∈ Ξ → CH.⊢ chs→chᵀ A
chs⊦→ch (CHS.mp i j ts) top     = CH.app (chs⊦→ch ts i) (chs⊦→ch ts j)
chs⊦→ch (CHS.ci ts)     top     = CH.ci
chs⊦→ch (CHS.ck ts)     top     = CH.ck
chs⊦→ch (CHS.cs ts)     top     = CH.cs
chs⊦→ch (CHS.nec ps ts) top     = {!CH.box (chs⊦→ch ps top)!} -- NOTE: Does not fill.
chs⊦→ch (CHS.cdist ts)  top     = {!CH.cdist!}                 -- NOTE: Does not fill.
chs⊦→ch (CHS.cup ts)    top     = CH.cup
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

chs→ch : ∀ {A} → CHS.⊢ A → CH.⊢ chs→chᵀ A
chs→ch (Ξ , ts) = chs⊦→ch ts top


-- Translation from closed Hilbert-style to closed Hilbert-style sequential.

ch→chsᴿ : CH.Rep → CHS.Rep
ch→chsᴿ (CH.APP t u) = CHS.APP (ch→chsᴿ t) (ch→chsᴿ u)
ch→chsᴿ CH.CI        = zero , CHS.CI CHS.NIL
ch→chsᴿ CH.CK        = zero , CHS.CK CHS.NIL
ch→chsᴿ CH.CS        = zero , CHS.CS CHS.NIL
ch→chsᴿ (CH.BOX p)   = CHS.BOX (ch→chsᴿ p)
ch→chsᴿ CH.CDIST     = zero , CHS.CDIST CHS.NIL
ch→chsᴿ CH.CUP       = zero , CHS.CUP CHS.NIL
ch→chsᴿ CH.CDOWN     = zero , CHS.CDOWN CHS.NIL
ch→chsᴿ CH.CPAIR     = zero , CHS.CPAIR CHS.NIL
ch→chsᴿ CH.CFST      = zero , CHS.CFST CHS.NIL
ch→chsᴿ CH.CSND      = zero , CHS.CSND CHS.NIL
ch→chsᴿ CH.TT        = zero , CHS.TT CHS.NIL

ch→chsᵀ : CH.Ty → CHS.Ty
ch→chsᵀ A = ch→chsᴿ ↦ᵀ A

ch→chs : ∀ {A} → CH.⊢ A → CHS.⊢ (ch→chsᵀ A)
ch→chs (CH.app t u) = CHS.app (ch→chs t) (ch→chs u)
ch→chs CH.ci        = ⌀ , CHS.ci CHS.nil
ch→chs CH.ck        = ⌀ , CHS.ck CHS.nil
ch→chs CH.cs        = ⌀ , CHS.cs CHS.nil
ch→chs (CH.box p)   = {!CHS.box (ch→chs p)!} -- NOTE: Does not fill.
ch→chs CH.cdist     = ⌀ , CHS.cdist CHS.nil
ch→chs CH.cup       = ⌀ , CHS.cup CHS.nil
ch→chs CH.cdown     = ⌀ , CHS.cdown CHS.nil
ch→chs CH.cpair     = ⌀ , CHS.cpair CHS.nil
ch→chs CH.cfst      = ⌀ , CHS.cfst CHS.nil
ch→chs CH.csnd      = ⌀ , CHS.csnd CHS.nil
ch→chs CH.tt        = ⌀ , CHS.tt CHS.nil
