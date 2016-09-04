module OldBasicILP.Syntax.Translation where

open import Common.Context public

import OldBasicILP.Syntax.ClosedHilbertSequential as CHS
import OldBasicILP.Syntax.ClosedHilbert as CH


-- Translation from closed Hilbert-style sequential to closed Hilbert-style.

mutual
  chsᵀ→chᵀ : CHS.Ty → CH.Ty
  chsᵀ→chᵀ (CHS.α P)   = CH.α P
  chsᵀ→chᵀ (A CHS.▻ B) = chsᵀ→chᵀ A CH.▻ chsᵀ→chᵀ B
  chsᵀ→chᵀ (p CHS.⦂ A) = chsᴾ→chᴾ p CH.⦂ chsᵀ→chᵀ A
  chsᵀ→chᵀ (A CHS.∧ B) = chsᵀ→chᵀ A CH.∧ chsᵀ→chᵀ B
  chsᵀ→chᵀ CHS.⊤      = CH.⊤

  chsᴾ→chᴾ : ∀ {Ξ A} → CHS.Proof Ξ A → CH.Proof (chsᵀ→chᵀ A)
  chsᴾ→chᴾ CHS.[ d ] = CH.[ chsᴰ→ch d top ]

  chsᴰ→ch : ∀ {Ξ A} → CHS.⊢ᴰ Ξ → A ∈ Ξ → CH.⊢ (chsᵀ→chᵀ A)
  chsᴰ→ch (CHS.mp i j d) top     = CH.app (chsᴰ→ch d i) (chsᴰ→ch d j)
  chsᴰ→ch (CHS.ci d)     top     = CH.ci
  chsᴰ→ch (CHS.ck d)     top     = CH.ck
  chsᴰ→ch (CHS.cs d)     top     = CH.cs
  chsᴰ→ch (CHS.nec `d d) top     = CH.box (chsᴰ→ch `d top)
  chsᴰ→ch (CHS.cdist {Ξ} {A} {B} {`Ξ₁} {`Ξ₂} {`d₁} {`d₂} d) top = oops {A} {B} {`Ξ₁} {`Ξ₂} {`d₁} {`d₂}
  chsᴰ→ch (CHS.cup d)    top     = CH.cup
  chsᴰ→ch (CHS.cdown d)  top     = CH.cdown
  chsᴰ→ch (CHS.cpair d)  top     = CH.cpair
  chsᴰ→ch (CHS.cfst d)   top     = CH.cfst
  chsᴰ→ch (CHS.csnd d)   top     = CH.csnd
  chsᴰ→ch (CHS.tt d)     top     = CH.tt
  chsᴰ→ch (CHS.mp i j d) (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.ci d)     (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.ck d)     (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.cs d)     (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.nec `d d) (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.cdist d)  (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.cup d)    (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.cdown d)  (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.cpair d)  (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.cfst d)   (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.csnd d)   (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.tt d)     (pop k) = chsᴰ→ch d k

  -- FIXME: I can’t even postulate this.
  -- postulate
  --   ᴬlem₁ : ∀ {Ξ₁ Ξ₂ A B} {d₁ : CHS.⊢ᴰ Ξ₁ , A CHS.▻ B} {d₂ : CHS.⊢ᴰ Ξ₂ , A}
  --           → chsᴰ→ch (CHS.appᴰ d₁ d₂) ≡ CH.app (chsᴰ→ch d₁ top) (chsᴰ→ch d₂ top)

  postulate
    oops : ∀ {A B Ξ₁ Ξ₂} {d₁ : CHS.⊢ᴰ Ξ₁ , A CHS.▻ B} {d₂ : CHS.⊢ᴰ Ξ₂ , A}
           → CH.⊢ chsᴾ→chᴾ CHS.[ d₁ ] CH.⦂ (chsᵀ→chᵀ A CH.▻ chsᵀ→chᵀ B) CH.▻
                    chsᴾ→chᴾ CHS.[ d₂ ] CH.⦂ chsᵀ→chᵀ A CH.▻
                    chsᴾ→chᴾ CHS.[ CHS.appᴰ d₁ d₂ ] CH.⦂ chsᵀ→chᵀ B

  chs→ch : ∀ {A} → CHS.⊢ A → CH.⊢ (chsᵀ→chᵀ A)
  chs→ch (Ξ , d) = chsᴰ→ch d top


-- Translation from closed Hilbert-style to closed Hilbert-style sequential.

mutual
  chᵀ→chsᵀ : CH.Ty → CHS.Ty
  chᵀ→chsᵀ (CH.α P)   = CHS.α P
  chᵀ→chsᵀ (A CH.▻ B) = chᵀ→chsᵀ A CHS.▻ chᵀ→chsᵀ B
  chᵀ→chsᵀ (p CH.⦂ A) with chᴾ→chsᴾ p
  chᵀ→chsᵀ (p CH.⦂ A) | (Ξ , p′) = p′ CHS.⦂ chᵀ→chsᵀ A
  chᵀ→chsᵀ (A CH.∧ B) = chᵀ→chsᵀ A CHS.∧ chᵀ→chsᵀ B
  chᵀ→chsᵀ CH.⊤      = CHS.⊤

  chᴾ→chsᴾ : ∀ {A} → CH.Proof A → ∃ (λ Ξ → CHS.Proof Ξ (chᵀ→chsᵀ A))
  chᴾ→chsᴾ CH.[ d ] with ch→chs d
  chᴾ→chsᴾ CH.[ d ] | (Ξ , d′) = Ξ , CHS.[ d′ ]

  ch→chs : ∀ {A} → CH.⊢ A → CHS.⊢ (chᵀ→chsᵀ A)
  ch→chs (CH.app d₁ d₂) = CHS.app (ch→chs d₁) (ch→chs d₂)
  ch→chs CH.ci          = ∅ , CHS.ci CHS.nil
  ch→chs CH.ck          = ∅ , CHS.ck CHS.nil
  ch→chs CH.cs          = ∅ , CHS.cs CHS.nil
  ch→chs (CH.box d)     = CHS.box (ch→chs d)
  ch→chs CH.cdist       = ∅ , CHS.cdist CHS.nil
  ch→chs CH.cup         = ∅ , CHS.cup CHS.nil
  ch→chs CH.cdown       = ∅ , CHS.cdown CHS.nil
  ch→chs CH.cpair       = ∅ , CHS.cpair CHS.nil
  ch→chs CH.cfst        = ∅ , CHS.cfst CHS.nil
  ch→chs CH.csnd        = ∅ , CHS.csnd CHS.nil
  ch→chs CH.tt          = ∅ , CHS.tt CHS.nil
