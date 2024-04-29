module A201607.OldBasicILP.UntypedSyntax.Translation where

open import A201607.OldBasicILP.UntypedSyntax.Common public

import A201607.OldBasicILP.UntypedSyntax.ClosedHilbertSequential as CHS
import A201607.OldBasicILP.UntypedSyntax.ClosedHilbert as CH


-- Translation of types parametrised by a closed, untyped representation of syntax.

_↦ᵀ_ : ∀ {Rep Rep′} → (Rep → Rep′) → ClosedSyntax.Ty Rep → ClosedSyntax.Ty Rep′
f ↦ᵀ (ClosedSyntax.α P)   = ClosedSyntax.α P
f ↦ᵀ (A ClosedSyntax.▻ B) = f ↦ᵀ A ClosedSyntax.▻ f ↦ᵀ B
f ↦ᵀ (p ClosedSyntax.⦂ A) = f p ClosedSyntax.⦂ f ↦ᵀ A
f ↦ᵀ (A ClosedSyntax.∧ B) = f ↦ᵀ A ClosedSyntax.∧ f ↦ᵀ B
f ↦ᵀ ClosedSyntax.⊤      = ClosedSyntax.⊤


-- Translation from closed Hilbert-style sequential to closed Hilbert-style.

chsᴿ→chᴿ : ∀ {n} → CHS.Rep n → Fin n → CH.Rep
chsᴿ→chᴿ (CHS.MP i j r) zero    = CH.APP (chsᴿ→chᴿ r i) (chsᴿ→chᴿ r j)
chsᴿ→chᴿ (CHS.CI r)     zero    = CH.CI
chsᴿ→chᴿ (CHS.CK r)     zero    = CH.CK
chsᴿ→chᴿ (CHS.CS r)     zero    = CH.CS
chsᴿ→chᴿ (CHS.NEC `r r) zero    = CH.BOX (chsᴿ→chᴿ `r zero)
chsᴿ→chᴿ (CHS.CDIST r)  zero    = CH.CDIST
chsᴿ→chᴿ (CHS.CUP r)    zero    = CH.CUP
chsᴿ→chᴿ (CHS.CDOWN r)  zero    = CH.CDOWN
chsᴿ→chᴿ (CHS.CPAIR r)  zero    = CH.CPAIR
chsᴿ→chᴿ (CHS.CFST r)   zero    = CH.CFST
chsᴿ→chᴿ (CHS.CSND r)   zero    = CH.CSND
chsᴿ→chᴿ (CHS.UNIT r)   zero    = CH.UNIT
chsᴿ→chᴿ (CHS.MP i j r) (suc k) = chsᴿ→chᴿ r k
chsᴿ→chᴿ (CHS.CI r)     (suc k) = chsᴿ→chᴿ r k
chsᴿ→chᴿ (CHS.CK r)     (suc k) = chsᴿ→chᴿ r k
chsᴿ→chᴿ (CHS.CS r)     (suc k) = chsᴿ→chᴿ r k
chsᴿ→chᴿ (CHS.NEC `r r) (suc k) = chsᴿ→chᴿ r k
chsᴿ→chᴿ (CHS.CDIST r)  (suc k) = chsᴿ→chᴿ r k
chsᴿ→chᴿ (CHS.CUP r)    (suc k) = chsᴿ→chᴿ r k
chsᴿ→chᴿ (CHS.CDOWN r)  (suc k) = chsᴿ→chᴿ r k
chsᴿ→chᴿ (CHS.CPAIR r)  (suc k) = chsᴿ→chᴿ r k
chsᴿ→chᴿ (CHS.CFST r)   (suc k) = chsᴿ→chᴿ r k
chsᴿ→chᴿ (CHS.CSND r)   (suc k) = chsᴿ→chᴿ r k
chsᴿ→chᴿ (CHS.UNIT r)   (suc k) = chsᴿ→chᴿ r k

chsᴾ→chᴾ : CHS.Proof → CH.Proof
chsᴾ→chᴾ CHS.[ r ] = CH.[ chsᴿ→chᴿ r zero ]

chsᵀ→chᵀ : CHS.Ty → CH.Ty
chsᵀ→chᵀ = chsᴾ→chᴾ ↦ᵀ_

-- FIXME: What is going on here?
postulate
  ᴬlem₁ : ∀ {n₁ n₂} → (r₁ : CHS.Rep (suc n₁)) → (r₂ : CHS.Rep (suc n₂))
          → chsᴿ→chᴿ (CHS.APP r₁ r₂) zero ≡ CH.APP (chsᴿ→chᴿ r₁ zero) (chsᴿ→chᴿ r₂ zero)

mutual
  chsᴰ→ch : ∀ {Ξ A} → CHS.⊢ᴰ Ξ → A ∈ Ξ → CH.⊢ chsᵀ→chᵀ A
  chsᴰ→ch (CHS.mp i j d)               top     = CH.app (chsᴰ→ch d i) (chsᴰ→ch d j)
  chsᴰ→ch (CHS.ci d)                   top     = CH.ci
  chsᴰ→ch (CHS.ck d)                   top     = CH.ck
  chsᴰ→ch (CHS.cs d)                   top     = CH.cs
  chsᴰ→ch (CHS.nec `d d)               top     rewrite ᴬlem₂ `d top = CH.box (chsᴰ→ch `d top)
  chsᴰ→ch (CHS.cdist {r₁ = r₁} {r₂} d) top     rewrite ᴬlem₁ r₁ r₂  = CH.cdist
  chsᴰ→ch (CHS.cup d)                  top     = CH.cup
  chsᴰ→ch (CHS.cdown d)                top     = CH.cdown
  chsᴰ→ch (CHS.cpair d)                top     = CH.cpair
  chsᴰ→ch (CHS.cfst d)                 top     = CH.cfst
  chsᴰ→ch (CHS.csnd d)                 top     = CH.csnd
  chsᴰ→ch (CHS.unit d)                 top     = CH.unit
  chsᴰ→ch (CHS.mp i j d)               (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.ci d)                   (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.ck d)                   (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.cs d)                   (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.nec `d d)               (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.cdist d)                (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.cup d)                  (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.cdown d)                (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.cpair d)                (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.cfst d)                 (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.csnd d)                 (pop k) = chsᴰ→ch d k
  chsᴰ→ch (CHS.unit d)                 (pop k) = chsᴰ→ch d k

  ᴬlem₂ : ∀ {Ξ A} → (d : CHS.⊢ᴰ Ξ) → (k : A ∈ Ξ)
         → chsᴿ→chᴿ CHS.ᴿ⌊ d ⌋ ⁱ⌊ k ⌋ ≡ CH.ᴿ⌊ chsᴰ→ch d k ⌋
  ᴬlem₂ CHS.nil                      ()
  ᴬlem₂ (CHS.mp i j d)               top     = cong² CH.APP (ᴬlem₂ d i) (ᴬlem₂ d j)
  ᴬlem₂ (CHS.ci d)                   top     = refl
  ᴬlem₂ (CHS.ck d)                   top     = refl
  ᴬlem₂ (CHS.cs d)                   top     = refl
  ᴬlem₂ (CHS.nec `d d)               top     rewrite ᴬlem₂ `d top = cong CH.BOX refl
  ᴬlem₂ (CHS.cdist {r₁ = r₁} {r₂} d) top     rewrite ᴬlem₁ r₁ r₂ = refl
  ᴬlem₂ (CHS.cup d)                  top     = refl
  ᴬlem₂ (CHS.cdown d)                top     = refl
  ᴬlem₂ (CHS.cpair d)                top     = refl
  ᴬlem₂ (CHS.cfst d)                 top     = refl
  ᴬlem₂ (CHS.csnd d)                 top     = refl
  ᴬlem₂ (CHS.unit d)                 top     = refl
  ᴬlem₂ (CHS.mp i j d)               (pop k) = ᴬlem₂ d k
  ᴬlem₂ (CHS.ci d)                   (pop k) = ᴬlem₂ d k
  ᴬlem₂ (CHS.ck d)                   (pop k) = ᴬlem₂ d k
  ᴬlem₂ (CHS.cs d)                   (pop k) = ᴬlem₂ d k
  ᴬlem₂ (CHS.nec `d d)               (pop k) = ᴬlem₂ d k
  ᴬlem₂ (CHS.cdist d)                (pop k) = ᴬlem₂ d k
  ᴬlem₂ (CHS.cup d)                  (pop k) = ᴬlem₂ d k
  ᴬlem₂ (CHS.cdown d)                (pop k) = ᴬlem₂ d k
  ᴬlem₂ (CHS.cpair d)                (pop k) = ᴬlem₂ d k
  ᴬlem₂ (CHS.cfst d)                 (pop k) = ᴬlem₂ d k
  ᴬlem₂ (CHS.csnd d)                 (pop k) = ᴬlem₂ d k
  ᴬlem₂ (CHS.unit d)                 (pop k) = ᴬlem₂ d k

chs→ch : ∀ {A} → CHS.⊢ A → CH.⊢ chsᵀ→chᵀ A
chs→ch (Ξ , d) = chsᴰ→ch d top


-- Translation from closed Hilbert-style to closed Hilbert-style sequential.

chᴿ→chsᴿ : CH.Rep → ∃ (λ n → CHS.Rep (suc n))
chᴿ→chsᴿ (CH.APP r₁ r₂) with chᴿ→chsᴿ r₁ | chᴿ→chsᴿ r₂
chᴿ→chsᴿ (CH.APP r₁ r₂) | (n₁ , r₁′) | (n₂ , r₂′) = suc n₂ + suc n₁ , CHS.APP r₁′ r₂′
chᴿ→chsᴿ CH.CI          = zero , CHS.CI CHS.NIL
chᴿ→chsᴿ CH.CK          = zero , CHS.CK CHS.NIL
chᴿ→chsᴿ CH.CS          = zero , CHS.CS CHS.NIL
chᴿ→chsᴿ (CH.BOX r)     with chᴿ→chsᴿ r
chᴿ→chsᴿ (CH.BOX r)     | (n , r′) = zero , CHS.BOX r′
chᴿ→chsᴿ CH.CDIST       = zero , CHS.CDIST CHS.NIL
chᴿ→chsᴿ CH.CUP         = zero , CHS.CUP CHS.NIL
chᴿ→chsᴿ CH.CDOWN       = zero , CHS.CDOWN CHS.NIL
chᴿ→chsᴿ CH.CPAIR       = zero , CHS.CPAIR CHS.NIL
chᴿ→chsᴿ CH.CFST        = zero , CHS.CFST CHS.NIL
chᴿ→chsᴿ CH.CSND        = zero , CHS.CSND CHS.NIL
chᴿ→chsᴿ CH.UNIT        = zero , CHS.UNIT CHS.NIL

chᴾ→chsᴾ : CH.Proof → CHS.Proof
chᴾ→chsᴾ CH.[ r ] with chᴿ→chsᴿ r
chᴾ→chsᴾ CH.[ r ] | (n , r′) = CHS.[ r′ ]

chᵀ→chsᵀ : CH.Ty → CHS.Ty
chᵀ→chsᵀ = chᴾ→chsᴾ ↦ᵀ_

distᴺ⌊⌋+ : ∀ {U} → (Γ Γ′ : Cx U) → ᴺ⌊ Γ ⧺ Γ′ ⌋ ≡ ᴺ⌊ Γ ⌋ + ᴺ⌊ Γ′ ⌋
distᴺ⌊⌋+ Γ ∅        = refl
distᴺ⌊⌋+ Γ (Γ′ , A) = cong suc (distᴺ⌊⌋+ Γ Γ′)

mutual
  ch→chs : ∀ {A} → CH.⊢ A → CHS.⊢ chᵀ→chsᵀ A
  ch→chs (CH.app d₁ d₂) = CHS.app (ch→chs d₁) (ch→chs d₂)
  ch→chs CH.ci          = ∅ , CHS.ci CHS.nil
  ch→chs CH.ck          = ∅ , CHS.ck CHS.nil
  ch→chs CH.cs          = ∅ , CHS.cs CHS.nil
  ch→chs (CH.box d)     rewrite ᴮlem₁ d = CHS.box (ch→chs d)
  ch→chs CH.cdist       = ∅ , CHS.cdist CHS.nil
  ch→chs CH.cup         = ∅ , CHS.cup CHS.nil
  ch→chs CH.cdown       = ∅ , CHS.cdown CHS.nil
  ch→chs CH.cpair       = ∅ , CHS.cpair CHS.nil
  ch→chs CH.cfst        = ∅ , CHS.cfst CHS.nil
  ch→chs CH.csnd        = ∅ , CHS.csnd CHS.nil
  ch→chs CH.unit        = ∅ , CHS.unit CHS.nil

  -- FIXME: This should hold by ᴮlem₂.
  postulate
    ᴮlem₁ : ∀ {A} → (d : CH.⊢ A)
           → chᴿ→chsᴿ CH.ᴿ⌊ d ⌋ ≡ ᴺ⌊ π₁ (ch→chs d) ⌋ , CHS.ᴿ⌊ π₂ (ch→chs d) ⌋

  ᴮlem₂ : ∀ {A} → (d : CH.⊢ A)
         → ᴺ⌊ π₁ (ch→chs d) ⌋ ≡ π₁ (chᴿ→chsᴿ CH.ᴿ⌊ d ⌋)
  ᴮlem₂ (CH.app d₁ d₂) rewrite ᴮlem₂ d₂ | ᴮlem₃ d₁ d₂ = cong suc refl
  ᴮlem₂ CH.ci          = refl
  ᴮlem₂ CH.ck          = refl
  ᴮlem₂ CH.cs          = refl
  ᴮlem₂ (CH.box d)     rewrite ᴮlem₂ d | ᴮlem₁ d = refl
  ᴮlem₂ CH.cdist       = refl
  ᴮlem₂ CH.cup         = refl
  ᴮlem₂ CH.cdown       = refl
  ᴮlem₂ CH.cpair       = refl
  ᴮlem₂ CH.cfst        = refl
  ᴮlem₂ CH.csnd        = refl
  ᴮlem₂ CH.unit        = refl

  ᴮlem₃ : ∀ {A B} → (d₁ : CH.⊢ A CH.▻ B) → (d₂ : CH.⊢ A)
         → ᴺ⌊ (π₁ (ch→chs d₂) , chᵀ→chsᵀ A) ⧺ π₁ (ch→chs d₁) ⌋ ≡
            suc (π₁ (chᴿ→chsᴿ CH.ᴿ⌊ d₂ ⌋)) + π₁ (chᴿ→chsᴿ CH.ᴿ⌊ d₁ ⌋)
  ᴮlem₃ {A} d₁ d₂ rewrite distᴺ⌊⌋+ (π₁ (ch→chs d₂) , chᵀ→chsᵀ A) (π₁ (ch→chs d₁)) =
                  cong² _+_ (cong suc (ᴮlem₂ d₂)) (ᴮlem₂ d₁)
