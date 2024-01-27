module About where


{- -------------------------------------------------------------------------------------------------

thanks to ames, dolio, drvink, mxu, ncf, ooovi, pgiarrusso, pounce, rak, roconnor, tuplanolla

join ##dependent on libera.chat

- Abel (2013)
  “NbE: Dependent types and impredicativity”
  https://www.cse.chalmers.se/~abela/habil.pdf

- Coquand (2002)
  “A formalised proof of the soundness and completeness of a STLC with explicit substitutions”
  https://github.com/dpndnt/library/blob/master/doc/pdf/coquand-2002.pdf

- Ghani (1995)
  “Adjoint rewriting”
  https://www.cs.le.ac.uk/people/ng13/papers/yellowthesis.ps.gz

- Kovacs (2017)
  “A machine-checked correctness proof of NbE for STLC”
  https://github.com/dpndnt/library/blob/master/doc/pdf/kovacs-2017.pdf


------------------------------------------------------------------------------------------------- -}

import Common
import Isomorphism

import STLC-Base
import STLC-Base-Weak-NotEtaLong
import STLC-Base-Weak-NotEtaLong-ConcreteNbE
import STLC-Base-Weak-NotEtaLong-AbstractNbE
import STLC-Base-Weak-EtaLong
import STLC-Base-Strong-EtaLong -- TODO

import STLC-Negative
import STLC-Negative-Weak-NotEtaLong
import STLC-Negative-Weak-NotEtaLong-ConcreteNbE
import STLC-Negative-Weak-NotEtaLong-AbstractNbE

import STLC-Naturals
import STLC-Naturals-Weak-NotEtaLong
import STLC-Naturals-Weak-NotEtaLong-ConcreteNbE -- TODO
import STLC-Naturals-Weak-NotEtaLong-AbstractNbE -- TODO
import STLC-Naturals2
import STLC-Naturals2-Strong-EtaLong
import STLC-Naturals2-Strong-EtaLong-ConcreteNBE


----------------------------------------------------------------------------------------------------

open STLC-Base-Weak-NotEtaLong-AbstractNbE

postulate
  -- Abel p.8: “preservation of meaning”
  lem₁ : ∀ {ℳ : Model} {W : World ℳ} {Γ A} (t : Γ ⊢ A) → ⟦ t ⟧ {ℳ} {W} ≡ ⟦ proj₁ (nbe t) ⟧

  -- Abel p.8: “idempotency”
  -- Kovacs p.59: “stability”
  lem₂ : ∀ {Γ A} (t : Γ ⊢ A) → NF t → t ≡ proj₁ (nbe t)

  -- Abel p.8: “semantic equality”
  lem₃ : ∀ {ℳ : Model} {W : World ℳ} {Γ A} (t t′ : Γ ⊢ A) → ⟦ t ⟧ {ℳ} {W} ≡ ⟦ t′ ⟧ →
         nbe t ≡ nbe t′

-- Abel p.8: “βη-equivalence”; “definitional equality”
_≝′_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
_≝′_ = _≝_

postulate
  -- Abel p.8: “substitution is meaning-preserving”
  thmᵢ : ∀ {ℳ : Model} {W : World ℳ} {Γ A B} (t : A ∷ Γ ⊢ B) (s : Γ ⊢ A) (os : ℳ / W ⊩* Γ)  →
         ⟦ t ⟧ (⟦ s ⟧ os ∷ os) ≡ ⟦ t [ s ] ⟧ os

  -- completeness of definitional equality?
  thmⱼ : ∀ {ℳ : Model} {W : World ℳ} {Γ A} {t t′ : Γ ⊢ A} → ⟦ t ⟧ {ℳ} {W} ≡ ⟦ t′ ⟧ → t ≝ t′

  -- Abel p.10: “soundness of definitional equality”
  thmₖ : ∀ {ℳ : Model} {W : World ℳ} {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → ⟦ t ⟧ {ℳ} {W} ≡ ⟦ t′ ⟧

  -- Coquand p.68: “extensional equality on semantic objects”
  Eq : ∀ {ℳ : Model} {W : World ℳ} {A} → ℳ / W ⊩ A → ℳ / W ⊩ A → Set

  -- Coquand p.73
  thm₁ : ∀ {Γ A} {o o′ : 𝒞 / Γ ⊩ A} → Eq {A = A} o o′ → ↓ {A = A} o ≡ ↓ o′

  -- Coquand p.73
  cor₁ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Eq {A = A} (⟦ t ⟧ refl⊩*) (⟦ t′ ⟧ refl⊩*) → nbe t ≡ nbe t′

  -- Abel p.10: “soundness”, “normalization is compatible with definitional equality”
  -- Coquand p.74
  -- Kovacs p.45: “completeness”
  thm₂ : ∀ {Γ A} (t : Γ ⊢ A) → t ≝ proj₁ (nbe t)

  -- Coquand p.75: “completeness of conversion rules”
  thm₃ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Eq {A = A} (⟦ t ⟧ refl⊩*) (⟦ t′ ⟧ refl⊩*) → t ≝ t′

  -- Coquand p.76: “soundness of conversion rules”
  thm₄ : ∀ {ℳ : Model} {W : World ℳ} {Γ A} (t t′ : Γ ⊢ A) (os : ℳ / W ⊩* Γ) → t ≝ t′ →
         Eq {A = A} (⟦ t ⟧ os) (⟦ t′ ⟧ os)

  -- Coquand p.76: “correctness [soundness?] of decision algorithm for conversion”
  thm₅ : ∀ {Γ A} (t t′ : Γ ⊢ A) → nbe t ≡ nbe t′ → t ≝ t′

  lemᵢ : ∀ {Γ} → refl⊩* {Γ = Γ} ≡ ren⊩* (refl≤ 𝒞) refl⊩*

-- Abel p.10: “completeness”, “definitionally equal terms have identical normal forms”
-- Coquand p.76: “completeness of decision algorithm for conversion”
-- Kovacs p.52: “soundness”
module _ where
  open ≡-Reasoning

  thm₆ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → nbe t ≡ nbe t′
  thm₆     refl≝                       = refl
  thm₆ {Γ} (sym≝ deq)                  with thmₖ {ℳ = 𝒞} {W = Γ} deq
  ... | eq                               = cong (λ o → ↓ (o refl⊩*)) (sym eq)
  thm₆ {Γ} (trans≝ deq deq′)           with thmₖ {ℳ = 𝒞} {W = Γ} deq | thmₖ {ℳ = 𝒞} {W = Γ} deq′
  ... | eq | eq′                         = cong (λ o → ↓ (o refl⊩*)) (trans eq eq′)
  thm₆ {Γ} (cong$ {t₁ = t₁} {t₁′} {t₂} {t₂′} deq₁ deq₂)
    with thmₖ {ℳ = 𝒞} {W = Γ} deq₁ | thmₖ {ℳ = 𝒞} {W = Γ} deq₂
  ... | eq | eq′ = cong ↓ $
    begin
      ⟦ t₁ ⟧ refl⊩* refl⊆ (⟦ t₂ ⟧ refl⊩*)
    ≡⟨ cong (⟦ t₁ ⟧ refl⊩* refl⊆) (cong-app eq′ refl⊩*) ⟩
      ⟦ t₁ ⟧ refl⊩* refl⊆ (⟦ t₂′ ⟧ refl⊩*)
    ≡⟨ cong-app (cong-app (cong-app′ (cong-app eq refl⊩*) {Γ}) refl⊆) (⟦ t₂′ ⟧ refl⊩*) ⟩
      ⟦ t₁′ ⟧ refl⊩* refl⊆ (⟦ t₂′ ⟧ refl⊩*)
    ∎
  thm₆ {Γ} (βred⊃ {t₁ = t₁} {t₂} refl) = cong ↓ $
    begin
      ⟦ ⌜λ⌝ t₁ ⌜$⌝ t₂ ⟧ refl⊩*
    ≡⟨⟩
      ⟦ t₁ ⟧ (⟦ t₂ ⟧ refl⊩* ∷ ren⊩* refl⊆ refl⊩*)
    ≡⟨ cong (λ os → ⟦ t₁ ⟧ (⟦ t₂ ⟧ refl⊩* ∷ os)) (sym (lemᵢ {Γ})) ⟩
      ⟦ t₁ ⟧ (⟦ t₂ ⟧ refl⊩* ∷ refl⊩*)
    ≡⟨ thmᵢ {ℳ = 𝒞} {W = Γ} t₁ t₂ refl⊩* ⟩
      ⟦ t₁ [ t₂ ] ⟧ refl⊩*
    ∎

-- Kovacs p.59: “decision procedure for conversion”
module _ where
  open ≝-Reasoning

  _≝?_ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Dec (t ≝ t′)
  t ≝? t′      with proj₁ (nbe t) ≟ proj₁ (nbe t′)
  ... | no ¬eq   = no λ eq → cong proj₁ (thm₆ eq) ↯ ¬eq
  ... | yes eq   = yes $
    begin
      t
    ≝⟨ thm₂ t ⟩
      proj₁ (nbe t)
    ≡⟨ eq ⟩
      proj₁ (nbe t′)
    ≝˘⟨ thm₂ t′ ⟩
      t′
    ∎


----------------------------------------------------------------------------------------------------
