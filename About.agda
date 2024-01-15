module About where

import Common


{- -------------------------------------------------------------------------------------------------

thanks to ames, dolio, drvink, mxu, ncf, ooovi, pgiarrusso, pounce, roconnor, tuplanolla

join ##dependent on libera.chat

- Abel (2013)
  “NbE: Dependent types and impredicativity”
  https://www.cse.chalmers.se/~abela/habil.pdf

- Coquand (2002)
  “A formalised proof of the soundness and completeness of a STLC with explicit substitutions”
  https://github.com/dpndnt/library/blob/master/doc/pdf/coquand-2002.pdf

- Jay-Ghani (1993)
  “The virtues of η-expansion”
  https://math.ucr.edu/home/baez/qg-winter2007/virtues.pdf

- Kovacs (2017)
  “A machine-checked correctness proof of NbE for STLC”
  https://github.com/dpndnt/library/blob/master/doc/pdf/kovacs-2017.pdf


------------------------------------------------------------------------------------------------- -}

import STLC-Base
import STLC-Base-Weak-NotEtaLong
import STLC-Base-Weak-NotEtaLong-NbE
import STLC-Base-Weak-EtaLong -- TODO: what to do about η-expansion?

import STLC-Negative
import STLC-Negative-Weak-NotEtaLong
import STLC-Negative-Weak-NotEtaLong-NbE

import STLC-Naturals
import STLC-Naturals-Weak-NotEtaLong
import STLC-Naturals-Weak-NotEtaLong-NbE -- TODO: interpret `ℕ per Abel p.10 §2.3


----------------------------------------------------------------------------------------------------

open STLC-Base-Weak-NotEtaLong-NbE

postulate
  -- Abel p.8: “preservation of meaning”
  lem₁ : ∀ {ℳ : Model} {W : World ℳ} {Γ A} (d : Γ ⊢ A) → ⟦ d ⟧ {ℳ} {W} ≡ ⟦ proj₁ (nbe d) ⟧

  -- Abel p.8: “idempotency”
  -- Kovacs p.59: “stability”
  lem₂ : ∀ {Γ A} (d : Γ ⊢ A) (p : NF d) → d ≡ proj₁ (nbe d)

  -- Abel p.8: “semantic equality”
  lem₃ : ∀ {ℳ : Model} {W : World ℳ} {Γ A} (d d′ : Γ ⊢ A) (eq : ⟦ d ⟧ {ℳ} {W} ≡ ⟦ d′ ⟧) →
         nbe d ≡ nbe d′

  -- Coquand p.68: “extensional equality on semantic objects”
  Eq : ∀ {ℳ : Model} {W : World ℳ} {A} (o o′ : ℳ ∣ W ⊩ A) → Set

  -- Coquand p.73
  thm₁ : ∀ {Γ A} {o o′ : 𝒞 ∣ Γ ⊩ A} (eq : Eq {A = A} o o′) → ↑ {A = A} o ≡ ↑ o′

  -- Coquand p.73
  cor₁ : ∀ {Γ A} (d d′ : Γ ⊢ A) (eq : Eq {A = A} (⟦ d ⟧ refl⊩*) (⟦ d′ ⟧ refl⊩*)) → nbe d ≡ nbe d′

  -- Abel p.10: “soundness of definitional equality”
  -- Coquand p.74
  -- Kovacs p.45: “completeness”
  thm₂ : ∀ {Γ A} (d : Γ ⊢ A) → d ≝ proj₁ (nbe d)

  -- Coquand p.75: “completeness of conversion rules”
  thm₃ : ∀ {Γ A} (d d′ : Γ ⊢ A) (eq : Eq {A = A} (⟦ d ⟧ refl⊩*) (⟦ d′ ⟧ refl⊩*)) → d ≝ d′

  -- Coquand p.76: “soundness of conversion rules”
  thm₄ : ∀ {ℳ : Model} {W : World ℳ} {Γ A} (d d′ : Γ ⊢ A) (eq : d ≝ d′) (os : ℳ ∣ W ⊩* Γ) →
         Eq {A = A} (⟦ d ⟧ os) (⟦ d′ ⟧ os)

  -- Coquand p.76: “correctness [soundness?] of decision algorithm for conversion”
  thm₅ : ∀ {Γ A} (d d′ : Γ ⊢ A) (eq : nbe d ≡ nbe d′) → d ≝ d′

  -- Abel p.10: “completeness of definitional equality”
  -- Coquand p.76: “completeness of decision algorithm for conversion”
  -- Kovacs p.52: “soundness”
  thm₆ : ∀ {Γ A} {d d′ : Γ ⊢ A} (eq : d ≝ d′) → nbe d ≡ nbe d′

-- Kovacs p.59: “decision procedure for conversion”
_≝?_ : ∀ {Γ A} (d d′ : Γ ⊢ A) → Dec (d ≝ d′)
d ≝? d′      with proj₁ (nbe d) ≟ proj₁ (nbe d′)
... | no ¬eq   = no λ eq → (proj₁ & thm₆ eq) ↯ ¬eq
... | yes eq   = yes $ begin
    d              ≝⟨ thm₂ d ⟩
    proj₁ (nbe d)  ≡⟨ eq ⟩
    proj₁ (nbe d′) ≝˘⟨ thm₂ d′ ⟩
    d′             ∎
  where open ≝-Reasoning


----------------------------------------------------------------------------------------------------
