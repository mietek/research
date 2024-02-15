{- -------------------------------------------------------------------------------------------------

thanks to ames, dolio, drvink, mxu, ncf, ovi, pgiarrusso, pounce, rak, roconnor, tuplanolla

join ##dependent on libera.chat

- Abel (2013)
  “NbE: Dependent types and impredicativity”
  https://www.cse.chalmers.se/~abela/habil.pdf

- Altenkirch (1993)
  “Constructions, inductive types, and strong normalization”
  http://www.cs.nott.ac.uk/~psztxa/publ/phd93.pdf

- Coquand (2002)
  “A formalised proof of the soundness and completeness of a STLC with explicit substitutions”
  https://github.com/dpndnt/library/blob/master/doc/pdf/coquand-2002.pdf

- Ghani (1995)
  “Adjoint rewriting”
  https://www.cs.le.ac.uk/people/ng13/papers/yellowthesis.ps.gz

- Kovacs (2017)
  “A machine-checked correctness proof of NBE for STLC”
  https://github.com/dpndnt/library/blob/master/doc/pdf/kovacs-2017.pdf

- Schäfer (2019)
  “Engineering formal systems in constructive type theory”
  https://www.ps.uni-saarland.de/~schaefer/thesis/draft-screen.pdf


------------------------------------------------------------------------------------------------- -}

module About where

import Prelude
import GAN
import ARS
import DBI


----------------------------------------------------------------------------------------------------

-- main version, with order-preserving embeddings

import OPE
import OPE-GAN

import Kit1
import Kit2
import Kit2-GAN
import Kit3
import Kit3-GAN
import Kit4

import STLC-Base
import STLC-Base-RenSub
import STLC-Base-WNF
import STLC-Base-WNF-CBV
import STLC-Base-WNF-CBV-SN
import STLC-Base-WNF-CBV-SN2
import STLC-Base-WNF-NBE
import STLC-Base-WNF-NBE2
import STLC-Base-EWNF
import STLC-Base-EWNF-CBV
import STLC-Base-NF
import STLC-Base-NF-AO
import STLC-Base-NF-NDR
import STLC-Base-NF-NDPR

import STLC-Negative
import STLC-Negative-RenSub
import STLC-Negative-WNF
import STLC-Negative-WNF-CBV
import STLC-Negative-WNF-NBE
import STLC-Negative-WNF-NBE2

import STLC-Naturals
import STLC-Naturals-RenSub
import STLC-Naturals-SWNF
import STLC-Naturals-SWNF-CBV
import STLC-Naturals-SWNF-NBE
import STLC-Naturals-SWNF-NBE2
import STLC-Naturals-SWNF-NBE3
import STLC-Naturals-WNF
import STLC-Naturals-WNF-CBV
import STLC-Naturals-WNF-NBE
import STLC-Naturals2
import STLC-Naturals2-NF
import STLC-Naturals2-NF-NBE


----------------------------------------------------------------------------------------------------

-- alternative version, with first-order renamings

import FOR
import FOR-GAN

import FOR-Kit1
import FOR-Kit2
import FOR-Kit2-GAN
import FOR-Kit3
import FOR-Kit3-GAN

import FOR-STLC-Base
import FOR-STLC-Base-RenSub
import FOR-STLC-Base-WNF
import FOR-STLC-Base-WNF-CBV


----------------------------------------------------------------------------------------------------

-- alternative version, with higher-order renamings

import HOR


----------------------------------------------------------------------------------------------------

-- roadmap towards correctness of NBE

open STLC-Base-WNF-NBE2
open BetaShortEtaLongDefEq

postulate
  -- Abel p.8: “preservation of meaning”
  lem-1 : ∀ {ℳ : Model} {W : World ℳ} {Γ A} (t : Γ ⊢ A) → ⟦ t ⟧ {ℳ} {W} ≡ ⟦ fst (nbe t) ⟧

  -- Abel p.8: “idempotency”
  -- Kovacs p.59: “stability”
  lem-2 : ∀ {Γ A} (t : Γ ⊢ A) → NF t → t ≡ fst (nbe t)

  -- Abel p.8: “semantic equality”
  lem-3 : ∀ {ℳ : Model} {W : World ℳ} {Γ A} (t t′ : Γ ⊢ A) → ⟦ t ⟧ {ℳ} {W} ≡ ⟦ t′ ⟧ →
          nbe t ≡ nbe t′

-- Abel p.8: “βη-equivalence”; “definitional equality”
_≝′_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
_≝′_ = _≝_

postulate
  -- Abel p.8: “substitution is meaning-preserving”
  thm-i : ∀ {ℳ : Model} {W : World ℳ} {Γ A B} (t : A ∷ Γ ⊢ B) (s : Γ ⊢ A) (vs : ℳ / W ⊩§ Γ) →
          ⟦ t ⟧ (⟦ s ⟧ vs ∷ vs) ≡ ⟦ t [ s ] ⟧ vs

  -- completeness of definitional equality?
  thm-j : ∀ {ℳ : Model} {W : World ℳ} {Γ A} {t t′ : Γ ⊢ A} → ⟦ t ⟧ {ℳ} {W} ≡ ⟦ t′ ⟧ → t ≝ t′

  -- Abel p.10: “soundness of definitional equality”
  thm-k : ∀ {ℳ : Model} {W : World ℳ} {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → ⟦ t ⟧ {ℳ} {W} ≡ ⟦ t′ ⟧

  -- Coquand p.68: “extensional equality on semantic objects”
  Eq : ∀ {ℳ : Model} {W : World ℳ} A → ℳ / W ⊩ A → ℳ / W ⊩ A → Set

  -- Coquand p.73
  thm-1 : ∀ {Γ A} {v v′ : 𝒞 / Γ ⊩ A} → Eq A v v′ → ↓ {A} v ≡ ↓ v′

  -- Coquand p.73
  cor-1 : ∀ {Γ A} (t t′ : Γ ⊢ A) → Eq A (⟦ t ⟧ vids) (⟦ t′ ⟧ vids) → nbe t ≡ nbe t′

  -- Abel p.10: “soundness”, “normalization is compatible with definitional equality”
  -- Coquand p.74
  -- Kovacs p.45: “completeness”
  thm-2 : ∀ {Γ A} (t : Γ ⊢ A) → t ≝ fst (nbe t)

  -- Coquand p.75: “completeness of conversion rules”
  thm-3 : ∀ {Γ A} (t t′ : Γ ⊢ A) → Eq A (⟦ t ⟧ vids) (⟦ t′ ⟧ vids) → t ≝ t′

  -- Coquand p.76: “soundness of conversion rules”
  thm-4 : ∀ {ℳ : Model} {W : World ℳ} {Γ A} (t t′ : Γ ⊢ A) (vs : ℳ / W ⊩§ Γ) → t ≝ t′ →
         Eq A (⟦ t ⟧ vs) (⟦ t′ ⟧ vs)

  -- Coquand p.76: “correctness [soundness?] of decision algorithm for conversion”
  thm-5 : ∀ {Γ A} (t t′ : Γ ⊢ A) → nbe t ≡ nbe t′ → t ≝ t′

  lem-t : ∀ {Γ} → vids {Γ = Γ} ≡ vrens (refl≤ 𝒞) vids

-- -- Abel p.10: “completeness”, “definitionally equal terms have identical normal forms”
-- -- Coquand p.76: “completeness of decision algorithm for conversion”
-- -- Kovacs p.52: “soundness”
-- module _ where
--   open ≡-Reasoning

--   thm-6 : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → nbe t ≡ nbe t′
--   thm-6 refl≝             = refl
--   thm-6 (sym≝ deq)        with thm-k deq
--   ... | eq                  = (λ v → ↓ (v vids)) & eq ⁻¹
--   thm-6 (trans≝ deq deq′) with thm-k deq | thm-k deq′
--   ... | eq | eq′            = (λ v → ↓ (v vids)) & (eq ⋮ eq′)
--   thm-6 {Γ} (congλ deq)   with thm-k {ℳ = 𝒞} {W = Γ} deq -- TODO
--   ... | eq                  = {!!}
--   thm-6 (cong$ {t₁ = t₁} {t₁′} {t₂} {t₂′} deq₁ deq₂) with thm-k deq₁ | thm-k deq₂
--   ... | eq | eq′ = ↓ & (
--       begin
--         ⟦ t₁ ⟧ vids id⊑ (⟦ t₂ ⟧ vids)
--       ≡⟨ ⟦ t₁ ⟧ vids id⊑ & congapp eq′ vids ⟩
--         ⟦ t₁ ⟧ vids id⊑ (⟦ t₂′ ⟧ vids)
--       ≡⟨ congapp (congapp (congapp′ (congapp eq vids)) id⊑) (⟦ t₂′ ⟧ vids) ⟩
--         ⟦ t₁′ ⟧ vids id⊑ (⟦ t₂′ ⟧ vids)
--       ∎)
--   thm-6 (βred⊃ {t₁ = t₁} {t₂} refl) = ↓ & (
--       begin
--         ⟦ ⌜λ⌝ t₁ ⌜$⌝ t₂ ⟧ vids
--       ≡⟨⟩
--         ⟦ t₁ ⟧ (⟦ t₂ ⟧ vids ∷ vrens id⊑ vids)
--       ≡⟨ (λ vs → ⟦ t₁ ⟧ (⟦ t₂ ⟧ vids ∷ vs)) & lem-t ⁻¹ ⟩
--         ⟦ t₁ ⟧ (⟦ t₂ ⟧ vids ∷ vids)
--       ≡⟨ thm-i t₁ t₂ vids ⟩
--         ⟦ t₁ [ t₂ ] ⟧ vids
--       ∎)
--   thm-6 {Γ} (ηexp⊃ refl) = {!!} -- TODO

-- -- Kovacs p.59: “decision procedure for conversion”
-- module _ where
--   open ≝-Reasoning

--   _≝?_ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Dec (t ≝ t′)
--   t ≝? t′      with fst (nbe t) ≟ fst (nbe t′)
--   ... | no ¬eq   = no λ eq → (fst & thm-6 eq) ↯ ¬eq
--   ... | yes eq   = yes (
--       begin
--         t
--       ≝⟨ thm-2 t ⟩
--         fst (nbe t)
--       ≡⟨ eq ⟩
--         fst (nbe t′)
--       ≝˘⟨ thm-2 t′ ⟩
--         t′
--       ∎)


-- ----------------------------------------------------------------------------------------------------
