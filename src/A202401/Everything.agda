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

module A202401.Everything where

import A202401.Prelude
import A202401.GAN
import A202401.DBI


----------------------------------------------------------------------------------------------------

-- main version, with order-preserving embeddings

import A202401.OPE
import A202401.OPE-GAN

import A202401.Kit1
import A202401.Kit2
import A202401.Kit2-GAN
import A202401.Kit3
import A202401.Kit3-GAN
import A202401.Kit4

import A202401.STLC-Base
import A202401.STLC-Base-RenSub
import A202401.STLC-Base-WNF
import A202401.STLC-Base-WNF-CBV
import A202401.STLC-Base-WNF-CBV-SN
import A202401.STLC-Base-WNF-CBV-SN2
import A202401.STLC-Base-WNF-NBE
import A202401.STLC-Base-WNF-NBE2
import A202401.STLC-Base-EWNF
import A202401.STLC-Base-EWNF-CBV
import A202401.STLC-Base-NF
import A202401.STLC-Base-NF-AO
import A202401.STLC-Base-NF-NDR
import A202401.STLC-Base-NF-NDPR

import A202401.STLC-Negative
import A202401.STLC-Negative-RenSub
import A202401.STLC-Negative-WNF
import A202401.STLC-Negative-WNF-CBV
import A202401.STLC-Negative-WNF-NBE
import A202401.STLC-Negative-WNF-NBE2

import A202401.STLC-Naturals
import A202401.STLC-Naturals-RenSub
import A202401.STLC-Naturals-SWNF
import A202401.STLC-Naturals-SWNF-CBV
import A202401.STLC-Naturals-SWNF-NBE
import A202401.STLC-Naturals-SWNF-NBE2
import A202401.STLC-Naturals-SWNF-NBE3
import A202401.STLC-Naturals-WNF
import A202401.STLC-Naturals-WNF-CBV
import A202401.STLC-Naturals-WNF-NBE
import A202401.STLC-Naturals2
import A202401.STLC-Naturals2-NF
import A202401.STLC-Naturals2-NF-NBE


----------------------------------------------------------------------------------------------------

-- alternative version, with first-order renamings

import A202401.FOR
import A202401.FOR-GAN

import A202401.FOR-Kit1
import A202401.FOR-Kit2
import A202401.FOR-Kit2-GAN
import A202401.FOR-Kit3
import A202401.FOR-Kit3-GAN

import A202401.FOR-STLC-Base
import A202401.FOR-STLC-Base-RenSub
import A202401.FOR-STLC-Base-WNF
import A202401.FOR-STLC-Base-WNF-CBV


----------------------------------------------------------------------------------------------------

-- alternative version, with higher-order renamings

import A202401.HOR


----------------------------------------------------------------------------------------------------

-- roadmap towards correctness of NBE

open A202401.STLC-Base-WNF-NBE2
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
  thm-i : ∀ {ℳ : Model} {W : World ℳ} {Γ A B} (t : Γ , A ⊢ B) (s : Γ ⊢ A) (γ : ℳ / W ⊩§ Γ) →
          ⟦ t ⟧ (γ , ⟦ s ⟧ γ) ≡ ⟦ t [ s ] ⟧ γ

  -- completeness of definitional equality?
  thm-j : ∀ {ℳ : Model} {W : World ℳ} {Γ A} {t t′ : Γ ⊢ A} → ⟦ t ⟧ {ℳ} {W} ≡ ⟦ t′ ⟧ → t ≝ t′

  -- Abel p.10: “soundness of definitional equality”
  thm-k : ∀ {ℳ : Model} {W : World ℳ} {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → ⟦ t ⟧ {ℳ} {W} ≡ ⟦ t′ ⟧

  -- Coquand p.68: “extensional equality on semantic objects”
  Eq : ∀ {ℳ : Model} {W : World ℳ} A → ℳ / W ⊩ A → ℳ / W ⊩ A → Set

  -- Coquand p.73
  thm-1 : ∀ {Γ A} {v v′ : 𝒞 / Γ ⊩ A} → Eq A v v′ → ↓ {A} v ≡ ↓ v′

  -- Coquand p.73
  cor-1 : ∀ {Γ A} (t t′ : Γ ⊢ A) → Eq A (⟦ t ⟧ vid§) (⟦ t′ ⟧ vid§) → nbe t ≡ nbe t′

  -- Abel p.10: “soundness”, “normalization is compatible with definitional equality”
  -- Coquand p.74
  -- Kovacs p.45: “completeness”
  thm-2 : ∀ {Γ A} (t : Γ ⊢ A) → t ≝ fst (nbe t)

  -- Coquand p.75: “completeness of conversion rules”
  thm-3 : ∀ {Γ A} (t t′ : Γ ⊢ A) → Eq A (⟦ t ⟧ vid§) (⟦ t′ ⟧ vid§) → t ≝ t′

  -- Coquand p.76: “soundness of conversion rules”
  thm-4 : ∀ {ℳ : Model} {W : World ℳ} {Γ A} (t t′ : Γ ⊢ A) (γ : ℳ / W ⊩§ Γ) → t ≝ t′ →
         Eq A (⟦ t ⟧ γ) (⟦ t′ ⟧ γ)

  -- Coquand p.76: “correctness [soundness?] of decision algorithm for conversion”
  thm-5 : ∀ {Γ A} (t t′ : Γ ⊢ A) → nbe t ≡ nbe t′ → t ≝ t′

  lem-t : ∀ {Γ} → vid§ {Γ = Γ} ≡ vren§ (refl≤ 𝒞) vid§

-- -- Abel p.10: “completeness”, “definitionally equal terms have identical normal forms”
-- -- Coquand p.76: “completeness of decision algorithm for conversion”
-- -- Kovacs p.52: “soundness”
-- module _ where
--   open ≡-Reasoning

--   thm-6 : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → nbe t ≡ nbe t′
--   thm-6 refl≝             = refl
--   thm-6 (sym≝ deq)        with thm-k deq
--   ... | eq                  = (λ v → ↓ (v vid§)) & eq ⁻¹
--   thm-6 (trans≝ deq deq′) with thm-k deq | thm-k deq′
--   ... | eq | eq′            = (λ v → ↓ (v vid§)) & (eq ⋮ eq′)
--   thm-6 {Γ} (congλ deq)   with thm-k {ℳ = 𝒞} {W = Γ} deq -- TODO
--   ... | eq                  = {!!}
--   thm-6 (cong$ {t₁ = t₁} {t₁′} {t₂} {t₂′} deq₁ deq₂) with thm-k deq₁ | thm-k deq₂
--   ... | eq | eq′ = ↓ & (
--       begin
--         ⟦ t₁ ⟧ vid§ id⊑ (⟦ t₂ ⟧ vid§)
--       ≡⟨ ⟦ t₁ ⟧ vid§ id⊑ & congapp eq′ vid§ ⟩
--         ⟦ t₁ ⟧ vid§ id⊑ (⟦ t₂′ ⟧ vid§)
--       ≡⟨ congapp (congapp (congapp′ (congapp eq vid§)) id⊑) (⟦ t₂′ ⟧ vid§) ⟩
--         ⟦ t₁′ ⟧ vid§ id⊑ (⟦ t₂′ ⟧ vid§)
--       ∎)
--   thm-6 (βred⊃ {t₁ = t₁} {t₂} refl) = ↓ & (
--       begin
--         ⟦ ⌜λ⌝ t₁ ⌜$⌝ t₂ ⟧ vid§
--       ≡⟨⟩
--         ⟦ t₁ ⟧ (vren§ id⊑ vid§ , ⟦ t₂ ⟧ vid§)
--       ≡⟨ (λ γ → ⟦ t₁ ⟧ (γ , ⟦ t₂ ⟧ vid§)) & lem-t ⁻¹ ⟩
--         ⟦ t₁ ⟧ (vid§ , ⟦ t₂ ⟧ vid§)
--       ≡⟨ thm-i t₁ t₂ vid§ ⟩
--         ⟦ t₁ [ t₂ ] ⟧ vid§
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
