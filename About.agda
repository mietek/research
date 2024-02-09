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
  “A machine-checked correctness proof of NbE for STLC”
  https://github.com/dpndnt/library/blob/master/doc/pdf/kovacs-2017.pdf

- Schäfer (2019)
  “Engineering formal systems in constructive type theory”
  https://www.ps.uni-saarland.de/~schaefer/thesis/draft-screen.pdf


------------------------------------------------------------------------------------------------- -}

module About where

import Prelude
import Category
import Isomorphism
import Common -- TODO: clean up
import Kit1 -- TODO!
import Kit2 -- TODO: less²
import Kit2-GAN -- TODO!
import Kit3 -- TODO: more Schäfer
import Kit4

import STLC-Base -- TODO
import STLC-Base-RenSub
import STLC-Base-WNF
import STLC-Base-WNF-CBV -- TODO
import STLC-Base-WNF-CBV-SN -- TODO
import STLC-Base-WNF-CBV-SN2 -- TODO
import STLC-Base-WNF-NbE
import STLC-Base-WNF-NbE2
import STLC-Base-EWNF
import STLC-Base-EWNF-CBV -- TODO

import STLC-Negative
import STLC-Negative-RenSub
import STLC-Negative-WNF
import STLC-Negative-WNF-CBV
import STLC-Negative-WNF-NbE
import STLC-Negative-WNF-NbE2

import STLC-Naturals
import STLC-Naturals-RenSub
import STLC-Naturals-SWNF
import STLC-Naturals-SWNF-CBV
import STLC-Naturals-SWNF-NbE
import STLC-Naturals-SWNF-NbE2
import STLC-Naturals-SWNF-NbE3
import STLC-Naturals-WNF
import STLC-Naturals-WNF-CBV
import STLC-Naturals-WNF-NbE
import STLC-Naturals2
import STLC-Naturals2-NF
import STLC-Naturals2-NF-NbE

-- TODO: use renamings for a STLC-Base alternative only
import Kit1-Renamings
import Kit2-Renamings
import Kit3-Renamings
import STLC-Naturals-Renamings
import STLC-Naturals-Renamings-Properties
-- import STLC-Naturals-Renamings-Weak-NotEtaLong


----------------------------------------------------------------------------------------------------

open STLC-Base-WNF-NbE2
open BetaShortEtaLongDefEq

postulate
  -- Abel p.8: “preservation of meaning”
  lem₁ : ∀ {ℳ : Model} {W : World ℳ} {Γ A} (t : Γ ⊢ A) → ⟦ t ⟧ {ℳ} {W} ≡ ⟦ fst (nbe t) ⟧

  -- Abel p.8: “idempotency”
  -- Kovacs p.59: “stability”
  lem₂ : ∀ {Γ A} (t : Γ ⊢ A) → NF t → t ≡ fst (nbe t)

  -- Abel p.8: “semantic equality”
  lem₃ : ∀ {ℳ : Model} {W : World ℳ} {Γ A} (t t′ : Γ ⊢ A) → ⟦ t ⟧ {ℳ} {W} ≡ ⟦ t′ ⟧ →
         nbe t ≡ nbe t′

-- Abel p.8: “βη-equivalence”; “definitional equality”
_≝′_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
_≝′_ = _≝_

postulate
  -- Abel p.8: “substitution is meaning-preserving”
  thmᵢ : ∀ {ℳ : Model} {W : World ℳ} {Γ A B} (t : A ∷ Γ ⊢ B) (s : Γ ⊢ A) (vs : ℳ / W ⊩* Γ)  →
         ⟦ t ⟧ (⟦ s ⟧ vs ∷ vs) ≡ ⟦ t [ s ] ⟧ vs

  -- completeness of definitional equality?
  thmⱼ : ∀ {ℳ : Model} {W : World ℳ} {Γ A} {t t′ : Γ ⊢ A} → ⟦ t ⟧ {ℳ} {W} ≡ ⟦ t′ ⟧ → t ≝ t′

  -- Abel p.10: “soundness of definitional equality”
  thmₖ : ∀ {ℳ : Model} {W : World ℳ} {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → ⟦ t ⟧ {ℳ} {W} ≡ ⟦ t′ ⟧

  -- Coquand p.68: “extensional equality on semantic objects”
  Eq : ∀ {ℳ : Model} {W : World ℳ} A → ℳ / W ⊩ A → ℳ / W ⊩ A → Set

  -- Coquand p.73
  thm₁ : ∀ {Γ A} {v v′ : 𝒞 / Γ ⊩ A} → Eq A v v′ → ↓ {A} v ≡ ↓ v′

  -- Coquand p.73
  cor₁ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Eq A (⟦ t ⟧ vids) (⟦ t′ ⟧ vids) → nbe t ≡ nbe t′

  -- Abel p.10: “soundness”, “normalization is compatible with definitional equality”
  -- Coquand p.74
  -- Kovacs p.45: “completeness”
  thm₂ : ∀ {Γ A} (t : Γ ⊢ A) → t ≝ fst (nbe t)

  -- Coquand p.75: “completeness of conversion rules”
  thm₃ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Eq A (⟦ t ⟧ vids) (⟦ t′ ⟧ vids) → t ≝ t′

  -- Coquand p.76: “soundness of conversion rules”
  thm₄ : ∀ {ℳ : Model} {W : World ℳ} {Γ A} (t t′ : Γ ⊢ A) (vs : ℳ / W ⊩* Γ) → t ≝ t′ →
         Eq A (⟦ t ⟧ vs) (⟦ t′ ⟧ vs)

  -- Coquand p.76: “correctness [soundness?] of decision algorithm for conversion”
  thm₅ : ∀ {Γ A} (t t′ : Γ ⊢ A) → nbe t ≡ nbe t′ → t ≝ t′

  lemᵢ : ∀ {Γ} → vids {Γ = Γ} ≡ vrens (refl≤ 𝒞) vids

-- -- Abel p.10: “completeness”, “definitionally equal terms have identical normal forms”
-- -- Coquand p.76: “completeness of decision algorithm for conversion”
-- -- Kovacs p.52: “soundness”
-- module _ where
--   open ≡-Reasoning

--   thm₆ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → nbe t ≡ nbe t′
--   thm₆     refl≝                       = refl
--   thm₆ {Γ} (sym≝ deq)                  with thmₖ {ℳ = 𝒞} {W = Γ} deq
--   ... | eq                               = cong (λ v → ↓ (v vids)) (sym eq)
--   thm₆ {Γ} (trans≝ deq deq′)           with thmₖ {ℳ = 𝒞} {W = Γ} deq | thmₖ {ℳ = 𝒞} {W = Γ} deq′
--   ... | eq | eq′                         = cong (λ v → ↓ (v vids)) (trans eq eq′)
--   thm₆ {Γ} (congλ deq)                 with thmₖ {ℳ = 𝒞} {W = Γ} deq
--   ... | eq                               = {!!}
--   thm₆ {Γ} (cong$ {t₁ = t₁} {t₁′} {t₂} {t₂′} deq₁ deq₂)
--     with thmₖ {ℳ = 𝒞} {W = Γ} deq₁ | thmₖ {ℳ = 𝒞} {W = Γ} deq₂
--   ... | eq | eq′ = cong ↓ $
--       begin
--         ⟦ t₁ ⟧ vids id⊆ (⟦ t₂ ⟧ vids)
--       ≡⟨ cong (⟦ t₁ ⟧ vids id⊆) (congapp eq′ vids) ⟩
--         ⟦ t₁ ⟧ vids id⊆ (⟦ t₂′ ⟧ vids)
--       ≡⟨ congapp (congapp (congapp′ (congapp eq vids) {Γ}) id⊆) (⟦ t₂′ ⟧ vids) ⟩
--         ⟦ t₁′ ⟧ vids id⊆ (⟦ t₂′ ⟧ vids)
--       ∎
--   thm₆ {Γ} (βred⊃ {t₁ = t₁} {t₂} refl) = cong ↓ $
--       begin
--         ⟦ ⌜λ⌝ t₁ ⌜$⌝ t₂ ⟧ vids
--       ≡⟨⟩
--         ⟦ t₁ ⟧ (⟦ t₂ ⟧ vids ∷ vrens id⊆ vids)
--       ≡⟨ cong (λ vs → ⟦ t₁ ⟧ (⟦ t₂ ⟧ vids ∷ vs)) (sym (lemᵢ {Γ})) ⟩
--         ⟦ t₁ ⟧ (⟦ t₂ ⟧ vids ∷ vids)
--       ≡⟨ thmᵢ {ℳ = 𝒞} {W = Γ} t₁ t₂ vids ⟩
--         ⟦ t₁ [ t₂ ] ⟧ vids
--       ∎
--   thm₆ {Γ} (ηexp⊃ refl) = {!!}

-- -- Kovacs p.59: “decision procedure for conversion”
-- module _ where
--   open ≝-Reasoning

--   _≝?_ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Dec (t ≝ t′)
--   t ≝? t′      with fst (nbe t) ≟ fst (nbe t′)
--   ... | no ¬eq   = no λ eq → cong fst (thm₆ eq) ↯ ¬eq
--   ... | yes eq   = yes $
--       begin
--         t
--       ≝⟨ thm₂ t ⟩
--         fst (nbe t)
--       ≡⟨ eq ⟩
--         fst (nbe t′)
--       ≝˘⟨ thm₂ t′ ⟩
--         t′
--       ∎


-- ----------------------------------------------------------------------------------------------------
