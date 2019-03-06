---------------------------------------------------------------------------------------------------------------
--
-- Equivalence of SS-HAO and BS-HAO
--
--                   5.1
--    SS-CBV|SS-HAO₂ ← SS-HAO ⎫     SS-HAO    ⎫   SS-HAO
--  3.1 ↓      ↓ 5.2           ⎬ 5.4 ↓ × ↑ 5.5 ⎬ 5.6 ↕
--    BS-CBV|BS-HAO₂ → BS-HAO ⎭     BS-HAO    ⎭   BS-HAO
--                   5.3

module Equivalence-HAO where

open import Syntax-Predicates
import Semantics-SmallStep as SS
import Semantics-BigStep as BS
import Properties-SmallStep-CBV as SS-CBV
import Properties-SmallStep-HAO as SS-HAO
-- import Properties-SmallStep-HAO₂ as SS-HAO₂
import Properties-BigStep-CBV as BS-CBV
import Properties-BigStep-HAO as BS-HAO
-- import Properties-BigStep-HAO₂ as BS-HAO₂
import Equivalence-CBV as CBV


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.1.  SS-HAO to NF implies SS-CBV to WNF followed by SS-HAO₂ to NF

module Lem-5-1 where
  open SS


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.2.  SS-HAO₂ to NF implies BS-HAO₂

module Lem-5-2 where
--  open SS-HAO₂
--  open BS-HAO₂


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.3.  BS-CBV followed by BS-HAO₂ implies BS-HAO

module Lem-5-3 where
  open BS


---------------------------------------------------------------------------------------------------------------
--
-- Corollary 5.4.  SS-HAO to NF implies BS-HAO

module Cor-5-4 where
  open SS-HAO
  open BS-HAO


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 5.5.  BS-HAO implies SS-HAO

module Lem-2-5 where

-- lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
-- lam* = map lam

-- applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → WNF e₁ → NF e₂ → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
-- applam* p₁ p₂ = applam p₁ p₂ ◅ ε

-- -- TODO

-- -- app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NA e₁ → e₁ ⇒* e₁′ → NF e₂ → app e₁ e₂ ⇒* app e₁′ e₂
-- -- app₁* p₁ rs p₂ = map (λ r₁ → app₁ {!!} r₁ p₂) rs

-- app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
-- app₂* = map app₂

  open SS-HAO
  open BS-HAO


---------------------------------------------------------------------------------------------------------------
--
-- Theorem 5.6.  SS-HAO to NF and BS-HAO coincide

module Thm-5-6 where
--  ss-hao↔bs-hao : ∀ {n} {e : Tm n} {e′} → (e SS.HAO.⇒* e′ × NF e′) ↔ e BS.HAO.⇓ e′
--  ss-hao↔bs-hao = uncurry Cor-5-4.bs←ss , λ r → Lem-5-5.ss←bs r , BS-HAO.nf-⇓ r


---------------------------------------------------------------------------------------------------------------
