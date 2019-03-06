---------------------------------------------------------------------------------------------------------------
--
-- Equivalence of SS-HAO and BS-HAO
--
--                     5.1
--      SS-CBV|SS-HAO₂ ← SS-HAO ⎫       SS-HAO      ⎫     SS-HAO
--  4.3.1 ↓      ↓ 4.5.2         ⎬ 4.5.4 ↓ × ↑ 4.5.5 ⎬ 4.5.6 ↕
--      BS-CBV|BS-HAO₂ → BS-HAO ⎭       BS-HAO      ⎭     BS-HAO
--                     5.3

module 4-5-Equivalence-HAO where

open import 1-2-Syntax-Predicates
import 1-3-Semantics-SmallStep as SS
import 1-4-Semantics-BigStep as BS
import 2-3-Properties-SmallStep-CBV as SS-CBV
import 2-5-1-Properties-SmallStep-HAO as SS-HAO
-- import 2-5-2-Properties-SmallStep-HAO₂ as SS-HAO₂
import 3-3-Properties-BigStep-CBV as BS-CBV
import 3-5-1-Properties-BigStep-HAO as BS-HAO
-- import 3-5-2-Properties-BigStep-HAO₂ as BS-HAO₂
import 4-3-Equivalence-CBV as CBV


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.5.1.  SS-HAO to NF implies SS-CBV to WNF followed by SS-HAO₂ to NF

module Lem-4-5-1 where
  open SS


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.5.2.  SS-HAO₂ to NF implies BS-HAO₂

module Lem-4-5-2 where
--  open SS-HAO₂
--  open BS-HAO₂


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.5.3.  BS-CBV followed by BS-HAO₂ implies BS-HAO

module Lem-4-5-3 where
  open BS


---------------------------------------------------------------------------------------------------------------
--
-- Corollary 4.5.4.  SS-HAO to NF implies BS-HAO

module Cor-4-5-4 where
  open SS-HAO
  open BS-HAO


---------------------------------------------------------------------------------------------------------------
--
-- Lemma 4.5.5.  BS-HAO implies SS-HAO

module Lem-4-5-5 where
  open SS-HAO
  open BS-HAO

--  cbv-app₁ : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ SS.CBV.⇒ e₁′ → NF e₂ → app e₁ e₂ ⇒ app e₁′ e₂
--  cbv-app₁ (SS.CBV.applam p₂)  p₂′ = {!_⇒_.app₁!}
--  cbv-app₁ (SS.CBV.app₁ r₁)    p₂′ = {!!}
--  cbv-app₁ (SS.CBV.app₂ p₁ r₂) p₂′ = {!!}

  lam* : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
  lam* = map lam

  applam* : ∀ {n} {e₁ : Tm (suc n)} {e₂ : Tm n} → NF e₂ → app (lam e₁) e₂ ⇒* e₁ [ e₂ ]
  applam* p₂ = applam p₂ ◅ ε

  app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → NAWNF e₁ → e₁ ⇒* e₁′ → NF e₂ → app e₁ e₂ ⇒* app e₁′ e₂
  app₁* p₁ ε          p₂ = ε
  app₁* p₁ (r₁ ◅ rs₁) p₂ = app₁ (na←nawnf p₁) r₁ p₂ ◅ app₁* (nawnf-⇒ p₁ r₁) rs₁ p₂

  app₂* : ∀ {n} {e₁ e₂ : Tm n} {e₂′} → e₂ ⇒* e₂′ → app e₁ e₂ ⇒* app e₁ e₂′
  app₂* = map app₂

--  cbv-app₁* : ∀ {n} {e₁ e₂ : Tm n} {e₁′} → e₁ SS.CBV.⇒* e₁′ → NF e₂ → app e₁ e₂ ⇒* app e₁′ e₂
--  cbv-app₁* ε                        p₂′ = ε
--  cbv-app₁* (SS.CBV.applam {e₂ = e₂} p₂ ◅ rs)  p₃′ with nf? e₂
--  ... | no ¬p₂ = {!!}
--  ... | yes p₂′ = app₁ app (applam p₂′) p₃′ ◅ cbv-app₁* rs p₃′
--  cbv-app₁* (SS.CBV.app₁ r₁ ◅ rs)    p₃′ = {!!} ◅◅ cbv-app₁* rs p₃′
--  cbv-app₁* (SS.CBV.app₂ p₁ r₂ ◅ rs) p₃′ = {!!} ◅◅ cbv-app₁* rs p₃′

  bs-lam : ∀ {n} {e : Tm (suc n)} {e′} → e ⇒* e′ → lam e ⇒* lam e′
  bs-lam = lam*

--  bs-applam : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₂′ e′} →
--              e₁ SS.CBV.⇒* lam e₁′ → WNF (lam e₁′) → e₂ ⇒* e₂′ → NF e₂′ → e₁′ [ e₂′ ] ⇒* e′ →
--              app e₁ e₂ ⇒* e′
--  bs-applam rs₁ lam      rs₂ p₂′ rs = {!!}
--  -- app₂* rs₂ ◅◅ cbv-app₁* rs₁ p₂′ ◅◅ applam* p₂′ ◅◅ rs
--  bs-applam rs₁ (wnf ()) rs₂ p₂′ rs
--
--  bs-app : ∀ {n} {e₁ e₂ : Tm n} {e₁′ e₁″ e₂′} →
--           e₁ SS.CBV.⇒* e₁′ → NAWNF e₁′ → e₁′ ⇒* e₁″ → NANF e₁″ → e₂ ⇒* e₂′ → NF e₂′ →
--           app e₁ e₂ ⇒* app e₁″ e₂′
--  bs-app rs₁ p₁′ rs₁′ p₁″ rs₂ p₂′ = {!!}
--  -- app₂* rs₂ ◅◅ cbv-app₁* rs₁ p₂′ ◅◅ app₁* p₁′ rs₁′ p₂′

  hao←cbv : ∀ {n} {e : Tm n} {e′} → e SS.CBV.⇒ e′ → e ⇒ e′
  hao←cbv (SS.CBV.applam p₂)  = applam {!!}
  hao←cbv (SS.CBV.app₁ r₁)    = app₁ {!!} (hao←cbv r₁) {!!}
  hao←cbv (SS.CBV.app₂ p₁ r₂) = app₂ (hao←cbv r₂)

  ss←bs : ∀ {n} {e : Tm n} {e′} → e ⇓ e′ → e ⇒* e′
  ss←bs var                 = ε
  ss←bs (lam r)             = bs-lam (ss←bs r)
  ss←bs (applam r₁ r₂ r)    = {!? ◅◅ applam* p₂′ ◅◅ rs!}
    where
      rs₁ = CBV.Lem-4-3-2.ss←bs r₁
      rs₂ = ss←bs r₂
      p₂′ = nf-⇓ r₂
      rs  = ss←bs r
  -- bs-applam (CBV.Lem-4-3-2.ss←bs r₁) lam (ss←bs r₂) (nf-⇓ r₂) (ss←bs r)
  ss←bs (app r₁ q₁′ r₁′ r₂) = {!!}
  -- bs-app (CBV.Lem-4-3-2.ss←bs r₁) p₁′ (ss←bs r₁′) p₁″ (ss←bs r₂) (nf-⇓ r₂)
    where
      p₁′ = nawnf←wnf (BS-CBV.wnf-⇓ r₁) q₁′
      p₁″ = nanf←nf (nf-⇓ r₁′) (na←wnf-⇓ (BS-CBV.wnf-⇓ r₁) q₁′ r₁′)


---------------------------------------------------------------------------------------------------------------
--
-- Theorem 4.5.6.  SS-HAO to NF and BS-HAO coincide

module Thm-4-5-6 where
--  ss-hao↔bs-hao : ∀ {n} {e : Tm n} {e′} → (e SS.HAO.⇒* e′ × NF e′) ↔ e BS.HAO.⇓ e′
--  ss-hao↔bs-hao = uncurry Cor-4-5-4.bs←ss , λ r → Lem-4-5-5.ss←bs r , BS-HAO.nf-⇓ r


---------------------------------------------------------------------------------------------------------------
