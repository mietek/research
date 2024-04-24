{-# OPTIONS --rewriting #-}

module A201801.S4TTIsomorphismWithS4 where

open import A201801.Prelude
open import A201801.Fin
open import A201801.List
open import A201801.Vec
open import A201801.VecLemmas
open import A201801.S4TTTypes
open import A201801.S4TTTerms
open import A201801.S4TTDerivations
import A201801.S4StandardDerivations as S4


--------------------------------------------------------------------------------


infix 3 _⊢_⦂_match[_]_
data _⊢_⦂_match[_]_ : ∀ {d g} → (Δ : List Assert) → Term d g → (A : Type) (Γ : List Type)
                               → Δ S4.⊢ A valid[ Γ ] → Set
  where
    var : ∀ {A d g Δ Γ i} → (I : Fin g)
                          → Δ ⊢ VAR {d} (toFin i) ⦂ A match[ Γ ] S4.var i

    lam : ∀ {A B d g Δ Γ 𝒟} → {M : Term d (suc g)}
                            → Δ ⊢ M ⦂ B match[ Γ , A ] 𝒟
                            → Δ ⊢ LAM M ⦂ A ⊃ B match[ Γ ] S4.lam 𝒟

    app : ∀ {A B d g Δ Γ 𝒟 ℰ} → {M N : Term d g}
                              → Δ ⊢ M ⦂ A ⊃ B match[ Γ ] 𝒟 → Δ ⊢ N ⦂ A match[ Γ ] ℰ
                              → Δ ⊢ APP M N ⦂ B match[ Γ ] S4.app 𝒟 ℰ

    mvar : ∀ {A d g Δ Γ i} → (I : Fin d)
                           → Δ ⊢ MVAR {g = g} (toFin i) ⦂ A match[ Γ ] S4.mvar i

    box : ∀ {A d g Δ Γ 𝒟} → {M : Term d zero}
                          → Δ ⊢ M ⦂ A match[ ∙ ] 𝒟
                          → Δ ⊢ BOX {g = g} M ⦂ □ A match[ Γ ] S4.box 𝒟

    letbox : ∀ {A B d g Δ Γ 𝒟 ℰ} → {M : Term d g} {N : Term (suc d) g}
                                 → Δ ⊢ M ⦂ □ A match[ Γ ] 𝒟 → Δ , ⟪⊫ A ⟫ ⊢ N ⦂ B match[ Γ ] ℰ
                                 → Δ ⊢ LETBOX M N ⦂ B match[ Γ ] S4.letbox 𝒟 ℰ


--------------------------------------------------------------------------------


toTerm : ∀ {Δ Γ A} → Δ S4.⊢ A valid[ Γ ]
                   → Term (len Δ) (len Γ)
toTerm (S4.var i)      = VAR (toFin i)
toTerm (S4.lam 𝒟)      = LAM (toTerm 𝒟)
toTerm (S4.app 𝒟 ℰ)    = APP (toTerm 𝒟) (toTerm ℰ)
toTerm (S4.mvar i)     = MVAR (toFin i)
toTerm (S4.box 𝒟)      = BOX (toTerm 𝒟)
toTerm (S4.letbox 𝒟 ℰ) = LETBOX (toTerm 𝒟) (toTerm ℰ)


match-toTerm : ∀ {Δ Γ A} → (𝒟 : Δ S4.⊢ A valid[ Γ ])
                         → Δ ⊢ toTerm 𝒟 ⦂ A match[ Γ ] 𝒟
match-toTerm (S4.var i)      = var (toFin i)
match-toTerm (S4.lam 𝒟)      = lam (match-toTerm 𝒟)
match-toTerm (S4.app 𝒟 ℰ)    = app (match-toTerm 𝒟) (match-toTerm ℰ)
match-toTerm (S4.mvar i)     = mvar (toFin i)
match-toTerm (S4.box 𝒟)      = box (match-toTerm 𝒟)
match-toTerm (S4.letbox 𝒟 ℰ) = letbox (match-toTerm 𝒟) (match-toTerm ℰ)


--------------------------------------------------------------------------------


↓ : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
                → Δ ⊢ M ⦂ A valid[ Γ ]
                → toList Δ S4.⊢ A valid[ toList Γ ]
↓ (var i)      = S4.var (to∋ i)
↓ (lam 𝒟)      = S4.lam (↓ 𝒟)
↓ (app 𝒟 ℰ)    = S4.app (↓ 𝒟) (↓ ℰ)
↓ (mvar i)     = S4.mvar (to∋ i)
↓ (box 𝒟)      = S4.box (↓ 𝒟)
↓ (letbox 𝒟 ℰ) = S4.letbox (↓ 𝒟) (↓ ℰ)


-- TODO: something broke
-- match↓ : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
--                      → (𝒟 : Δ ⊢ M ⦂ A valid[ Γ ])
--                      → toList Δ ⊢ M ⦂ A match[ toList Γ ] ↓ 𝒟
-- match↓ (var {I = I} i)  = {!var I!}
-- match↓ (lam 𝒟)          = lam (match↓ 𝒟)
-- match↓ (app 𝒟 ℰ)        = app (match↓ 𝒟) (match↓ ℰ)
-- match↓ (mvar {I = I} i) = {!mvar I!}
-- match↓ (box 𝒟)          = box (match↓ 𝒟)
-- match↓ (letbox 𝒟 ℰ)     = letbox (match↓ 𝒟) (match↓ ℰ)


↑ : ∀ {Δ Γ M A} → (𝒟 : Δ S4.⊢ A valid[ Γ ]) {{p : Δ ⊢ M ⦂ A match[ Γ ] 𝒟}}
                → fromList Δ ⊢ M ⦂ A valid[ fromList Γ ]
↑ (S4.var i)      {{var I}}      = var (from∋ i)
↑ (S4.lam 𝒟)      {{lam p}}      = lam (↑ 𝒟 {{p}})
↑ (S4.app 𝒟 ℰ)    {{app p q}}    = app (↑ 𝒟 {{p}}) (↑ ℰ {{q}})
↑ (S4.mvar i)     {{mvar I}}     = mvar (from∋ i)
↑ (S4.box 𝒟)      {{box p}}      = box (↑ 𝒟 {{p}})
↑ (S4.letbox 𝒟 ℰ) {{letbox p q}} = letbox (↑ 𝒟 {{p}}) (↑ ℰ {{q}})


--------------------------------------------------------------------------------


gen-id↓↑ : ∀ {Δ Γ M A} → (𝒟 : Δ S4.⊢ A valid[ Γ ]) {{p : Δ ⊢ M ⦂ A match[ Γ ] 𝒟}}
                       → ↓ (↑ 𝒟 {{p}}) ≡ 𝒟
gen-id↓↑ (S4.var i)      {{var I}}      = refl
gen-id↓↑ (S4.lam 𝒟)      {{lam p}}      = S4.lam & gen-id↓↑ 𝒟 {{p}}
gen-id↓↑ (S4.app 𝒟 ℰ)    {{app p q}}    = S4.app & gen-id↓↑ 𝒟 {{p}} ⊗ gen-id↓↑ ℰ {{q}}
gen-id↓↑ (S4.mvar i)     {{mvar I}}     = refl
gen-id↓↑ (S4.box 𝒟)      {{box p}}      = S4.box & gen-id↓↑ 𝒟 {{p}}
gen-id↓↑ (S4.letbox 𝒟 ℰ) {{letbox p q}} = S4.letbox & gen-id↓↑ 𝒟 {{p}} ⊗ gen-id↓↑ ℰ {{q}}


-- TODO: something broke
-- id↓↑ : ∀ {Δ Γ A} → (𝒟 : Δ S4.⊢ A valid[ Γ ])
--                  → ↓ (↑ 𝒟) ≡ 𝒟
-- id↓↑ 𝒟 = gen-id↓↑ 𝒟 {{match-toTerm 𝒟}}


gen-id↑↓ : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
                       → (𝒟 : Δ ⊢ M ⦂ A valid[ Γ ]) {{p : toList Δ ⊢ M ⦂ A match[ toList Γ ] ↓ 𝒟}}
                       → ↑ (↓ 𝒟) {{p}} ≡ 𝒟
gen-id↑↓ (var i)      {{var I}}      = refl
gen-id↑↓ (lam 𝒟)      {{lam p}}      = lam & gen-id↑↓ 𝒟 {{p}}
gen-id↑↓ (app 𝒟 ℰ)    {{app p q}}    = app & gen-id↑↓ 𝒟 {{p}} ⊗ gen-id↑↓ ℰ {{q}}
gen-id↑↓ (mvar i)     {{mvar I}}     = refl
gen-id↑↓ (box 𝒟)      {{box p}}      = box & gen-id↑↓ 𝒟 {{p}}
gen-id↑↓ (letbox 𝒟 ℰ) {{letbox p q}} = letbox & gen-id↑↓ 𝒟 {{p}} ⊗ gen-id↑↓ ℰ {{q}}


-- TODO: something broke
-- id↑↓ : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
--                    → (𝒟 : Δ ⊢ M ⦂ A valid[ Γ ])
--                    → ↑ (↓ 𝒟) ≡ 𝒟
-- id↑↓ 𝒟 = gen-id↑↓ 𝒟 {{match↓ 𝒟}}


--------------------------------------------------------------------------------
