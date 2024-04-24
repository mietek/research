{-# OPTIONS --rewriting #-}

module A201801.STLCStandardIsomorphismWithIPL where

open import A201801.Prelude
open import A201801.Fin
open import A201801.List
open import A201801.Vec
open import A201801.VecLemmas
open import A201801.STLCTypes
open import A201801.STLCStandardTerms
open import A201801.STLCStandardDerivations
import A201801.IPLStandardDerivations as IPL


--------------------------------------------------------------------------------


infix 3 ⊢_⦂_match[_]_
data ⊢_⦂_match[_]_ : ∀ {g} → Term g → (A : Type) (Γ : List Type)
                            → Γ IPL.⊢ A true → Set
  where
    var : ∀ {A g Γ i} → (I : Fin g)
                      → ⊢ VAR (toFin i) ⦂ A match[ Γ ] IPL.var i

    lam : ∀ {A B g Γ 𝒟} → {M : Term (suc g)}
                        → ⊢ M ⦂ B match[ Γ , A ] 𝒟
                        → ⊢ LAM M ⦂ A ⊃ B match[ Γ ] IPL.lam 𝒟

    app : ∀ {A B g Γ 𝒟 ℰ} → {M N : Term g}
                          → ⊢ M ⦂ A ⊃ B match[ Γ ] 𝒟 → ⊢ N ⦂ A match[ Γ ] ℰ
                          → ⊢ APP M N ⦂ B match[ Γ ] IPL.app 𝒟 ℰ


--------------------------------------------------------------------------------


toTerm : ∀ {Γ A} → Γ IPL.⊢ A true
                 → Term (len Γ)
toTerm (IPL.var i)   = VAR (toFin i)
toTerm (IPL.lam 𝒟)   = LAM (toTerm 𝒟)
toTerm (IPL.app 𝒟 ℰ) = APP (toTerm 𝒟) (toTerm ℰ)


match-toTerm : ∀ {Γ A} → (𝒟 : Γ IPL.⊢ A true)
                       → ⊢ toTerm 𝒟 ⦂ A match[ Γ ] 𝒟
match-toTerm (IPL.var i)   = var (toFin i)
match-toTerm (IPL.lam 𝒟)   = lam (match-toTerm 𝒟)
match-toTerm (IPL.app 𝒟 ℰ) = app (match-toTerm 𝒟) (match-toTerm ℰ)


--------------------------------------------------------------------------------


↓ : ∀ {g M A} → {Γ : Types g}
              → ⊢ M ⦂ A valid[ Γ ]
              → toList Γ IPL.⊢ A true
↓ (var i)   = IPL.var (to∋ i)
↓ (lam 𝒟)   = IPL.lam (↓ 𝒟)
↓ (app 𝒟 ℰ) = IPL.app (↓ 𝒟) (↓ ℰ)


-- TODO: something broke
-- match↓ : ∀ {g M A} → {Γ : Types g}
--                    → (𝒟 : ⊢ M ⦂ A valid[ Γ ])
--                    → ⊢ M ⦂ A match[ toList Γ ] ↓ 𝒟
-- match↓ (var {I = I} i) = {!var I!}
-- match↓ (lam 𝒟)         = lam (match↓ 𝒟)
-- match↓ (app 𝒟 ℰ)       = app (match↓ 𝒟) (match↓ ℰ)


↑ : ∀ {Γ M A} → (𝒟 : Γ IPL.⊢ A true) {{p : ⊢ M ⦂ A match[ Γ ] 𝒟}}
              → ⊢ M ⦂ A valid[ fromList Γ ]
↑ (IPL.var i)   {{var I}}   = var (from∋ i)
↑ (IPL.lam 𝒟)   {{lam p}}   = lam (↑ 𝒟 {{p}})
↑ (IPL.app 𝒟 ℰ) {{app p q}} = app (↑ 𝒟 {{p}}) (↑ ℰ {{q}})


--------------------------------------------------------------------------------


gen-id↓↑ : ∀ {Γ M A} → (𝒟 : Γ IPL.⊢ A true) {{p : ⊢ M ⦂ A match[ Γ ] 𝒟}}
                     → ↓ (↑ 𝒟 {{p}}) ≡ 𝒟
gen-id↓↑ (IPL.var i)   {{var I}}   = refl
gen-id↓↑ (IPL.lam 𝒟)   {{lam p}}   = IPL.lam & gen-id↓↑ 𝒟 {{p}}
gen-id↓↑ (IPL.app 𝒟 ℰ) {{app p q}} = IPL.app & gen-id↓↑ 𝒟 {{p}} ⊗ gen-id↓↑ ℰ {{q}}


gen-id↑↓ : ∀ {g M A} → {Γ : Types g}
                     → (𝒟 : ⊢ M ⦂ A valid[ Γ ]) {{p : ⊢ M ⦂ A match[ toList Γ ] ↓ 𝒟}}
                     → ↑ (↓ 𝒟) {{p}} ≡ 𝒟
gen-id↑↓ (var i)   {{var I}}   = refl
gen-id↑↓ (lam 𝒟)   {{lam p}}   = lam & gen-id↑↓ 𝒟 {{p}}
gen-id↑↓ (app 𝒟 ℰ) {{app p q}} = app & gen-id↑↓ 𝒟 {{p}} ⊗ gen-id↑↓ ℰ {{q}}


--------------------------------------------------------------------------------


-- TODO: something broke
-- id↓↑ : ∀ {Γ A} → (𝒟 : Γ IPL.⊢ A true)
--                → ↓ (↑ 𝒟) ≡ 𝒟
-- id↓↑ 𝒟 = gen-id↓↑ 𝒟 {{match-toTerm 𝒟}}
--
--
-- id↑↓ : ∀ {g M A} → {Γ : Types g}
--                  → (𝒟 : ⊢ M ⦂ A valid[ Γ ])
--                  → ↑ (↓ 𝒟) ≡ 𝒟
-- id↑↓ 𝒟 = gen-id↑↓ 𝒟 {{match↓ 𝒟}}


--------------------------------------------------------------------------------
