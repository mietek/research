{-# OPTIONS --rewriting #-}

module STLCIsomorphismWithIPL where

open import Prelude
open import Fin
open import List
open import Vec
open import VecLemmas
open import STLCTypes
open import STLCTerms
open import STLCDerivations
import IPLDerivations as IPL


--------------------------------------------------------------------------------


data _⌊≡⌋_ : ∀ {g Γ A} → Term g → Γ IPL.⊢ A true → Set
  where
    var : ∀ {g Γ A} → {I : Fin g} {i : Γ ∋ A}
                    → VAR (toFin i) ⌊≡⌋ IPL.var i

    lam : ∀ {g Γ A B} → {M : Term (suc g)} {𝒟 : Γ , A IPL.⊢ B true}
                      → M ⌊≡⌋ 𝒟
                      → LAM M ⌊≡⌋ IPL.lam 𝒟

    app : ∀ {g Γ A B} → {M N : Term g} {𝒟 : Γ IPL.⊢ A ⊃ B true} {ℰ : Γ IPL.⊢ A true}
                      → M ⌊≡⌋ 𝒟 → N ⌊≡⌋ ℰ
                      → APP M N ⌊≡⌋ IPL.app 𝒟 ℰ


toTerm : ∀ {Γ A} → Γ IPL.⊢ A true
                 → Term (len Γ)
toTerm (IPL.var i)   = VAR (toFin i)
toTerm (IPL.lam 𝒟)   = LAM (toTerm 𝒟)
toTerm (IPL.app 𝒟 ℰ) = APP (toTerm 𝒟) (toTerm ℰ)


instance
  ⌊id⌋-toTerm : ∀ {Γ A} → (𝒟 : Γ IPL.⊢ A true)
                        → toTerm 𝒟 ⌊≡⌋ 𝒟
  ⌊id⌋-toTerm (IPL.var i)   = var {I = toFin i}
  ⌊id⌋-toTerm (IPL.lam 𝒟)   = lam (⌊id⌋-toTerm 𝒟)
  ⌊id⌋-toTerm (IPL.app 𝒟 ℰ) = app (⌊id⌋-toTerm 𝒟) (⌊id⌋-toTerm ℰ)


--------------------------------------------------------------------------------


↓ : ∀ {g M A} → {Γ : Types g}
              → ⊢ M ⦂ A valid[ Γ ]
              → toList Γ IPL.⊢ A true
↓ (var i)   = IPL.var (to∋ i)
↓ (lam 𝒟)   = IPL.lam (↓ 𝒟)
↓ (app 𝒟 ℰ) = IPL.app (↓ 𝒟) (↓ ℰ)


instance
  ⌊map⌋-↓ : ∀ {g M A} → {Γ : Types g}
                      → (𝒟 : ⊢ M ⦂ A valid[ Γ ])
                      → M ⌊≡⌋ ↓ 𝒟
  ⌊map⌋-↓ (var {I = I} i) = var {I = I}
  ⌊map⌋-↓ (lam 𝒟)         = lam (⌊map⌋-↓ 𝒟)
  ⌊map⌋-↓ (app 𝒟 ℰ)       = app (⌊map⌋-↓ 𝒟) (⌊map⌋-↓ ℰ)


↑ : ∀ {Γ M A} → (𝒟 : Γ IPL.⊢ A true) {{p : M ⌊≡⌋ 𝒟}}
              → ⊢ M ⦂ A valid[ fromList Γ ]
↑ (IPL.var i)   {{var}}     = var (from∋ i)
↑ (IPL.lam 𝒟)   {{lam p}}   = lam (↑ 𝒟 {{p}})
↑ (IPL.app 𝒟 ℰ) {{app p q}} = app (↑ 𝒟 {{p}}) (↑ ℰ {{q}})


--------------------------------------------------------------------------------


{-# REWRITE id-to∋-from∋ #-}
gen-id↓↑ : ∀ {Γ M A} → (𝒟 : Γ IPL.⊢ A true) {{p : M ⌊≡⌋ 𝒟}}
                     → ↓ (↑ 𝒟 {{p}}) ≡ 𝒟
gen-id↓↑ (IPL.var i)   {{var}}     = refl
gen-id↓↑ (IPL.lam 𝒟)   {{lam p}}   = IPL.lam & gen-id↓↑ 𝒟 {{p}}
gen-id↓↑ (IPL.app 𝒟 ℰ) {{app p q}} = IPL.app & gen-id↓↑ 𝒟 {{p}} ⊗ gen-id↓↑ ℰ {{q}}


id↓↑ : ∀ {Γ A} → (𝒟 : Γ IPL.⊢ A true)
               → ↓ (↑ 𝒟) ≡ 𝒟
id↓↑ 𝒟 = gen-id↓↑ 𝒟 {{⌊id⌋-toTerm 𝒟}}


{-# REWRITE id-from∋-to∋ #-}
gen-id↑↓ : ∀ {g M A} → {Γ : Types g}
                     → (𝒟 : ⊢ M ⦂ A valid[ Γ ]) {{p : M ⌊≡⌋ ↓ 𝒟}}
                     → ↑ (↓ 𝒟) {{p}} ≡ 𝒟
gen-id↑↓ (var i)   {{var}}     = refl
gen-id↑↓ (lam 𝒟)   {{lam p}}   = lam & gen-id↑↓ 𝒟 {{p}}
gen-id↑↓ (app 𝒟 ℰ) {{app p q}} = app & gen-id↑↓ 𝒟 {{p}} ⊗ gen-id↑↓ ℰ {{q}}


id↑↓ : ∀ {g M A} → {Γ : Types g}
                 → (𝒟 : ⊢ M ⦂ A valid[ Γ ])
                 → ↑ (↓ 𝒟) ≡ 𝒟
id↑↓ 𝒟 = gen-id↑↓ 𝒟


--------------------------------------------------------------------------------
