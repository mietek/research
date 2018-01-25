module IPLExperimentalDerivations1 where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import IPLPropositions
import IPLDerivations as IPL


--------------------------------------------------------------------------------


infix 3 _⊢_true
data _⊢_true : List Prop → Prop → Set
  where
    vz : ∀ {A Γ} → Γ , A ⊢ A true

    wk : ∀ {A B Γ} → Γ ⊢ A true
                   → Γ , B ⊢ A true

    lam : ∀ {A B Γ} → Γ , A ⊢ B true
                    → Γ ⊢ A ⊃ B true

    app : ∀ {A B Γ} → Γ ⊢ A ⊃ B true → Γ ⊢ A true
                    → Γ ⊢ B true


infix 3 _⊢_alltrue
_⊢_alltrue : List Prop → List Prop → Set
Γ ⊢ Ξ alltrue = All (Γ ⊢_true) Ξ


--------------------------------------------------------------------------------


wks : ∀ {A Γ Ξ} → Γ ⊢ Ξ alltrue
                → Γ , A ⊢ Ξ alltrue
wks ξ = maps wk ξ


lifts : ∀ {A Γ Ξ} → Γ ⊢ Ξ alltrue
                  → Γ , A ⊢ Ξ , A alltrue
lifts ξ = wks ξ , vz


vars : ∀ {Γ Γ′} → Γ′ ⊇ Γ
                → Γ′ ⊢ Γ alltrue
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {Γ} → Γ ⊢ Γ alltrue
ids = vars id


--------------------------------------------------------------------------------


sub : ∀ {Γ Ξ A} → Γ ⊢ Ξ alltrue → Ξ ⊢ A true
                → Γ ⊢ A true
sub (ξ , 𝒞) vz        = 𝒞
sub (ξ , 𝒞) (wk 𝒟)    = sub ξ 𝒟
sub ξ       (lam 𝒟)   = lam (sub (lifts ξ) 𝒟)
sub ξ       (app 𝒟 ℰ) = app (sub ξ 𝒟) (sub ξ ℰ)


--------------------------------------------------------------------------------


var : ∀ {Γ A} → Γ ∋ A
              → Γ ⊢ A true
var zero    = vz
var (suc i) = wk (var i)


ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A true
                 → Γ′ ⊢ A true
ren η 𝒟 = sub (vars η) 𝒟


--------------------------------------------------------------------------------


↓ : ∀ {Γ A} → Γ ⊢ A true
            → Γ IPL.⊢ A true
↓ vz        = IPL.vz
↓ (wk 𝒟)    = IPL.wk (↓ 𝒟)
↓ (lam 𝒟)   = IPL.lam (↓ 𝒟)
↓ (app 𝒟 ℰ) = IPL.app (↓ 𝒟) (↓ ℰ)


↑ : ∀ {Γ A} → Γ IPL.⊢ A true
            → Γ ⊢ A true
↑ (IPL.var i)   = var i
↑ (IPL.lam 𝒟)   = lam (↑ 𝒟)
↑ (IPL.app 𝒟 ℰ) = app (↑ 𝒟) (↑ ℰ)


lem-var : ∀ {Γ A} → (i : Γ ∋ A)
                    → ↓ (var i) ≡ IPL.var i
lem-var zero    = refl
lem-var (suc i) = IPL.wk & lem-var i
                ⋮ IPL.var ∘ suc & id-ren∋ i


id↓↑ : ∀ {Γ A} → (𝒟 : Γ IPL.⊢ A true)
               → (↓ ∘ ↑) 𝒟 ≡ 𝒟
id↓↑ (IPL.var i)   = lem-var i
id↓↑ (IPL.lam 𝒟)   = IPL.lam & id↓↑ 𝒟
id↓↑ (IPL.app 𝒟 ℰ) = IPL.app & id↓↑ 𝒟 ⊗ id↓↑ ℰ


-- NOTE: Problematic

-- id↑↓ : ∀ {Γ A} → (𝒟 : Γ ⊢ A true)
--                → (↑ ∘ ↓) 𝒟 ≡ 𝒟
-- id↑↓ vz        = refl
-- id↑↓ (wk 𝒟)    = {!!} -- ↑ (IPL.wk (↓ 𝒟)) ≡ wk 𝒟
-- id↑↓ (lam 𝒟)   = lam & id↑↓ 𝒟
-- id↑↓ (app 𝒟 ℰ) = app & id↑↓ 𝒟 ⊗ id↑↓ ℰ


-- TODO: Semantic equivalence


--------------------------------------------------------------------------------