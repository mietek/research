{-# OPTIONS --rewriting #-}

module A201801.IPLAlternativeDerivations where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.IPLPropositions
import A201801.IPLStandardDerivations as IPL
import A201801.IPLStandardDerivationsLemmas as IPL


--------------------------------------------------------------------------------


infix 3 _⊢_true
data _⊢_true : List Form → Form → Set
  where
    vz : ∀ {A Γ} → Γ , A ⊢ A true

    wk : ∀ {A B Γ} → Γ ⊢ A true
                   → Γ , B ⊢ A true

    cut : ∀ {A B Γ} → Γ ⊢ A true → Γ , A ⊢ B true
                    → Γ ⊢ B true

    lam : ∀ {A B Γ} → Γ , A ⊢ B true
                    → Γ ⊢ A ⊃ B true

    unlam : ∀ {A B Γ} → Γ ⊢ A ⊃ B true
                      → Γ , A ⊢ B true


infix 3 _⊢_alltrue
_⊢_alltrue : List Form → List Form → Set
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
sub ξ       (cut 𝒟 ℰ) = cut (sub ξ 𝒟) (sub (lifts ξ) ℰ)
sub ξ       (lam 𝒟)   = lam (sub (lifts ξ) 𝒟)
sub (ξ , 𝒞) (unlam 𝒟) = cut 𝒞 (unlam (sub ξ 𝒟))


--------------------------------------------------------------------------------


var : ∀ {Γ A} → Γ ∋ A
              → Γ ⊢ A true
var zero    = vz
var (suc i) = wk (var i)


app : ∀ {Γ A B} → Γ ⊢ A ⊃ B true → Γ ⊢ A true
                → Γ ⊢ B true
app 𝒟 ℰ = cut ℰ (unlam 𝒟)


-- NOTE: Local completeness of ⊃

relam : ∀ {Γ A B} → Γ ⊢ A ⊃ B true
                  → Γ ⊢ A ⊃ B true
relam 𝒟 = lam (unlam 𝒟)


-- NOTE: Local soundness of ⊃

pseudocut : ∀ {Γ A B} → Γ ⊢ A true → Γ , A ⊢ B true
                      → Γ ⊢ B true
pseudocut 𝒟 ℰ = app (lam ℰ) 𝒟


--------------------------------------------------------------------------------


↓ : ∀ {Γ A} → Γ ⊢ A true
            → Γ IPL.⊢ A true
↓ vz        = IPL.vz
↓ (wk 𝒟)    = IPL.wk (↓ 𝒟)
↓ (cut 𝒟 ℰ) = IPL.cut (↓ 𝒟) (↓ ℰ)
↓ (lam 𝒟)   = IPL.lam (↓ 𝒟)
↓ (unlam 𝒟) = IPL.unlam (↓ 𝒟)


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
id↓↑ (IPL.app 𝒟 ℰ) = IPL.app & ( IPL.id-cons-wk-sub IPL.ids (↓ (↑ ℰ)) (↓ (↑ 𝒟))
                               ⋮ IPL.id-sub (↓ (↑ 𝒟))
                               ⋮ id↓↑ 𝒟
                               )
                             ⊗ id↓↑ ℰ


-- NOTE: Problematic

-- id↑↓ : ∀ {Γ A} → (𝒟 : Γ ⊢ A true)
--                → (↑ ∘ ↓) 𝒟 ≡ 𝒟
-- id↑↓ vz        = refl
-- id↑↓ (wk 𝒟)    = {!!} -- ↑ (IPL.wk (↓ 𝒟)) ≡ wk 𝒟
-- id↑↓ (cut 𝒟 ℰ) = {!!} -- ↑ (IPL.cut (↓ 𝒟) (↓ ℰ)) ≡ cut 𝒟 ℰ
-- id↑↓ (lam 𝒟)   = lam & id↑↓ 𝒟
-- id↑↓ (unlam 𝒟) = {!!} -- app (↑ (IPL.wk (↓ 𝒟))) vz ≡ unlam 𝒟


-- TODO: Semantic equivalence


--------------------------------------------------------------------------------
