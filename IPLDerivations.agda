module IPLDerivations where

open import Prelude
open import Category
open import List
open import ListLemmas
open import ListConcatenation
open import AllList
open import IPLPropositions


--------------------------------------------------------------------------------


infix 3 _⊢_true
data _⊢_true : List Prop → Prop → Set
  where
    var : ∀ {A Γ} → Γ ∋ A
                  → Γ ⊢ A true

    lam : ∀ {A B Γ} → Γ , A ⊢ B true
                    → Γ ⊢ A ⊃ B true

    app : ∀ {A B Γ} → Γ ⊢ A ⊃ B true → Γ ⊢ A true
                    → Γ ⊢ B true


infix 3 _⊢_alltrue
_⊢_alltrue : List Prop → List Prop → Set
Γ ⊢ Ξ alltrue = All (Γ ⊢_true) Ξ


--------------------------------------------------------------------------------


ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A true
                 → Γ′ ⊢ A true
ren η (var i)   = var (ren∋ η i)
ren η (lam 𝒟)   = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ) = app (ren η 𝒟) (ren η ℰ)


rens : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢ Ξ alltrue
                  → Γ′ ⊢ Ξ alltrue
rens η ξ = maps (ren η) ξ


--------------------------------------------------------------------------------


wk : ∀ {B Γ A} → Γ ⊢ A true
               → Γ , B ⊢ A true
wk 𝒟 = ren (drop id) 𝒟


wks : ∀ {A Γ Ξ} → Γ ⊢ Ξ alltrue
                → Γ , A ⊢ Ξ alltrue
wks ξ = rens (drop id) ξ


vz : ∀ {Γ A} → Γ , A ⊢ A true
vz = var zero


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
sub ξ (var i)   = get ξ i
sub ξ (lam 𝒟)   = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ) = app (sub ξ 𝒟) (sub ξ ℰ)


subs : ∀ {Γ Ξ Ψ} → Γ ⊢ Ξ alltrue → Ξ ⊢ Ψ alltrue
                 → Γ ⊢ Ψ alltrue
subs ξ ψ = maps (sub ξ) ψ


--------------------------------------------------------------------------------


unlam : ∀ {Γ A B} → Γ ⊢ A ⊃ B true
                  → Γ , A ⊢ B true
unlam 𝒟 = app (wk 𝒟) vz


-- NOTE: Local completeness of ⊃

relam : ∀ {Γ A B} → Γ ⊢ A ⊃ B true
                  → Γ ⊢ A ⊃ B true
relam 𝒟 = lam (unlam 𝒟)


cut : ∀ {Γ A B} → Γ ⊢ A true → Γ , A ⊢ B true
                → Γ ⊢ B true
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


-- NOTE: Local soundness of ⊃

pseudocut : ∀ {Γ A B} → Γ ⊢ A true → Γ , A ⊢ B true
                      → Γ ⊢ B true
pseudocut 𝒟 ℰ = app (lam ℰ) 𝒟


-- NOTE: Interesting

pseudocut′ : ∀ {Γ A B} → Γ ⊢ A true → Γ , A ⊢ B true
                       → Γ ⊢ B true
pseudocut′ 𝒟 ℰ = cut 𝒟 (unlam (lam ℰ))


pseudosub : ∀ {Γ Ξ A} → Γ ⊢ Ξ alltrue → Ξ ⊢ A true
                      → Γ ⊢ A true
pseudosub ∙       𝒟 = ren bot⊇ 𝒟
pseudosub (ξ , 𝒞) 𝒟 = app (pseudosub ξ (lam 𝒟)) 𝒞


exch : ∀ {Γ A B C} → Γ , A , B ⊢ C true
                   → Γ , B , A ⊢ C true
exch 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------


pull : ∀ {Δ A B} → (Γ : List Prop) → (Δ , A) ⧺ Γ ⊢ B true
                 → Δ ⧺ (Γ , A) ⊢ B true
pull Γ (var i)   = var (pull∋ Γ i)
pull Γ (lam 𝒟)   = lam (exch (pull (Γ , _) 𝒟))
pull Γ (app 𝒟 ℰ) = app (pull Γ 𝒟) (pull Γ ℰ)


lams : ∀ {Γ A} → (Ξ : List Prop) → Γ ⧺ Ξ ⊢ A true
               → Γ ⊢ Ξ ⊃⋯⊃ A true
lams ∙       𝒟 = 𝒟
lams (Ξ , B) 𝒟 = lams Ξ (lam 𝒟)


unlams : ∀ {Γ A} → (Ξ : List Prop) → Γ ⊢ Ξ ⊃⋯⊃ A true
                 → Γ ⧺ Ξ ⊢ A true
unlams ∙       𝒟 = 𝒟
unlams (Ξ , B) 𝒟 = unlam (unlams Ξ 𝒟)


apps : ∀ {Γ Ξ A} → Γ ⊢ Ξ ⊃⋯⊃ A true → Γ ⊢ Ξ alltrue
                 → Γ ⊢ A true
apps 𝒟 ∙       = 𝒟
apps 𝒟 (ξ , ℰ) = app (apps 𝒟 ξ) ℰ


--------------------------------------------------------------------------------
