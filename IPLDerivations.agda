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


infix 3 _⊢_true*
_⊢_true* : List Prop → List Prop → Set
Γ ⊢ Ξ true* = All (Γ ⊢_true) Ξ


--------------------------------------------------------------------------------


ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A true
                 → Γ′ ⊢ A true
ren η (var i)   = var (ren∋ η i)
ren η (lam 𝒟)   = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ) = app (ren η 𝒟) (ren η ℰ)


rens : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢ Ξ true*
                  → Γ′ ⊢ Ξ true*
rens η ξ = maps (ren η) ξ


--------------------------------------------------------------------------------


wk : ∀ {B A Γ} → Γ ⊢ A true
               → Γ , B ⊢ A true
wk 𝒟 = ren (drop id) 𝒟


vz : ∀ {A Γ} → Γ , A ⊢ A true
vz = var zero


wks : ∀ {A Γ Ξ} → Γ ⊢ Ξ true*
                → Γ , A ⊢ Ξ true*
wks ξ = rens (drop id) ξ


lifts : ∀ {A Γ Ξ} → Γ ⊢ Ξ true*
                  → Γ , A ⊢ Ξ , A true*
lifts ξ = wks ξ , vz


vars : ∀ {Γ Γ′} → Γ′ ⊇ Γ
                → Γ′ ⊢ Γ true*
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {Γ} → Γ ⊢ Γ true*
ids = vars id


--------------------------------------------------------------------------------


sub : ∀ {Γ Ξ A} → Γ ⊢ Ξ true* → Ξ ⊢ A true
                → Γ ⊢ A true
sub ξ (var i)   = get ξ i
sub ξ (lam 𝒟)   = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ) = app (sub ξ 𝒟) (sub ξ ℰ)


subs : ∀ {Γ Ξ Ψ} → Γ ⊢ Ξ true* → Ξ ⊢ Ψ true*
                 → Γ ⊢ Ψ true*
subs ξ ψ = maps (sub ξ) ψ


--------------------------------------------------------------------------------


unlam : ∀ {Γ A B} → Γ ⊢ A ⊃ B true
                  → Γ , A ⊢ B true
unlam 𝒟 = app (wk 𝒟) vz


cut : ∀ {Γ A B} → Γ ⊢ A true → Γ , A ⊢ B true
                → Γ ⊢ B true
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


cut′ : ∀ {Γ A B} → Γ ⊢ A true → Γ , A ⊢ B true
                 → Γ ⊢ B true
cut′ 𝒟 ℰ = app (lam ℰ) 𝒟


wkn : ∀ {Γ A} → ∙ ⊢ A true
              → Γ ⊢ A true
wkn {∙}     𝒟 = 𝒟
wkn {Γ , B} 𝒟 = wk (wkn 𝒟)


sub′ : ∀ {Γ Ξ A} → Γ ⊢ Ξ true* → Ξ ⊢ A true
                 → Γ ⊢ A true
sub′ ∙       𝒟 = wkn 𝒟
sub′ (ξ , 𝒞) 𝒟 = app (sub′ ξ (lam 𝒟)) 𝒞


exch : ∀ {Γ A B C} → Γ , A , B ⊢ C true
                   → Γ , B , A ⊢ C true
exch 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------


pull : ∀ {Δ A B} → (Γ : List Prop) → (Δ , A) ⧺ Γ ⊢ B true
                 → Δ ⧺ (Γ , A) ⊢ B true
pull Γ (var i)   = var (pull∋ Γ i )
pull Γ (lam 𝒟)   = lam (exch (pull (Γ , _) 𝒟))
pull Γ (app 𝒟 ℰ) = app (pull Γ 𝒟) (pull Γ ℰ)


--------------------------------------------------------------------------------
