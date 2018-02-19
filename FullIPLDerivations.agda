module FullIPLDerivations where

open import Prelude
open import Category
open import List
open import ListLemmas
open import ListConcatenation
open import AllList
open import FullIPLPropositions


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

    pair : ∀ {A B Γ} → Γ ⊢ A true → Γ ⊢ B true
                     → Γ ⊢ A ∧ B true

    fst : ∀ {A B Γ} → Γ ⊢ A ∧ B true
                    → Γ ⊢ A true

    snd : ∀ {A B Γ} → Γ ⊢ A ∧ B true
                    → Γ ⊢ B true

    unit : ∀ {Γ} → Γ ⊢ 𝟏 true

    abort : ∀ {A Γ} → Γ ⊢ 𝟎 true
                    → Γ ⊢ A true

    inl : ∀ {A B Γ} → Γ ⊢ A true
                    → Γ ⊢ A ∨ B true

    inr : ∀ {A B Γ} → Γ ⊢ B true
                    → Γ ⊢ A ∨ B true

    case : ∀ {A B C Γ} → Γ ⊢ A ∨ B true → Γ , A ⊢ C true → Γ , B ⊢ C true
                       → Γ ⊢ C true


infix 3 _⊢_alltrue
_⊢_alltrue : List Prop → List Prop → Set
Γ ⊢ Ξ alltrue = All (Γ ⊢_true) Ξ


--------------------------------------------------------------------------------


ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A true
                 → Γ′ ⊢ A true
ren η (var i)      = var (ren∋ η i)
ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
ren η (pair 𝒟 ℰ)   = pair (ren η 𝒟) (ren η ℰ)
ren η (fst 𝒟)      = fst (ren η 𝒟)
ren η (snd 𝒟)      = snd (ren η 𝒟)
ren η unit         = unit
ren η (abort 𝒟)    = abort (ren η 𝒟)
ren η (inl 𝒟)      = inl (ren η 𝒟)
ren η (inr 𝒟)      = inr (ren η 𝒟)
ren η (case 𝒟 ℰ ℱ) = case (ren η 𝒟) (ren (keep η) ℰ) (ren (keep η) ℱ)


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
sub ξ (var i)      = get ξ i
sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (pair 𝒟 ℰ)   = pair (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (fst 𝒟)      = fst (sub ξ 𝒟)
sub ξ (snd 𝒟)      = snd (sub ξ 𝒟)
sub ξ unit         = unit
sub ξ (abort 𝒟)    = abort (sub ξ 𝒟)
sub ξ (inl 𝒟)      = inl (sub ξ 𝒟)
sub ξ (inr 𝒟)      = inr (sub ξ 𝒟)
sub ξ (case 𝒟 ℰ ℱ) = case (sub ξ 𝒟) (sub (lifts ξ) ℰ) (sub (lifts ξ) ℱ)


subs : ∀ {Γ Ξ Ψ} → Γ ⊢ Ξ alltrue → Ξ ⊢ Ψ alltrue
                 → Γ ⊢ Ψ alltrue
subs ξ ψ = maps (sub ξ) ψ


--------------------------------------------------------------------------------


unlam : ∀ {Γ A B} → Γ ⊢ A ⊃ B true
                  → Γ , A ⊢ B true
unlam 𝒟 = app (wk 𝒟) vz


relam : ∀ {Γ A B} → Γ ⊢ A ⊃ B true
                  → Γ ⊢ A ⊃ B true
relam 𝒟 = lam (unlam 𝒟)


cut : ∀ {Γ A B} → Γ ⊢ A true → Γ , A ⊢ B true
                → Γ ⊢ B true
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


pseudocut : ∀ {Γ A B} → Γ ⊢ A true → Γ , A ⊢ B true
                      → Γ ⊢ B true
pseudocut 𝒟 ℰ = app (lam ℰ) 𝒟


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
pull Γ (var i)      = var (pull∋ Γ i)
pull Γ (lam 𝒟)      = lam (exch (pull (Γ , _) 𝒟))
pull Γ (app 𝒟 ℰ)    = app (pull Γ 𝒟) (pull Γ ℰ)
pull Γ (pair 𝒟 ℰ)   = pair (pull Γ 𝒟) (pull Γ ℰ)
pull Γ (fst 𝒟)      = fst (pull Γ 𝒟)
pull Γ (snd 𝒟)      = snd (pull Γ 𝒟)
pull Γ unit         = unit
pull Γ (abort 𝒟)    = abort (pull Γ 𝒟)
pull Γ (inl 𝒟)      = inl (pull Γ 𝒟)
pull Γ (inr 𝒟)      = inr (pull Γ 𝒟)
pull Γ (case 𝒟 ℰ ℱ) = case (pull Γ 𝒟) (exch (pull (Γ , _) ℰ)) (exch (pull (Γ , _) ℱ))


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
