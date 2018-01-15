module StdIPLDerivations where

open import Prelude
open import List
open import AllList
open import StdIPLPropositions


--------------------------------------------------------------------------------


infix 7 _true
record Truth : Set
  where
    constructor _true
    field
      A : Prop


--------------------------------------------------------------------------------


-- In general, we read “J₁, …, Jₙ ⊢ J” as “from the assumptions that J₁, …,
-- and that Jₙ, we deduce that J”.
--
-- Therefore, we read “A₁ true, …, Aₙ true ⊢ A true” as “from the assumptions
-- that A₁ is true, …, and that Aₙ is true, we deduce that A is true”.

infix 3 _⊢_
data _⊢_ : List Truth → Truth → Set
  where
    var : ∀ {A Γ} → Γ ∋ A true
                  → Γ ⊢ A true

    lam : ∀ {A B Γ} → Γ , A true ⊢ B true
                    → Γ ⊢ A ⊃ B true

    app : ∀ {A B Γ} → Γ ⊢ A ⊃ B true → Γ ⊢ A true
                    → Γ ⊢ B true


infix 3 _⊢⋆_
_⊢⋆_ : List Truth → List Truth → Set
Γ ⊢⋆ Ξ = All (Γ ⊢_) Ξ


--------------------------------------------------------------------------------


ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A true
                 → Γ′ ⊢ A true
ren η (var 𝒾)   = var (ren∋ η 𝒾)
ren η (lam 𝒟)   = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ) = app (ren η 𝒟) (ren η ℰ)


rens : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢⋆ Ξ
                  → Γ′ ⊢⋆ Ξ
rens η ξ = maps (ren η) ξ


wk : ∀ {B A Γ} → Γ ⊢ A true
               → Γ , B true ⊢ A true
wk 𝒟 = ren (drop id⊇) 𝒟


wks : ∀ {A Γ Ξ} → Γ ⊢⋆ Ξ
                → Γ , A true ⊢⋆ Ξ
wks ξ = rens (drop id⊇) ξ


vz : ∀ {A Γ} → Γ , A true ⊢ A true
vz = var zero


lifts : ∀ {A Γ Ξ} → Γ ⊢⋆ Ξ
                  → Γ , A true ⊢⋆ Ξ , A true
lifts ξ = wks ξ , vz


vars : ∀ {Γ Γ′} → Γ′ ⊇ Γ
                → Γ′ ⊢⋆ Γ
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {Γ} → Γ ⊢⋆ Γ
ids = vars id⊇


--------------------------------------------------------------------------------


sub : ∀ {Γ Ξ A} → Γ ⊢⋆ Ξ → Ξ ⊢ A true
                → Γ ⊢ A true
sub ξ (var 𝒾)   = get ξ 𝒾
sub ξ (lam 𝒟)   = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ) = app (sub ξ 𝒟) (sub ξ ℰ)


subs : ∀ {Γ Ξ Ψ} → Γ ⊢⋆ Ξ → Ξ ⊢⋆ Ψ
                 → Γ ⊢⋆ Ψ
subs ξ ψ = maps (sub ξ) ψ


cut : ∀ {Γ A B} → Γ ⊢ A true → Γ , A true ⊢ B true
                → Γ ⊢ B true
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


--------------------------------------------------------------------------------


unlam : ∀ {Γ A B} → Γ ⊢ A ⊃ B true
                  → Γ , A true ⊢ B true
unlam 𝒟 = app (wk 𝒟) vz


ex : ∀ {Γ A B C} → Γ , A true , B true ⊢ C true
                 → Γ , B true , A true ⊢ C true
ex 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------
