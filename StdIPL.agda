module StdIPL where

open import Prelude
open import List
open import AllList
open GetAllList


--------------------------------------------------------------------------------


infixr 8 _⊃_
data Prop : Set
  where
    BASE : Prop
    _⊃_  : Prop → Prop → Prop


infix 7 _true
record Truth : Set
  where
    constructor _true
    field
      A : Prop


--------------------------------------------------------------------------------


Context : Set
Context = List Truth


--------------------------------------------------------------------------------


infix 3 _⊢_
data _⊢_ : Context → Truth → Set
  where
    var : ∀ {A Γ} → Γ ∋ A true
                  → Γ ⊢ A true

    lam : ∀ {A B Γ} → Γ , A true ⊢ B true
                    → Γ ⊢ A ⊃ B true

    app : ∀ {A B Γ} → Γ ⊢ A ⊃ B true → Γ ⊢ A true
                    → Γ ⊢ B true


--------------------------------------------------------------------------------


ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A true
                 → Γ′ ⊢ A true
ren η (var 𝒾)   = var (ren∋ η 𝒾)
ren η (lam 𝒟)   = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ) = app (ren η 𝒟) (ren η ℰ)


wk : ∀ {B A Γ} → Γ ⊢ A true
               → Γ , B true ⊢ A true
wk 𝒟 = ren (drop id⊇) 𝒟


vz : ∀ {A Γ} → Γ , A true ⊢ A true
vz = var zero


--------------------------------------------------------------------------------


infix 3 _⊢⋆_
_⊢⋆_ : Context → List Truth → Set
Γ ⊢⋆ Ξ = All (Γ ⊢_) Ξ


--------------------------------------------------------------------------------


rens : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢⋆ Ξ
                  → Γ′ ⊢⋆ Ξ
rens η ξ = maps (ren η) ξ


wks : ∀ {A Γ Ξ} → Γ ⊢⋆ Ξ
                → Γ , A true ⊢⋆ Ξ
wks ξ = rens (drop id⊇) ξ


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


cut : ∀ {Γ A B} → Γ ⊢ A true → Γ , A true ⊢ B true
                → Γ ⊢ B true
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


--------------------------------------------------------------------------------


subs : ∀ {Γ Ξ Ψ} → Γ ⊢⋆ Ξ → Ξ ⊢⋆ Ψ
                 → Γ ⊢⋆ Ψ
subs ξ ψ = maps (sub ξ) ψ


--------------------------------------------------------------------------------


unlam : ∀ {Γ A B} → Γ ⊢ A ⊃ B true
                  → Γ , A true ⊢ B true
unlam 𝒟 = app (wk 𝒟) vz


ex : ∀ {Γ A B C} → Γ , A true , B true ⊢ C true
                 → Γ , B true , A true ⊢ C true
ex 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------
