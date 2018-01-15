module SymIPL where

open import Prelude
open import List
open import AllList
import StdIPL as Std
open Std using (Prop ; BASE ; _⊃_ ; Truth ; _true)


--------------------------------------------------------------------------------


infix 3 _⊢_
data _⊢_ : List Truth → Truth → Set
  where
    vz : ∀ {A Γ} → Γ , A true ⊢ A true

    wk : ∀ {A B Γ} → Γ ⊢ A true
                   → Γ , B true ⊢ A true

    cut : ∀ {A B Γ} → Γ ⊢ A true → Γ , A true ⊢ B true
                    → Γ ⊢ B true

    lam : ∀ {A B Γ} → Γ , A true ⊢ B true
                    → Γ ⊢ A ⊃ B true

    unlam : ∀ {A B Γ} → Γ ⊢ A ⊃ B true
                      → Γ , A true ⊢ B true


infix 3 _⊢⋆_
_⊢⋆_ : List Truth → List Truth → Set
Γ ⊢⋆ Ξ = All (Γ ⊢_) Ξ


--------------------------------------------------------------------------------


wks : ∀ {A Γ Ξ} → Γ ⊢⋆ Ξ
                → Γ , A true ⊢⋆ Ξ
wks ξ = maps wk ξ


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


sub : ∀ {Γ Ξ A} → Γ ⊢⋆ Ξ → Ξ ⊢ A true
                → Γ ⊢ A true
sub (ξ , 𝒟) vz        = 𝒟
sub (ξ , 𝒟) (wk ℰ)    = sub ξ ℰ
sub ξ       (cut 𝒟 ℰ) = cut (sub ξ 𝒟) (sub (lifts ξ) ℰ)
sub ξ       (lam 𝒟)   = lam (sub (lifts ξ) 𝒟)
sub (ξ , 𝒟) (unlam ℰ) = cut 𝒟 (unlam (sub ξ ℰ))


subs : ∀ {Γ Ξ Ψ} → Γ ⊢⋆ Ξ → Ξ ⊢⋆ Ψ
                 → Γ ⊢⋆ Ψ
subs ξ ψ = maps (sub ξ) ψ


ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A true
                 → Γ′ ⊢ A true
ren η 𝒟 = sub (vars η) 𝒟


rens : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢⋆ Ξ
                  → Γ′ ⊢⋆ Ξ
rens η ξ = maps (ren η) ξ


--------------------------------------------------------------------------------


var : ∀ {Γ A} → Γ ∋ A true
              → Γ ⊢ A true
var zero    = vz
var (suc 𝒾) = wk (var 𝒾)


app : ∀ {Γ A B} → Γ ⊢ A ⊃ B true → Γ ⊢ A true
                → Γ ⊢ B true
app 𝒟 ℰ = cut ℰ (unlam 𝒟)


--------------------------------------------------------------------------------


fromStd : ∀ {Γ A} → Γ Std.⊢ A true
                  → Γ ⊢ A true
fromStd (Std.var 𝒾)   = var 𝒾
fromStd (Std.lam 𝒟)   = lam (fromStd 𝒟)
fromStd (Std.app 𝒟 ℰ) = app (fromStd 𝒟) (fromStd ℰ)


toStd : ∀ {Γ A} → Γ ⊢ A true
                → Γ Std.⊢ A true
toStd vz        = Std.vz
toStd (wk 𝒟)    = Std.wk (toStd 𝒟)
toStd (cut 𝒟 ℰ) = Std.cut (toStd 𝒟) (toStd ℰ)
toStd (lam 𝒟)   = Std.lam (toStd 𝒟)
toStd (unlam 𝒟) = Std.unlam (toStd 𝒟)


--------------------------------------------------------------------------------
