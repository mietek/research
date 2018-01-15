module SymS4 where

open import Prelude
open import List
open List²
open import AllList
import StdS4 as Std
open Std using (Prop ; BASE ; _⊃_ ; □_ ; Truth ; _true ; Validity ; _valid)


--------------------------------------------------------------------------------


infix 3 _⊢_
data _⊢_ : List² Validity Truth → Truth → Set
  where
    vz : ∀ {A Δ Γ} → Δ ⨾ Γ , A true ⊢ A true

    wk : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true
                     → Δ ⨾ Γ , B true ⊢ A true

    cut : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true → Δ ⨾ Γ , A true ⊢ B true
                      → Δ ⨾ Γ ⊢ B true

    lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A true ⊢ B true
                      → Δ ⨾ Γ ⊢ A ⊃ B true

    unlam : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true
                        → Δ ⨾ Γ , A true ⊢ B true

    mvz : ∀ {A Δ Γ} → Δ , A valid ⨾ Γ ⊢ A true

    mwk : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true
                      → Δ , B valid ⨾ Γ ⊢ A true

    mcut : ∀ {A B Δ Γ} → Δ ⨾ ∙ ⊢ A true → Δ , A valid ⨾ Γ ⊢ B true
                       → Δ ⨾ Γ ⊢ B true

    up : ∀ {A B Δ Γ} → Δ ⨾ Γ , □ A true ⊢ B true
                     → Δ , A valid ⨾ Γ ⊢ B true

    down : ∀ {A B Δ Γ} → Δ , A valid ⨾ Γ ⊢ B true
                       → Δ ⨾ Γ , □ A true ⊢ B true


infix 3 _⊢⋆_
_⊢⋆_ : List² Validity Truth → List Truth → Set
Δ ⨾ Γ ⊢⋆ Ξ = All (Δ ⨾ Γ ⊢_) Ξ


--------------------------------------------------------------------------------


wks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                  → Δ ⨾ Γ , A true ⊢⋆ Ξ
wks ξ = maps wk ξ


lifts : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                    → Δ ⨾ Γ , A true ⊢⋆ Ξ , A true
lifts ξ = wks ξ , vz


vars : ∀ {Δ Γ Γ′} → Γ′ ⊇ Γ
                  → Δ ⨾ Γ′ ⊢⋆ Γ
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {Δ Γ} → Δ ⨾ Γ ⊢⋆ Γ
ids = vars id⊇


mwks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                   → Δ , A valid ⨾ Γ ⊢⋆ Ξ
mwks ξ = maps mwk ξ


mlifts : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                     → Δ , A valid ⨾ Γ ⊢⋆ Ξ , A true
mlifts ξ = mwks ξ , mvz


-- mvars : ∀ {Δ Δ′ Γ} → Δ′ ⊇ Δ
--                    → Δ′ ⨾ Γ ⊢⋆ {!Δ!}
-- mvars done     = ∙
-- mvars (drop η) = mwks (mvars η)
-- mvars (keep η) = mlifts (mvars η)
--
--
-- mids : ∀ {Δ Γ} → Δ ⨾ Γ ⊢⋆ {!Δ!}
-- mids = mvars id⊇


ups : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ , □ A true ⊢⋆ Ξ
                  → Δ , A valid ⨾ Γ ⊢⋆ Ξ
ups ξ = maps up ξ

downs : ∀ {Δ Γ Ξ A} → Δ , A valid ⨾ Γ ⊢⋆ Ξ
                    → Δ ⨾ Γ , □ A true ⊢⋆ Ξ
downs ξ = maps down ξ


sub : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢⋆ Ξ → Δ ⨾ Ξ ⊢ A true
                  → Δ ⨾ Γ ⊢ A true
sub (ξ , 𝒟) vz         = 𝒟
sub (ξ , 𝒟) (wk ℰ)     = sub ξ ℰ
sub ξ       (cut 𝒟 ℰ)  = cut (sub ξ 𝒟) (sub (lifts ξ) ℰ)
sub ξ       (lam 𝒟)    = lam (sub (lifts ξ) 𝒟)
sub (ξ , 𝒟) (unlam ℰ)  = cut 𝒟 (unlam (sub ξ ℰ))
sub ξ       mvz        = mvz
sub ξ       (mwk 𝒟)    = up (sub (downs ξ) 𝒟)
sub ξ       (mcut 𝒟 ℰ) = mcut 𝒟 (sub (mwks ξ) ℰ)
sub ξ       (up 𝒟)     = up (sub (downs ξ , vz) 𝒟)
sub (ξ , 𝒟) (down ℰ)   = cut 𝒟 (down (sub (mwks ξ) ℰ))


--------------------------------------------------------------------------------


var : ∀ {Δ Γ A} → Γ ∋ A true
                → Δ ⨾ Γ ⊢ A true
var zero    = vz
var (suc 𝒾) = wk (var 𝒾)


app : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A ⊃ B true → Δ ⨾ Γ ⊢ A true
                  → Δ ⨾ Γ ⊢ B true
app 𝒟 ℰ = cut ℰ (unlam 𝒟)


mvar : ∀ {Δ Γ A} → Δ ∋ A valid
                 → Δ ⨾ Γ ⊢ A true
mvar zero    = mvz
mvar (suc 𝒾) = mwk (mvar 𝒾)


box : ∀ {Δ Γ A} → Δ ⨾ ∙ ⊢ A true
                → Δ ⨾ Γ ⊢ □ A true
box 𝒟 = mcut 𝒟 (up vz)


letbox : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ □ A true → Δ , A valid ⨾ Γ ⊢ B true
                     → Δ ⨾ Γ ⊢ B true
letbox 𝒟 ℰ = cut 𝒟 (down ℰ)


--------------------------------------------------------------------------------


fromStd : ∀ {Γ A} → Γ Std.⊢ A true
                  → Γ ⊢ A true
fromStd (Std.var 𝒾)      = var 𝒾
fromStd (Std.lam 𝒟)      = lam (fromStd 𝒟)
fromStd (Std.app 𝒟 ℰ)    = app (fromStd 𝒟) (fromStd ℰ)
fromStd (Std.mvar 𝒾)     = mvar 𝒾
fromStd (Std.box 𝒟)      = box (fromStd 𝒟)
fromStd (Std.letbox 𝒟 ℰ) = letbox (fromStd 𝒟) (fromStd ℰ)


toStd : ∀ {Γ A} → Γ ⊢ A true
                → Γ Std.⊢ A true
toStd vz         = Std.vz
toStd (wk 𝒟)     = Std.wk (toStd 𝒟)
toStd (cut 𝒟 ℰ)  = Std.cut (toStd 𝒟) (toStd ℰ)
toStd (lam 𝒟)    = Std.lam (toStd 𝒟)
toStd (unlam 𝒟)  = Std.unlam (toStd 𝒟)
toStd mvz        = Std.mvz
toStd (mwk 𝒟)    = Std.mwk (toStd 𝒟)
toStd (mcut 𝒟 ℰ) = Std.mcut (toStd 𝒟) (toStd ℰ)
toStd (up 𝒟)     = Std.up (toStd 𝒟)
toStd (down 𝒟)   = Std.down (toStd 𝒟)


--------------------------------------------------------------------------------


import StdIPL as IPL
open IPL using (BASE ; _⊃_ ; _true)


⌈_⌉ₚ : IPL.Prop → Prop
⌈ BASE ⌉ₚ  = BASE
⌈ A ⊃ B ⌉ₚ = ⌈ A ⌉ₚ ⊃ ⌈ B ⌉ₚ

⌈_⌉ₕ : List IPL.Truth → List Truth
⌈ ∙ ⌉ₕ          = ∙
⌈ Γ , A true ⌉ₕ = ⌈ Γ ⌉ₕ , ⌈ A ⌉ₚ true

⌈_⌉ᵢ : ∀ {Γ A} → Γ ∋ A true
               → ⌈ Γ ⌉ₕ ∋ ⌈ A ⌉ₚ true
⌈ zero ⌉ᵢ  = zero
⌈ suc 𝒾 ⌉ᵢ = suc ⌈ 𝒾 ⌉ᵢ

⌈_⌉ : ∀ {Γ A} → Γ IPL.⊢ A true
              → ∙ ⨾ ⌈ Γ ⌉ₕ ⊢ ⌈ A ⌉ₚ true
⌈ IPL.var 𝒾 ⌉   = var ⌈ 𝒾 ⌉ᵢ
⌈ IPL.lam 𝒟 ⌉   = lam ⌈ 𝒟 ⌉
⌈ IPL.app 𝒟 ℰ ⌉ = app ⌈ 𝒟 ⌉ ⌈ ℰ ⌉


⌊_⌋ₚ : Prop → IPL.Prop
⌊ BASE ⌋ₚ  = BASE
⌊ A ⊃ B ⌋ₚ = ⌊ A ⌋ₚ ⊃ ⌊ B ⌋ₚ
⌊ □ A ⌋ₚ   = ⌊ A ⌋ₚ

⌊_⌋ₕ : List Truth → List IPL.Truth
⌊ ∙ ⌋ₕ          = ∙
⌊ Γ , A true ⌋ₕ = ⌊ Γ ⌋ₕ , ⌊ A ⌋ₚ true

⌊_⌋ᵢ : ∀ {Γ A} → Γ ∋ A true
               → ⌊ Γ ⌋ₕ ∋ ⌊ A ⌋ₚ true
⌊ zero ⌋ᵢ  = zero
⌊ suc 𝒾 ⌋ᵢ = suc ⌊ 𝒾 ⌋ᵢ

-- {-# TERMINATING #-}
⌊_⌋ : ∀ {Γ A} → ∙ ⨾ Γ ⊢ A true
              → ⌊ Γ ⌋ₕ IPL.⊢ ⌊ A ⌋ₚ true
⌊ vz ⌋       = IPL.vz
⌊ wk 𝒟 ⌋     = IPL.wk ⌊ 𝒟 ⌋
⌊ cut 𝒟 ℰ ⌋  = IPL.cut ⌊ 𝒟 ⌋ ⌊ ℰ ⌋
⌊ lam 𝒟 ⌋    = IPL.lam ⌊ 𝒟 ⌋
⌊ unlam 𝒟 ⌋  = IPL.unlam ⌊ 𝒟 ⌋
⌊ mcut 𝒟 ℰ ⌋ = IPL.cut (IPL.sub ∙ ⌊ 𝒟 ⌋) {!⌊ down ℰ ⌋!}
⌊ down 𝒟 ⌋   = {!!}

-- ⌊ var 𝒾 ⌋      = var ⌊ 𝒾 ⌋ᵢ
-- ⌊ lam 𝒟 ⌋      = lam ⌊ 𝒟 ⌋
-- ⌊ app 𝒟 ℰ ⌋    = app ⌊ 𝒟 ⌋ ⌊ ℰ ⌋
-- ⌊ mvar () ⌋
-- ⌊ box 𝒟 ⌋      = IPL.sub ∙ ⌊ 𝒟 ⌋
-- ⌊ letbox 𝒟 ℰ ⌋ = ⌊ cut 𝒟 (down ℰ) ⌋ -- woah!
