module STLCDerivations where

open import Prelude
open import Category
open import Fin
open import Vec
open import AllVec
open import STLCTypes
open import STLCTerms


--------------------------------------------------------------------------------


infix 4 _⊦_⦂_
record Typing : Set
  where
    constructor _⊦_⦂_
    field
      {g} : Nat
      Γ   : Types g
      M   : Term g
      A   : Type


infix 4 _⊦⋆_⦂_
record Typings : Set
  where
    constructor _⊦⋆_⦂_
    field
      {g} : Nat
      {n} : Nat
      Γ   : Types g
      x   : Terms g n
      Ξ   : Types n


pac : ∀ {g n} → Types g → Terms g n → Types n
              → Vec Typing n
pac Γ ∙       ∙       = ∙
pac Γ (x , M) (Ξ , A) = pac Γ x Ξ , (Γ ⊦ M ⦂ A)


pac∋ : ∀ {g n I A} → {Γ : Types g} {x : Terms g n} {Ξ : Types n}
                   → Ξ ∋⟨ I ⟩ A
                   → pac Γ x Ξ ∋⟨ I ⟩ (Γ ⊦ GET x I ⦂ A)
pac∋ {x = x , M} {Ξ , A} zero    = zero
pac∋ {x = x , N} {Ξ , B} (suc i) = suc (pac∋ i)


--------------------------------------------------------------------------------


infix 3 ⊢_
data ⊢_ : Typing → Set
  where
    var : ∀ {A g I} → {Γ : Types g}
                    → Γ ∋⟨ I ⟩ A
                    → ⊢ Γ ⊦ VAR I ⦂ A

    lam : ∀ {A B g M} → {Γ : Types g}
                      → ⊢ Γ , A ⊦ M ⦂ B
                      → ⊢ Γ ⊦ LAM M ⦂ A ⊃ B

    app : ∀ {A B g M N} → {Γ : Types g}
                        → ⊢ Γ ⊦ M ⦂ A ⊃ B → ⊢ Γ ⊦ N ⦂ A
                        → ⊢ Γ ⊦ APP M N ⦂ B


infix 3 ⊢⋆_
⊢⋆_ : Typings → Set
⊢⋆ Γ ⊦⋆ x ⦂ Ξ = All (⊢_) (pac Γ x Ξ)


--------------------------------------------------------------------------------


ren : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                     → Γ′ ⊇⟨ e ⟩ Γ → ⊢ Γ ⊦ M ⦂ A
                     → ⊢ Γ′ ⊦ REN e M ⦂ A
ren η (var i)   = var (ren∋ η i)
ren η (lam 𝒟)   = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ) = app (ren η 𝒟) (ren η ℰ)


rens : ∀ {g g′ e n} → {Γ : Types g} {Γ′ : Types g′} {x : Terms g n} {Ξ : Types n}
                    → Γ′ ⊇⟨ e ⟩ Γ → ⊢⋆ Γ ⊦⋆ x ⦂ Ξ
                    → ⊢⋆ Γ′ ⊦⋆ RENS e x ⦂ Ξ
rens {x = ∙}     {∙}     η ∙       = ∙
rens {x = x , M} {Ξ , A} η (ξ , 𝒟) = rens η ξ , ren η 𝒟
-- NOTE: Equivalent to
-- rens η ξ = maps (ren η) ξ


--------------------------------------------------------------------------------


wk : ∀ {B g M A} → {Γ : Types g}
                 → ⊢ Γ ⊦ M ⦂ A
                 → ⊢ Γ , B ⊦ WK M ⦂ A
wk 𝒟 = ren (drop id⊇) 𝒟


vz : ∀ {g A} → {Γ : Types g}
             → ⊢ Γ , A ⊦ VZ ⦂ A
vz = var zero


wks : ∀ {g n A} → {Γ : Types g} {x : Terms g n} {Ξ : Types n}
                → ⊢⋆ Γ ⊦⋆ x ⦂ Ξ
                → ⊢⋆ Γ , A ⊦⋆ WKS x ⦂ Ξ
wks ξ = rens (drop id⊇) ξ


lifts : ∀ {g n A} → {Γ : Types g} {x : Terms g n} {Ξ : Types n}
                  → ⊢⋆ Γ ⊦⋆ x ⦂ Ξ
                  → ⊢⋆ Γ , A ⊦⋆ LIFTS x ⦂ Ξ , A
lifts ξ = wks ξ , vz


vars : ∀ {g g′ e} → {Γ : Types g} {Γ′ : Types g′}
                  → Γ′ ⊇⟨ e ⟩ Γ
                  → ⊢⋆ Γ′ ⊦⋆ VARS e ⦂ Γ
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {g} → {Γ : Types g}
            → ⊢⋆ Γ ⊦⋆ IDS ⦂ Γ
ids = vars id⊇


--------------------------------------------------------------------------------


sub : ∀ {g n M A} → {Γ : Types g} {x : Terms g n} {Ξ : Types n}
                  → ⊢⋆ Γ ⊦⋆ x ⦂ Ξ → ⊢ Ξ ⊦ M ⦂ A
                  → ⊢ Γ ⊦ SUB x M ⦂ A
sub ξ (var i)   = get ξ (pac∋ i)
sub ξ (lam 𝒟)   = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ) = app (sub ξ 𝒟) (sub ξ ℰ)


subs : ∀ {g n m} → {Γ : Types g} {x : Terms g n} {y : Terms n m} {Ξ : Types n} {Ψ : Types m}
                 → ⊢⋆ Γ ⊦⋆ x ⦂ Ξ → ⊢⋆ Ξ ⊦⋆ y ⦂ Ψ
                 → ⊢⋆ Γ ⊦⋆ SUBS x y ⦂ Ψ
subs {y = ∙}     {Ψ = ∙}     ξ ∙       = ∙
subs {y = y , M} {Ψ = Ψ , A} ξ (ψ , 𝒟) = subs ξ ψ , sub ξ 𝒟
-- NOTE: Equivalent to
-- subs ξ ψ = maps (sub ξ) ψ


--------------------------------------------------------------------------------


unlam : ∀ {g M A B} → {Γ : Types g}
                    → ⊢ Γ ⊦ M ⦂ A ⊃ B
                    → ⊢ Γ , A ⊦ UNLAM M ⦂ B
unlam 𝒟 = app (wk 𝒟) vz


cut : ∀ {g M N A B} → {Γ : Types g}
                    → ⊢ Γ ⊦ M ⦂ A → ⊢ Γ , A ⊦ N ⦂ B
                    → ⊢ Γ ⊦ CUT M N ⦂ B
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


cut′ : ∀ {g M N A B} → {Γ : Types g}
                     → ⊢ Γ ⊦ M ⦂ A → ⊢ Γ , A ⊦ N ⦂ B
                     → ⊢ Γ ⊦ CUT′ M N ⦂ B
cut′ 𝒟 ℰ = app (lam ℰ) 𝒟


wkn : ∀ {g M A} → {Γ : Types g}
                → ⊢ ∙ ⊦ M ⦂ A
                → ⊢ Γ ⊦ WKN M ⦂ A
wkn {Γ = ∙}     𝒟 = 𝒟
wkn {Γ = Γ , B} 𝒟 = wk (wkn 𝒟)


sub′ : ∀ {g n M A} → {Γ : Types g} {x : Terms g n} {Ξ : Types n}
                   → ⊢⋆ Γ ⊦⋆ x ⦂ Ξ → ⊢ Ξ ⊦ M ⦂ A
                   → ⊢ Γ ⊦ SUB′ x M ⦂ A
sub′ {x = ∙}     {∙}     ∙       𝒟 = wkn 𝒟
sub′ {x = x , M} {Ξ , B} (ξ , 𝒞) 𝒟 = app (sub′ ξ (lam 𝒟)) 𝒞


exch : ∀ {g M A B C} → {Γ : Types g}
                     → ⊢ Γ , A , B ⊦ M ⦂ C
                     → ⊢ Γ , B , A ⊦ EXCH M ⦂ C
exch 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------
