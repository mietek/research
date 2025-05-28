{-# OPTIONS --rewriting #-}

module A201802.LR1 where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.FinLemmas
open import A201801.Vec
open import A201801.VecLemmas
open import A201801.AllVec

open import A201802.LR0


--------------------------------------------------------------------------------


infix 3 _⊢_⦂_
data _⊢_⦂_ {g} (Γ : Types g) : Term g → Type → Set
  where
    var : ∀ {A I} → Γ ∋⟨ I ⟩ A
                  → Γ ⊢ VAR I ⦂ A

    lam : ∀ {A B M} → Γ , A ⊢ M ⦂ B
                    → Γ ⊢ LAM M ⦂ A ⊃ B

    app : ∀ {A B M N} → Γ ⊢ M ⦂ A ⊃ B → Γ ⊢ N ⦂ A
                      → Γ ⊢ APP M N ⦂ B

    pair : ∀ {A B M N} → Γ ⊢ M ⦂ A → Γ ⊢ N ⦂ B
                       → Γ ⊢ PAIR M N ⦂ A ∧ B

    fst : ∀ {A B M} → Γ ⊢ M ⦂ A ∧ B
                    → Γ ⊢ FST M ⦂ A

    snd : ∀ {A B M} → Γ ⊢ M ⦂ A ∧ B
                    → Γ ⊢ SND M ⦂ B

    unit : Γ ⊢ UNIT ⦂ 𝟙

    abort : ∀ {C M} → Γ ⊢ M ⦂ 𝟘
                    → Γ ⊢ ABORT M ⦂ C

    left : ∀ {A B M} → Γ ⊢ M ⦂ A
                     → Γ ⊢ LEFT M ⦂ A ∨ B

    right : ∀ {A B M} → Γ ⊢ M ⦂ B
                      → Γ ⊢ RIGHT M ⦂ A ∨ B

    case : ∀ {A B C M N O} → Γ ⊢ M ⦂ A ∨ B → Γ , A ⊢ N ⦂ C → Γ , B ⊢ O ⦂ C
                           → Γ ⊢ CASE M N O ⦂ C

    true : Γ ⊢ TRUE ⦂ 𝔹

    false : Γ ⊢ FALSE ⦂ 𝔹

    if : ∀ {C M N O} → Γ ⊢ M ⦂ 𝔹 → Γ ⊢ N ⦂ C → Γ ⊢ O ⦂ C
                     → Γ ⊢ IF M N O ⦂ C


infix 3 _⊢_⦂_all
_⊢_⦂_all : ∀ {g n} → Types g → Terms g n → Types n → Set
Γ ⊢ τ ⦂ Ξ all = All (\ { (M , A) → Γ ⊢ M ⦂ A }) (zip τ Ξ)


--------------------------------------------------------------------------------


ren : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                     → Γ′ ⊇⟨ e ⟩ Γ → Γ ⊢ M ⦂ A
                     → Γ′ ⊢ REN e M ⦂ A
ren η (var i)      = var (ren∋ η i)
ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
ren η (pair 𝒟 ℰ)   = pair (ren η 𝒟) (ren η ℰ)
ren η (fst 𝒟)      = fst (ren η 𝒟)
ren η (snd 𝒟)      = snd (ren η 𝒟)
ren η unit         = unit
ren η (abort 𝒟)    = abort (ren η 𝒟)
ren η (left 𝒟)     = left (ren η 𝒟)
ren η (right 𝒟)    = right (ren η 𝒟)
ren η (case 𝒟 ℰ ℱ) = case (ren η 𝒟) (ren (keep η) ℰ) (ren (keep η) ℱ)
ren η true         = true
ren η false        = false
ren η (if 𝒟 ℰ ℱ)   = if (ren η 𝒟) (ren η ℰ) (ren η ℱ)


rens : ∀ {g g′ e n} → {Γ : Types g} {Γ′ : Types g′}
                       {τ : Terms g n} {Ξ : Types n}
                    → Γ′ ⊇⟨ e ⟩ Γ → Γ ⊢ τ ⦂ Ξ all
                    → Γ′ ⊢ RENS e τ ⦂ Ξ all
rens {τ = ∙}     {∙}     η ∙       = ∙
rens {τ = τ , M} {Ξ , A} η (ξ , 𝒟) = rens η ξ , ren η 𝒟


wk : ∀ {B g M A} → {Γ : Types g}
                 → Γ ⊢ M ⦂ A
                 → Γ , B ⊢ WK M ⦂ A
wk 𝒟 = ren (drop id⊇) 𝒟


wks : ∀ {g n A} → {Γ : Types g} {τ : Terms g n} {Ξ : Types n}
                → Γ ⊢ τ ⦂ Ξ all
                → Γ , A ⊢ WKS τ ⦂ Ξ all
wks ξ = rens (drop id⊇) ξ


vz : ∀ {g A} → {Γ : Types g}
             → Γ , A ⊢ VZ ⦂ A
vz = var zero


lifts : ∀ {g n A} → {Γ : Types g} {τ : Terms g n} {Ξ : Types n}
                  → Γ ⊢ τ ⦂ Ξ all
                  → Γ , A ⊢ LIFTS τ ⦂ Ξ , A all
lifts ξ = wks ξ , vz


vars : ∀ {g g′ e} → {Γ : Types g} {Γ′ : Types g′}
                  → Γ′ ⊇⟨ e ⟩ Γ
                  → Γ′ ⊢ VARS e ⦂ Γ all
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {g} → {Γ : Types g}
            → Γ ⊢ IDS ⦂ Γ all
ids = vars id⊇


-- Substitution is type-preserving.
sub : ∀ {g n M A} → {Γ : Types g} {τ : Terms g n} {Ξ : Types n}
                  → Γ ⊢ τ ⦂ Ξ all → Ξ ⊢ M ⦂ A
                  → Γ ⊢ SUB τ M ⦂ A
sub ξ (var i)      = get ξ (zip∋₂ i)
sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (pair 𝒟 ℰ)   = pair (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (fst 𝒟)      = fst (sub ξ 𝒟)
sub ξ (snd 𝒟)      = snd (sub ξ 𝒟)
sub ξ unit         = unit
sub ξ (abort 𝒟)    = abort (sub ξ 𝒟)
sub ξ (left 𝒟)     = left (sub ξ 𝒟)
sub ξ (right 𝒟)    = right (sub ξ 𝒟)
sub ξ (case 𝒟 ℰ ℱ) = case (sub ξ 𝒟) (sub (lifts ξ) ℰ) (sub (lifts ξ) ℱ)
sub ξ true         = true
sub ξ false        = false
sub ξ (if 𝒟 ℰ ℱ)   = if (sub ξ 𝒟) (sub ξ ℰ) (sub ξ ℱ)


subs : ∀ {g n m} → {Γ : Types g} {τ : Terms g n} {Ξ : Types n}
                    {υ : Terms n m}  {Ψ : Types m}
                 → Γ ⊢ τ ⦂ Ξ all → Ξ ⊢ υ ⦂ Ψ all
                 → Γ ⊢ SUBS τ υ ⦂ Ψ all
subs {υ = ∙}     {∙}     ξ ∙       = ∙
subs {υ = υ , M} {Ψ , A} ξ (ψ , 𝒟) = subs ξ ψ , sub ξ 𝒟


cut : ∀ {g M N A B} → {Γ : Types g}
                    → Γ ⊢ M ⦂ A → Γ , A ⊢ N ⦂ B
                    → Γ ⊢ CUT M N ⦂ B
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


--------------------------------------------------------------------------------
