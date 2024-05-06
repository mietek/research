module A201802.WIP.LR1a where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.FinLemmas
open import A201801.Vec
open import A201801.VecLemmas
open import A201801.AllVec


--------------------------------------------------------------------------------


infixr 8 _⊃_
data Type : Set
  where
    bool : Type
    _⊃_  : Type → Type → Type


Types : Nat → Set
Types g = Vec Type g


--------------------------------------------------------------------------------


data Exp (g : Nat) : Set
  where
    var   : Fin g → Exp g
    lam   : Exp (suc g) → Exp g
    app   : Exp g → Exp g → Exp g
    true  : Exp g
    false : Exp g
    if    : Exp g → Exp g → Exp g → Exp g


Exps : Nat → Nat → Set
Exps g n = Vec (Exp g) n


ren : ∀ {g g′} → g′ ≥ g → Exp g
               → Exp g′
ren r (var i)       = var (REN∋ r i)
ren r (lam e)       = lam (ren (keep r) e)
ren r (app e₁ e₂)   = app (ren r e₁) (ren r e₂)
ren r true          = true
ren r false         = false
ren r (if e₁ e₂ e₃) = if (ren r e₁) (ren r e₂) (ren r e₃)


rens : ∀ {g g′ n} → g′ ≥ g → Exps g n
                  → Exps g′ n
rens r s = MAPS (ren r) s


wk : ∀ {g} → Exp g
           → Exp (suc g)
wk e = ren (drop id≥) e


wks : ∀ {g n} → Exps g n
              → Exps (suc g) n
wks s = rens (drop id≥) s


vz : ∀ {g} → Exp (suc g)
vz = var zero


lifts : ∀ {g n} → Exps g n
                → Exps (suc g) (suc n)
lifts s = wks s , vz


vars : ∀ {g g′} → g′ ≥ g
                → Exps g′ g
vars done     = ∙
vars (drop r) = wks (vars r)
vars (keep r) = lifts (vars r)


ids : ∀ {g} → Exps g g
ids = vars id≥


sub : ∀ {g n} → Exps g n → Exp n
              → Exp g
sub s (var i)       = GET s i
sub s (lam e)       = lam (sub (lifts s) e)
sub s (app e₁ e₂)   = app (sub s e₁) (sub s e₂)
sub s true          = true
sub s false         = false
sub s (if e₁ e₂ e₃) = if (sub s e₁) (sub s e₂) (sub s e₃)


subs : ∀ {g n m} → Exps g n → Exps n m
                 → Exps g m
subs s₁ s₂ = MAPS (sub s₁) s₂


cut : ∀ {g} → Exp g → Exp (suc g)
            → Exp g
cut e₁ e₂ = sub (ids , e₁) e₂


--------------------------------------------------------------------------------


infix 3 _⊢_⦂_
data _⊢_⦂_ {g} (Γ : Types g) : Exp g → Type → Set
  where
    VAR : ∀ {τ i} → Γ ∋⟨ i ⟩ τ
                  → Γ ⊢ var i ⦂ τ

    LAM : ∀ {τ₁ τ₂ e} → Γ , τ₁ ⊢ e ⦂ τ₂
                      → Γ ⊢ lam e ⦂ τ₁ ⊃ τ₂

    APP : ∀ {τ₁ τ₂ e₁ e₂} → Γ ⊢ e₁ ⦂ τ₁ ⊃ τ₂ → Γ ⊢ e₂ ⦂ τ₁
                          → Γ ⊢ app e₁ e₂ ⦂ τ₂

    TRUE : Γ ⊢ true ⦂ bool

    FALSE : Γ ⊢ false ⦂ bool

    IF : ∀ {τ e₁ e₂ e₃} → Γ ⊢ e₁ ⦂ bool → Γ ⊢ e₂ ⦂ τ → Γ ⊢ e₃ ⦂ τ
                        → Γ ⊢ if e₁ e₂ e₃ ⦂ τ


infix 3 _⊢_⦂_all
_⊢_⦂_all : ∀ {g n} → Types g → Exps g n → Types n → Set
Γ ⊢ s ⦂ Ξ all = All (\ { (e , τ) → Γ ⊢ e ⦂ τ }) (zip s Ξ)


REN : ∀ {g g′ r e τ} → {Γ : Types g} {Γ′ : Types g′}
                     → Γ′ ⊇⟨ r ⟩ Γ → Γ ⊢ e ⦂ τ
                     → Γ′ ⊢ ren r e ⦂ τ
REN ρ (VAR I)       = VAR (ren∋ ρ I)
REN ρ (LAM D)       = LAM (REN (keep ρ) D)
REN ρ (APP D₁ D₂)   = APP (REN ρ D₁) (REN ρ D₂)
REN ρ TRUE          = TRUE
REN ρ FALSE         = FALSE
REN ρ (IF D₁ D₂ D₃) = IF (REN ρ D₁) (REN ρ D₂) (REN ρ D₃)


RENS : ∀ {g g′ r n} → {Γ : Types g} {Γ′ : Types g′}
                       {s : Exps g n} {Ξ : Types n}
                    → Γ′ ⊇⟨ r ⟩ Γ → Γ ⊢ s ⦂ Ξ all
                    → Γ′ ⊢ rens r s ⦂ Ξ all
RENS {s = ∙}     {∙}     ρ ∙       = ∙
RENS {s = s , e} {Ξ , τ} ρ (σ , D) = RENS ρ σ , REN ρ D


WK : ∀ {g e τ₁ τ₂} → {Γ : Types g}
                   → Γ ⊢ e ⦂ τ₂
                   → Γ , τ₁ ⊢ wk e ⦂ τ₂
WK D = REN (drop id⊇) D


WKS : ∀ {g n τ} → {Γ : Types g} {s : Exps g n} {Ξ : Types n}
                → Γ ⊢ s ⦂ Ξ all
                → Γ , τ ⊢ wks s ⦂ Ξ all
WKS σ = RENS (drop id⊇) σ


VZ : ∀ {g τ} → {Γ : Types g}
             → Γ , τ ⊢ vz ⦂ τ
VZ = VAR zero


LIFTS : ∀ {g n τ} → {Γ : Types g} {s : Exps g n} {Ξ : Types n}
                  → Γ ⊢ s ⦂ Ξ all
                  → Γ , τ ⊢ lifts s ⦂ Ξ , τ all
LIFTS σ = WKS σ , VZ


VARS : ∀ {g g′ r} → {Γ : Types g} {Γ′ : Types g′}
                  → Γ′ ⊇⟨ r ⟩ Γ
                  → Γ′ ⊢ vars r ⦂ Γ all
VARS done     = ∙
VARS (drop ρ) = WKS (VARS ρ)
VARS (keep ρ) = LIFTS (VARS ρ)


IDS : ∀ {g} → {Γ : Types g}
            → Γ ⊢ ids ⦂ Γ all
IDS = VARS id⊇


SUB : ∀ {g n e τ} → {Γ : Types g} {s : Exps g n} {Ξ : Types n}
                  → Γ ⊢ s ⦂ Ξ all → Ξ ⊢ e ⦂ τ
                  → Γ ⊢ sub s e ⦂ τ
SUB σ (VAR I)       = get σ (zip∋₂ I)
SUB σ (LAM D)       = LAM (SUB (LIFTS σ) D)
SUB σ (APP D₁ D₂)   = APP (SUB σ D₁) (SUB σ D₂)
SUB σ TRUE          = TRUE
SUB σ FALSE         = FALSE
SUB σ (IF D₁ D₂ D₃) = IF (SUB σ D₁) (SUB σ D₂) (SUB σ D₃)


SUBS : ∀ {g n m} → {Γ : Types g} {s₁ : Exps g n} {Ξ₁ : Types n}
                    {s₂ : Exps n m} {Ξ₂ : Types m}
                 → Γ ⊢ s₁ ⦂ Ξ₁ all → Ξ₁ ⊢ s₂ ⦂ Ξ₂ all
                 → Γ ⊢ subs s₁ s₂ ⦂ Ξ₂ all
SUBS {s₂ = ∙}      {∙}      σ₁ ∙        = ∙
SUBS {s₂ = s₂ , e} {Ξ₂ , τ} σ₁ (σ₂ , D) = SUBS σ₁ σ₂ , SUB σ₁ D


CUT : ∀ {g e₁ e₂ τ₁ τ₂} → {Γ : Types g}
                        → Γ ⊢ e₁ ⦂ τ₁ → Γ , τ₁ ⊢ e₂ ⦂ τ₂
                        → Γ ⊢ cut e₁ e₂ ⦂ τ₂
CUT D₁ D₂ = SUB (IDS , D₁) D₂


--------------------------------------------------------------------------------
