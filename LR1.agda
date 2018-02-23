module LR1 where

open import Prelude
open import Category
open import Fin
open import FinLemmas
-- open import List
-- open import ListLemmas
open import Vec
open import VecLemmas
open import AllVec


--------------------------------------------------------------------------------


infixr 8 _⊃_
data Type : Set
  where
    𝔹   : Type
    _⊃_ : Type → Type → Type

Types : Nat → Set
Types g = Vec Type g


--------------------------------------------------------------------------------


data Term (g : Nat) : Set
  where
    VAR   : Fin g → Term g
    LAM   : Term (suc g) → Term g
    APP   : Term g → Term g → Term g
    TRUE  : Term g
    FALSE : Term g
    IF    : Term g → Term g → Term g → Term g

Terms : Nat → Nat → Set
Terms g n = Vec (Term g) n

REN : ∀ {g g′} → g′ ≥ g → Term g
               → Term g′
REN e (VAR I)    = VAR (REN∋ e I)
REN e (LAM M)    = LAM (REN (keep e) M)
REN e (APP M N)  = APP (REN e M) (REN e N)
REN e TRUE       = TRUE
REN e FALSE      = FALSE
REN e (IF M N O) = IF (REN e M) (REN e N) (REN e O)

RENS : ∀ {g g′ n} → g′ ≥ g → Terms g n
                  → Terms g′ n
RENS e τ = MAPS (REN e) τ

WK : ∀ {g} → Term g
           → Term (suc g)
WK M = REN (drop id) M

WKS : ∀ {g n} → Terms g n
              → Terms (suc g) n
WKS τ = RENS (drop id) τ

VZ : ∀ {g} → Term (suc g)
VZ = VAR zero

LIFTS : ∀ {g n} → Terms g n
                → Terms (suc g) (suc n)
LIFTS τ = WKS τ , VZ

VARS : ∀ {g g′} → g′ ≥ g
                → Terms g′ g
VARS done     = ∙
VARS (drop e) = WKS (VARS e)
VARS (keep e) = LIFTS (VARS e)

IDS : ∀ {g} → Terms g g
IDS = VARS id

SUB : ∀ {g n} → Terms g n → Term n
              → Term g
SUB τ (VAR I)    = GET τ I
SUB τ (LAM M)    = LAM (SUB (LIFTS τ) M)
SUB τ (APP M N)  = APP (SUB τ M) (SUB τ N)
SUB τ TRUE       = TRUE
SUB τ FALSE      = FALSE
SUB τ (IF M N O) = IF (SUB τ M) (SUB τ N) (SUB τ O)

SUBS : ∀ {g n m} → Terms g n → Terms n m
                 → Terms g m
SUBS τ υ = MAPS (SUB τ) υ

CUT : ∀ {g} → Term g → Term (suc g)
            → Term g
CUT M N = SUB (IDS , M) N


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

    true : Γ ⊢ TRUE ⦂ 𝔹

    false : Γ ⊢ FALSE ⦂ 𝔹

    if : ∀ {C M N O} → Γ ⊢ M ⦂ 𝔹 → Γ ⊢ N ⦂ C → Γ ⊢ O ⦂ C
                     → Γ ⊢ IF M N O ⦂ C

infix 3 _⊢_⦂_all
_⊢_⦂_all : ∀ {g n} → Types g → Terms g n → Types n → Set
Γ ⊢ τ ⦂ Ξ all = All (\ { (M , A) → Γ ⊢ M ⦂ A }) (zip τ Ξ)

ren : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                     → Γ′ ⊇⟨ e ⟩ Γ → Γ ⊢ M ⦂ A
                     → Γ′ ⊢ REN e M ⦂ A
ren η (var i)    = var (ren∋ η i)
ren η (lam 𝒟)    = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ)  = app (ren η 𝒟) (ren η ℰ)
ren η true       = true
ren η false      = false
ren η (if 𝒟 ℰ ℱ) = if (ren η 𝒟) (ren η ℰ) (ren η ℱ)

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

sub : ∀ {g n M A} → {Γ : Types g} {τ : Terms g n} {Ξ : Types n}
                  → Γ ⊢ τ ⦂ Ξ all → Ξ ⊢ M ⦂ A
                  → Γ ⊢ SUB τ M ⦂ A
sub ξ (var i)    = get ξ (zip∋₂ i)
sub ξ (lam 𝒟)    = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ)  = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ true       = true
sub ξ false      = false
sub ξ (if 𝒟 ℰ ℱ) = if (sub ξ 𝒟) (sub ξ ℰ) (sub ξ ℱ)

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
