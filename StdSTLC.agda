module StdSTLC where

open import Prelude
open import Fin
open import Vec


data Term : Nat → Set
  where
    VAR : ∀ {g} → Fin g → Term g
    LAM : ∀ {g} → Term (suc g) → Term g
    APP : ∀ {g} → Term g → Term g → Term g


REN : ∀ {g g′} → g′ ≥ g → Term g
               → Term g′
REN e (VAR i)   = VAR (renFin e i)
REN e (LAM M)   = LAM (REN (keep e) M)
REN e (APP M N) = APP (REN e M) (REN e N)

WK : ∀ {g} → Term g
           → Term (suc g)
WK M = REN (drop id≥) M

VZ : ∀ {g} → Term (suc g)
VZ = VAR zero


Terms : Nat → Nat → Set
Terms g x = Vec (Term g) x


RENS : ∀ {g g′ x} → g′ ≥ g → Terms g x
                  → Terms g′ x
RENS e ζ = map (REN e) ζ

WKS : ∀ {g x} → Terms g x
              → Terms (suc g) x
WKS ζ = RENS (drop id≥) ζ

LIFTS : ∀ {g x} → Terms g x
                → Terms (suc g) (suc x)
LIFTS ζ = WKS ζ , VZ

IDS : ∀ {g} → Terms g g
IDS {zero}  = ∙
IDS {suc g} = LIFTS IDS


SUB : ∀ {g x} → Terms g x → Term x
              → Term g
SUB ζ (VAR i)   = get ζ i
SUB ζ (LAM M)   = LAM (SUB (LIFTS ζ) M)
SUB ζ (APP M N) = APP (SUB ζ M) (SUB ζ N)

CUT : ∀ {g} → Term g → Term (suc g)
            → Term g
CUT M N = SUB (IDS , M) N


UNLAM : ∀ {g} → Term g
              → Term (suc g)
UNLAM M = APP (WK M) VZ

EX : ∀ {g} → Term (suc (suc g))
           → Term (suc (suc g))
EX M = APP (APP (WK (WK (LAM (LAM M)))) VZ) (WK VZ)


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

Truths : Nat → Set
Truths g = Vec Truth g


record Derivation : Set
  where
    constructor [_⊢_⦂_]
    field
      {g} : Nat
      Γ   : Truths g
      M   : Term g
      A   : Truth


infix 3 ∙⋙_
data ∙⋙_ : Derivation → Set
  where
    var : ∀ {A g i} → {Γ : Truths g}
                    → Γ ∋⟨ i ⟩ A true
                    → ∙⋙ [ Γ ⊢ VAR i ⦂ A true ]

    lam : ∀ {A B g M} → {Γ : Truths g}
                      → ∙⋙ [ Γ , A true ⊢ M ⦂ B true ]
                      → ∙⋙ [ Γ ⊢ LAM M ⦂ A ⊃ B true ]

    app : ∀ {A B g M N} → {Γ : Truths g}
                        → ∙⋙ [ Γ ⊢ M ⦂ A ⊃ B true ] → ∙⋙ [ Γ ⊢ N ⦂ A true ]
                        → ∙⋙ [ Γ ⊢ APP M N ⦂ B true ]


ren : ∀ {g g′ e M A} → {Γ : Truths g} {Γ′ : Truths g′}
                     → Γ′ ⊇⟨ e ⟩ Γ → ∙⋙ [ Γ ⊢ M ⦂ A true ]
                     → ∙⋙ [ Γ′ ⊢ REN e M ⦂ A true ]
ren η (var 𝒾)   = var (ren∋ η 𝒾)
ren η (lam 𝒟)   = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ) = app (ren η 𝒟) (ren η ℰ)

wk : ∀ {B g M A} → {Γ : Truths g}
                 → ∙⋙ [ Γ ⊢ M ⦂ A true ]
                 → ∙⋙ [ Γ , B true ⊢ WK M ⦂ A true ]
wk 𝒟 = ren (drop id⊇) 𝒟

vz : ∀ {g A} → {Γ : Truths g}
             → ∙⋙ [ Γ , A true ⊢ VZ ⦂ A true ]
vz = var zero


record Derivations : Set
  where
    constructor [_⊢⋆_⦂_]
    field
      {g} : Nat
      {x} : Nat
      Γ   : Truths g
      ζ   : Terms g x
      Ξ   : Truths x


infix 3 ∙⋙⋆_
∙⋙⋆_ : Derivations → Set
∙⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ] = All (\ { (M , A true) → ∙⋙ [ Γ ⊢ M ⦂ A true ] }) (zip ζ Ξ)


rens : ∀ {g g′ e x} → {Γ : Truths g} {Γ′ : Truths g′} {ζ : Terms g x} {Ξ : Truths x}
                    → Γ′ ⊇⟨ e ⟩ Γ → ∙⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
                    → ∙⋙⋆ [ Γ′ ⊢⋆ RENS e ζ ⦂ Ξ ]
rens {ζ = ∙}     {∙}          η ∙       = ∙
rens {ζ = ζ , M} {Ξ , A true} η (ξ , 𝒟) = rens η ξ , ren η 𝒟
-- NOTE: Equivalent to
-- rens η ξ = mapAll (ren η) ξ

wks : ∀ {g x A} → {Γ : Truths g} {ζ : Terms g x} {Ξ : Truths x}
                → ∙⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
                → ∙⋙⋆ [ Γ , A true ⊢⋆ WKS ζ ⦂ Ξ ]
wks ξ = rens (drop id⊇) ξ

lifts : ∀ {g x A} → {Γ : Truths g} {ζ : Terms g x} {Ξ : Truths x}
                  → ∙⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
                  → ∙⋙⋆ [ Γ , A true ⊢⋆ LIFTS ζ ⦂ Ξ , A true ]
lifts ξ = wks ξ , vz

ids : ∀ {g} → {Γ : Truths g}
            → ∙⋙⋆ [ Γ ⊢⋆ IDS ⦂ Γ ]
ids {Γ = ∙}          = ∙
ids {Γ = Γ , A true} = lifts ids


sub : ∀ {g x M A} → {Γ : Truths g} {ζ : Terms g x} {Ξ : Truths x}
                  → ∙⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ] → ∙⋙ [ Ξ ⊢ M ⦂ A ]
                  → ∙⋙ [ Γ ⊢ SUB ζ M ⦂ A ]
sub ξ (var 𝒾)   = lookup ξ (zip∋₂ 𝒾)
sub ξ (lam 𝒟)   = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ) = app (sub ξ 𝒟) (sub ξ ℰ)

cut : ∀ {g M N A B} → {Γ : Truths g}
                    → ∙⋙ [ Γ ⊢ M ⦂ A true ] → ∙⋙ [ Γ , A true ⊢ N ⦂ B true ]
                    → ∙⋙ [ Γ ⊢ CUT M N ⦂ B true ]
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


unlam : ∀ {g M A B} → {Γ : Truths g}
                    → ∙⋙ [ Γ ⊢ M ⦂ A ⊃ B true ]
                    → ∙⋙ [ Γ , A true ⊢ UNLAM M ⦂ B true ]
unlam 𝒟 = app (wk 𝒟) vz

ex : ∀ {g M A B C} → {Γ : Truths g}
                   → ∙⋙ [ Γ , A true , B true ⊢ M ⦂ C true ]
                   → ∙⋙ [ Γ , B true , A true ⊢ EX M ⦂ C true ]
ex 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)
