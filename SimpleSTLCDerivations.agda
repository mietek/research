module SimpleSTLCDerivations where

open import Prelude
open import Category
open import Fin
open import Vec
open import AllVec
open import IPLPropositions
open import StdSTLCTerms


--------------------------------------------------------------------------------


record Derivation : Set
  where
    constructor [_⊦_⦂_]
    field
      {g} : Nat
      Γ   : Truths g
      M   : Term g
      Aₜ  : Truth


record Derivations : Set
  where
    constructor [_⊦⋆_⦂_]
    field
      {g} : Nat
      {n} : Nat
      Γ   : Truths g
      x   : Terms g n
      Ξ   : Truths n


pac : ∀ {g n} → Truths g → Terms g n → Truths n
              → Vec Derivation n
pac Γ ∙       ∙            = ∙
pac Γ (x , M) (Ξ , A true) = pac Γ x Ξ , [ Γ ⊦ M ⦂ A true ]


pac∋ : ∀ {g n i A} → {Γ : Truths g} {x : Terms g n} {Ξ : Truths n}
                   → Ξ ∋⟨ i ⟩ A true
                   → pac Γ x Ξ ∋⟨ i ⟩ [ Γ ⊦ GET x i ⦂ A true ]
pac∋ {x = x , M} {Ξ , A true} zero    = zero
pac∋ {x = x , N} {Ξ , B true} (suc 𝒾) = suc (pac∋ 𝒾)


--------------------------------------------------------------------------------


infix 3 ⊢_
data ⊢_ : Derivation → Set
  where
    var : ∀ {A g i} → {Γ : Truths g}
                    → Γ ∋⟨ i ⟩ A true
                    → ⊢ [ Γ ⊦ VAR i ⦂ A true ]

    lam : ∀ {A B g M} → {Γ : Truths g}
                      → ⊢ [ Γ , A true ⊦ M ⦂ B true ]
                      → ⊢ [ Γ ⊦ LAM M ⦂ A ⊃ B true ]

    app : ∀ {A B g M N} → {Γ : Truths g}
                        → ⊢ [ Γ ⊦ M ⦂ A ⊃ B true ] → ⊢ [ Γ ⊦ N ⦂ A true ]
                        → ⊢ [ Γ ⊦ APP M N ⦂ B true ]


infix 3 ⊢⋆_
⊢⋆_ : Derivations → Set
⊢⋆ [ Γ ⊦⋆ x ⦂ Ξ ] = All (⊢_) (pac Γ x Ξ)


--------------------------------------------------------------------------------


ren : ∀ {g g′ e M A} → {Γ : Truths g} {Γ′ : Truths g′}
                     → Γ′ ⊇⟨ e ⟩ Γ → ⊢ [ Γ ⊦ M ⦂ A true ]
                     → ⊢ [ Γ′ ⊦ REN e M ⦂ A true ]
ren η (var 𝒾)   = var (ren∋ η 𝒾)
ren η (lam 𝒟)   = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ) = app (ren η 𝒟) (ren η ℰ)


wk : ∀ {B g M A} → {Γ : Truths g}
                 → ⊢ [ Γ ⊦ M ⦂ A true ]
                 → ⊢ [ Γ , B true ⊦ WK M ⦂ A true ]
wk 𝒟 = ren (drop id⊇) 𝒟


vz : ∀ {g A} → {Γ : Truths g}
             → ⊢ [ Γ , A true ⊦ VZ ⦂ A true ]
vz = var zero


--------------------------------------------------------------------------------


rens : ∀ {g g′ e n} → {Γ : Truths g} {Γ′ : Truths g′} {x : Terms g n} {Ξ : Truths n}
                    → Γ′ ⊇⟨ e ⟩ Γ → ⊢⋆ [ Γ ⊦⋆ x ⦂ Ξ ]
                    → ⊢⋆ [ Γ′ ⊦⋆ RENS e x ⦂ Ξ ]
rens {x = ∙}     {∙}          η ∙       = ∙
rens {x = x , M} {Ξ , A true} η (ξ , 𝒟) = rens η ξ , ren η 𝒟
-- NOTE: Equivalent to
-- rens η ξ = maps (ren η) ξ


wks : ∀ {g n A} → {Γ : Truths g} {x : Terms g n} {Ξ : Truths n}
                → ⊢⋆ [ Γ ⊦⋆ x ⦂ Ξ ]
                → ⊢⋆ [ Γ , A true ⊦⋆ WKS x ⦂ Ξ ]
wks ξ = rens (drop id⊇) ξ


lifts : ∀ {g n A} → {Γ : Truths g} {x : Terms g n} {Ξ : Truths n}
                  → ⊢⋆ [ Γ ⊦⋆ x ⦂ Ξ ]
                  → ⊢⋆ [ Γ , A true ⊦⋆ LIFTS x ⦂ Ξ , A true ]
lifts ξ = wks ξ , vz


vars : ∀ {g g′ e} → {Γ : Truths g} {Γ′ : Truths g′}
                  → Γ′ ⊇⟨ e ⟩ Γ
                  → ⊢⋆ [ Γ′ ⊦⋆ VARS e ⦂ Γ ]
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {g} → {Γ : Truths g}
            → ⊢⋆ [ Γ ⊦⋆ IDS ⦂ Γ ]
ids = vars id⊇


--------------------------------------------------------------------------------


sub : ∀ {g n M A} → {Γ : Truths g} {x : Terms g n} {Ξ : Truths n}
                  → ⊢⋆ [ Γ ⊦⋆ x ⦂ Ξ ] → ⊢ [ Ξ ⊦ M ⦂ A ]
                  → ⊢ [ Γ ⊦ SUB x M ⦂ A ]
sub ξ (var 𝒾)   = get ξ (pac∋ 𝒾)
sub ξ (lam 𝒟)   = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ) = app (sub ξ 𝒟) (sub ξ ℰ)


cut : ∀ {g M N A B} → {Γ : Truths g}
                    → ⊢ [ Γ ⊦ M ⦂ A true ] → ⊢ [ Γ , A true ⊦ N ⦂ B true ]
                    → ⊢ [ Γ ⊦ CUT M N ⦂ B true ]
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


--------------------------------------------------------------------------------


unlam : ∀ {g M A B} → {Γ : Truths g}
                    → ⊢ [ Γ ⊦ M ⦂ A ⊃ B true ]
                    → ⊢ [ Γ , A true ⊦ UNLAM M ⦂ B true ]
unlam 𝒟 = app (wk 𝒟) vz


ex : ∀ {g M A B C} → {Γ : Truths g}
                   → ⊢ [ Γ , A true , B true ⊦ M ⦂ C true ]
                   → ⊢ [ Γ , B true , A true ⊦ EX M ⦂ C true ]
ex 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------
