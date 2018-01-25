module STLCDerivations where

open import Prelude
open import Category
open import Fin
open import Vec
open import VecLemmas
open import AllVec
open import STLCTypes
open import STLCTerms


--------------------------------------------------------------------------------


infix 3 ⊢_⦂_valid[_]
data ⊢_⦂_valid[_] : ∀ {g} → Term g → Type → Types g → Set
  where
    var : ∀ {A g I} → {Γ : Types g}
                    → Γ ∋⟨ I ⟩ A
                    → ⊢ VAR I ⦂ A valid[ Γ ]

    lam : ∀ {A B g M} → {Γ : Types g}
                      → ⊢ M ⦂ B valid[ Γ , A ]
                      → ⊢ LAM M ⦂ A ⊃ B valid[ Γ ]

    app : ∀ {A B g M N} → {Γ : Types g}
                        → ⊢ M ⦂ A ⊃ B valid[ Γ ] → ⊢ N ⦂ A valid[ Γ ]
                        → ⊢ APP M N ⦂ B valid[ Γ ]


infix 3 ⊢_⦂_allvalid[_]
⊢_⦂_allvalid[_] : ∀ {g n} → Terms g n → Types n → Types g → Set
⊢ x ⦂ Ξ allvalid[ Γ ] = All (\ { (M , A) → ⊢ M ⦂ A valid[ Γ ] }) (zip x Ξ)


--------------------------------------------------------------------------------


ren : ∀ {g g′ e M A} → {Γ : Types g} {Γ′ : Types g′}
                     → Γ′ ⊇⟨ e ⟩ Γ → ⊢ M ⦂ A valid[ Γ ]
                     → ⊢ REN e M ⦂ A valid[ Γ′ ]
ren η (var i)   = var (ren∋ η i)
ren η (lam 𝒟)   = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ) = app (ren η 𝒟) (ren η ℰ)


rens : ∀ {g g′ e n} → {Γ : Types g} {Γ′ : Types g′} {x : Terms g n} {Ξ : Types n}
                    → Γ′ ⊇⟨ e ⟩ Γ → ⊢ x ⦂ Ξ allvalid[ Γ ]
                    → ⊢ RENS e x ⦂ Ξ allvalid[ Γ′ ]
rens {x = ∙}     {∙}     η ∙       = ∙
rens {x = x , M} {Ξ , A} η (ξ , 𝒟) = rens η ξ , ren η 𝒟


--------------------------------------------------------------------------------


wk : ∀ {B g M A} → {Γ : Types g}
                 → ⊢ M ⦂ A valid[ Γ ]
                 → ⊢ WK M ⦂ A valid[ Γ , B ]
wk 𝒟 = ren (drop id⊇) 𝒟


vz : ∀ {g A} → {Γ : Types g}
             → ⊢ VZ ⦂ A valid[ Γ , A ]
vz = var zero


wks : ∀ {g n A} → {Γ : Types g} {x : Terms g n} {Ξ : Types n}
                → ⊢ x ⦂ Ξ allvalid[ Γ ]
                → ⊢ WKS x ⦂ Ξ allvalid[ Γ , A ]
wks ξ = rens (drop id⊇) ξ


lifts : ∀ {g n A} → {Γ : Types g} {x : Terms g n} {Ξ : Types n}
                  → ⊢ x ⦂ Ξ allvalid[ Γ ]
                  → ⊢ LIFTS x ⦂ Ξ , A allvalid[ Γ , A ]
lifts ξ = wks ξ , vz


vars : ∀ {g g′ e} → {Γ : Types g} {Γ′ : Types g′}
                  → Γ′ ⊇⟨ e ⟩ Γ
                  → ⊢ VARS e ⦂ Γ allvalid[ Γ′ ]
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {g} → {Γ : Types g}
            → ⊢ IDS ⦂ Γ allvalid[ Γ ]
ids = vars id⊇


--------------------------------------------------------------------------------


sub : ∀ {g n M A} → {Γ : Types g} {x : Terms g n} {Ξ : Types n}
                  → ⊢ x ⦂ Ξ allvalid[ Γ ] → ⊢ M ⦂ A valid[ Ξ ]
                  → ⊢ SUB x M ⦂ A valid[ Γ ]
sub ξ (var i)   = get ξ (zip∋₂ i)
sub ξ (lam 𝒟)   = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ) = app (sub ξ 𝒟) (sub ξ ℰ)


subs : ∀ {g n m} → {Γ : Types g} {x : Terms g n} {y : Terms n m} {Ξ : Types n} {Ψ : Types m}
                 → ⊢ x ⦂ Ξ allvalid[ Γ ] → ⊢ y ⦂ Ψ allvalid[ Ξ ]
                 → ⊢ SUBS x y ⦂ Ψ allvalid[ Γ ]
subs {y = ∙}     {Ψ = ∙}     ξ ∙       = ∙
subs {y = y , M} {Ψ = Ψ , A} ξ (ψ , 𝒟) = subs ξ ψ , sub ξ 𝒟


--------------------------------------------------------------------------------


unlam : ∀ {g M A B} → {Γ : Types g}
                    → ⊢ M ⦂ A ⊃ B valid[ Γ ]
                    → ⊢ UNLAM M ⦂ B valid[ Γ , A ]
unlam 𝒟 = app (wk 𝒟) vz


cut : ∀ {g M N A B} → {Γ : Types g}
                    → ⊢ M ⦂ A valid[ Γ ] → ⊢ N ⦂ B valid[ Γ , A ]
                    → ⊢ CUT M N ⦂ B valid[ Γ ]
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


pseudocut : ∀ {g M N A B} → {Γ : Types g}
                          → ⊢ M ⦂ A valid[ Γ ] → ⊢ N ⦂ B valid[ Γ , A ]
                          → ⊢ PSEUDOCUT M N ⦂ B valid[ Γ ]
pseudocut 𝒟 ℰ = app (lam ℰ) 𝒟


pseudosub : ∀ {g n M A} → {Γ : Types g} {x : Terms g n} {Ξ : Types n}
                        → ⊢ x ⦂ Ξ allvalid[ Γ ] → ⊢ M ⦂ A valid[ Ξ ]
                        → ⊢ PSEUDOSUB x M ⦂ A valid[ Γ ]
pseudosub {x = ∙}     {∙}     ∙       𝒟 = ren bot⊇ 𝒟
pseudosub {x = x , M} {Ξ , B} (ξ , 𝒞) 𝒟 = app (pseudosub ξ (lam 𝒟)) 𝒞


exch : ∀ {g M A B C} → {Γ : Types g}
                     → ⊢ M ⦂ C valid[ Γ , A , B ]
                     → ⊢ EXCH M ⦂ C valid[ Γ , B , A ]
exch 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------
