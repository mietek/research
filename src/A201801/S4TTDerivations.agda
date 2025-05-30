{-# OPTIONS --rewriting #-}

module A201801.S4TTDerivations where

open import A201801.Prelude
open import A201801.Category
open import A201801.Fin
open import A201801.Vec
open import A201801.VecLemmas
open import A201801.AllVec
open import A201801.S4TTTypes
open import A201801.S4TTTerms


--------------------------------------------------------------------------------


infix 3 _⊢_⦂_valid[_]
data _⊢_⦂_valid[_] : ∀ {d g} → Asserts d → Term d g → Type → Types g → Set
  where
    var : ∀ {A d g I} → {Δ : Asserts d} {Γ : Types g}
                      → Γ ∋⟨ I ⟩ A
                      → Δ ⊢ VAR I ⦂ A valid[ Γ ]

    lam : ∀ {A B d g M} → {Δ : Asserts d} {Γ : Types g}
                        → Δ ⊢ M ⦂ B valid[ Γ , A ]
                        → Δ ⊢ LAM M ⦂ A ⊃ B valid[ Γ ]

    app : ∀ {A B d g M N} → {Δ : Asserts d} {Γ : Types g}
                          → Δ ⊢ M ⦂ A ⊃ B valid[ Γ ] → Δ ⊢ N ⦂ A valid[ Γ ]
                          → Δ ⊢ APP M N ⦂ B valid[ Γ ]

    mvar : ∀ {A d g I} → {Δ : Asserts d} {Γ : Types g}
                       → Δ ∋⟨ I ⟩ ⟪⊫ A ⟫
                       → Δ ⊢ MVAR I ⦂ A valid[ Γ ]

    box : ∀ {A d g M} → {Δ : Asserts d} {Γ : Types g}
                      → Δ ⊢ M ⦂ A valid[ ∙ ]
                      → Δ ⊢ BOX M ⦂ □ A valid[ Γ ]

    letbox : ∀ {A B d g M N} → {Δ : Asserts d} {Γ : Types g}
                             → Δ ⊢ M ⦂ □ A valid[ Γ ] → Δ , ⟪⊫ A ⟫ ⊢ N ⦂ B valid[ Γ ]
                             → Δ ⊢ LETBOX M N ⦂ B valid[ Γ ]


infix 3 _⊢_⦂_allvalid[_]
_⊢_⦂_allvalid[_] : ∀ {d g n} → Asserts d → Terms d g n → Types n → Types g → Set
Δ ⊢ τ ⦂ Ξ allvalid[ Γ ] = All (\ { (M , A) → Δ ⊢ M ⦂ A valid[ Γ ] }) (zip τ Ξ)


infix 3 _⊢_⦂_allvalid*
_⊢_⦂_allvalid* : ∀ {d n} → Asserts d → Terms* d n → Asserts n → Set
Δ ⊢ τ ⦂ Ξ allvalid* = All (\ { (M , ⟪⊫ A ⟫) → Δ ⊢ M ⦂ A valid[ ∙ ] }) (zip τ Ξ)


--------------------------------------------------------------------------------


ren : ∀ {d g g′ e M A} → {Δ : Asserts d} {Γ : Types g} {Γ′ : Types g′}
                       → Γ′ ⊇⟨ e ⟩ Γ → Δ ⊢ M ⦂ A valid[ Γ ]
                       → Δ ⊢ REN e M ⦂ A valid[ Γ′ ]
ren η (var i)      = var (ren∋ η i)
ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
ren η (mvar i)     = mvar i
ren η (box 𝒟)      = box 𝒟
ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren η ℰ)


rens : ∀ {d g g′ e n} → {Δ : Asserts d} {Γ : Types g} {Γ′ : Types g′}
                         {τ : Terms d g n} {Ξ : Types n}
                      → Γ′ ⊇⟨ e ⟩ Γ → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ]
                      → Δ ⊢ RENS e τ ⦂ Ξ allvalid[ Γ′ ]
rens {τ = ∙}     {∙}     η ∙       = ∙
rens {τ = τ , M} {Ξ , A} η (ξ , 𝒟) = rens η ξ , ren η 𝒟


--------------------------------------------------------------------------------


mren : ∀ {d d′ g e M A} → {Δ : Asserts d} {Δ′ : Asserts d′} {Γ : Types g}
                        → Δ′ ⊇⟨ e ⟩ Δ → Δ ⊢ M ⦂ A valid[ Γ ]
                        → Δ′ ⊢ MREN e M ⦂ A valid[ Γ ]
mren η (var i)      = var i
mren η (lam 𝒟)      = lam (mren η 𝒟)
mren η (app 𝒟 ℰ)    = app (mren η 𝒟) (mren η ℰ)
mren η (mvar i)     = mvar (ren∋ η i)
mren η (box 𝒟)      = box (mren η 𝒟)
mren η (letbox 𝒟 ℰ) = letbox (mren η 𝒟) (mren (keep η) ℰ)


mrens : ∀ {d d′ g e n} → {Δ : Asserts d} {Δ′ : Asserts d′} {Γ : Types g}
                          {τ : Terms d g n} {Ξ : Types n}
                       → Δ′ ⊇⟨ e ⟩ Δ → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ]
                       → Δ′ ⊢ MRENS e τ ⦂ Ξ allvalid[ Γ ]
mrens {τ = ∙}     {∙}     η ∙       = ∙
mrens {τ = τ , M} {Ξ , A} η (ξ , 𝒟) = mrens η ξ , mren η 𝒟


mrens* : ∀ {d d′ e n} → {Δ : Asserts d} {Δ′ : Asserts d′}
                         {τ : Terms* d n} {Ξ : Asserts n}
                      → Δ′ ⊇⟨ e ⟩ Δ → Δ ⊢ τ ⦂ Ξ allvalid*
                      → Δ′ ⊢ MRENS* e τ ⦂ Ξ allvalid*
mrens* {τ = ∙}     {∙}     η ∙       = ∙
mrens* {τ = τ , M} {Ξ , A} η (ξ , 𝒟) = mrens* η ξ , mren η 𝒟


--------------------------------------------------------------------------------


wk : ∀ {B d g M A} → {Δ : Asserts d} {Γ : Types g}
                   → Δ ⊢ M ⦂ A valid[ Γ ]
                   → Δ ⊢ WK M ⦂ A valid[ Γ , B ]
wk 𝒟 = ren (drop id⊇) 𝒟


wks : ∀ {A d g n} → {Δ : Asserts d} {Γ : Types g}
                     {τ : Terms d g n} {Ξ : Types n}
                  → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ]
                  → Δ ⊢ WKS τ ⦂ Ξ allvalid[ Γ , A ]
wks ξ = rens (drop id⊇) ξ


vz : ∀ {d g A} → {Δ : Asserts d} {Γ : Types g}
               → Δ ⊢ VZ ⦂ A valid[ Γ , A ]
vz = var zero


lifts : ∀ {A d g n} → {Δ : Asserts d} {Γ : Types g}
                       {τ : Terms d g n} {Ξ : Types n}
                    → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ]
                    → Δ ⊢ LIFTS τ ⦂ Ξ , A allvalid[ Γ , A ]
lifts ξ = wks ξ , vz


vars : ∀ {d g g′ e} → {Δ : Asserts d} {Γ : Types g} {Γ′ : Types g′}
                    → Γ′ ⊇⟨ e ⟩ Γ
                    → Δ ⊢ VARS e ⦂ Γ allvalid[ Γ′ ]
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {d g} → {Δ : Asserts d} {Γ : Types g}
              → Δ ⊢ IDS ⦂ Γ allvalid[ Γ ]
ids = vars id⊇


--------------------------------------------------------------------------------


mwk : ∀ {B d g M A} → {Δ : Asserts d} {Γ : Types g}
                    → Δ ⊢ M ⦂ A valid[ Γ ]
                    → Δ , ⟪⊫ B ⟫ ⊢ MWK M ⦂ A valid[ Γ ]
mwk 𝒟 = mren (drop id⊇) 𝒟


mwks : ∀ {A d g n} → {Δ : Asserts d} {Γ : Types g}
                      {τ : Terms d g n} {Ξ : Types n}
                   → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ]
                   → Δ , ⟪⊫ A ⟫ ⊢ MWKS τ ⦂ Ξ allvalid[ Γ ]
mwks ξ = mrens (drop id⊇) ξ


mwks* : ∀ {A d n} → {Δ : Asserts d}
                     {τ : Terms* d n} {Ξ : Asserts n}
                  → Δ ⊢ τ ⦂ Ξ allvalid*
                  → Δ , ⟪⊫ A ⟫ ⊢ MWKS* τ ⦂ Ξ allvalid*
mwks* ξ = mrens* (drop id⊇) ξ


mvz : ∀ {d g A} → {Δ : Asserts d} {Γ : Types g}
                → Δ , ⟪⊫ A ⟫ ⊢ MVZ ⦂ A valid[ Γ ]
mvz = mvar zero


mlifts* : ∀ {A d n} → {Δ : Asserts d}
                       {τ : Terms* d n} {Ξ : Asserts n}
                    → Δ ⊢ τ ⦂ Ξ allvalid*
                    → Δ , ⟪⊫ A ⟫ ⊢ MLIFTS* τ ⦂ Ξ , ⟪⊫ A ⟫ allvalid*
mlifts* ξ = mwks* ξ , mvz


mvars* : ∀ {d d′ e} → {Δ : Asserts d} {Δ′ : Asserts d′}
                    → Δ′ ⊇⟨ e ⟩ Δ
                    → Δ′ ⊢ MVARS* e ⦂ Δ allvalid*
mvars* done     = ∙
mvars* (drop η) = mwks* (mvars* η)
mvars* (keep η) = mlifts* (mvars* η)


mids* : ∀ {d} → {Δ : Asserts d}
              → Δ ⊢ MIDS* ⦂ Δ allvalid*
mids* = mvars* id⊇


--------------------------------------------------------------------------------


sub : ∀ {d g n M A} → {Δ : Asserts d} {Γ : Types g}
                       {τ : Terms d g n} {Ξ : Types n}
                    → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ] → Δ ⊢ M ⦂ A valid[ Ξ ]
                    → Δ ⊢ SUB τ M ⦂ A valid[ Γ ]
sub ξ (var i)      = get ξ (zip∋₂ i)
sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (mvar i)     = mvar i
sub ξ (box 𝒟)      = box 𝒟
sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)


subs : ∀ {d g n m} → {Δ : Asserts d} {Γ : Types g}
                      {τ : Terms d g n} {Ξ : Types n}
                      {υ : Terms d n m} {Ψ : Types m}
                   → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ] → Δ ⊢ υ ⦂ Ψ allvalid[ Ξ ]
                   → Δ ⊢ SUBS τ υ ⦂ Ψ allvalid[ Γ ]
subs {υ = ∙}     {∙}     ξ ∙       = ∙
subs {υ = υ , M} {Ψ , A} ξ (ψ , 𝒟) = subs ξ ψ , sub ξ 𝒟


--------------------------------------------------------------------------------


msub : ∀ {d g n M A} → {Δ : Asserts d} {Γ : Types g}
                        {τ : Terms* d n} {Ξ : Asserts n}
                     → Δ ⊢ τ ⦂ Ξ allvalid* → Ξ ⊢ M ⦂ A valid[ Γ ]
                     → Δ ⊢ MSUB τ M ⦂ A valid[ Γ ]
msub ξ (var i)      = var i
msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
msub ξ (mvar i)     = sub ∙ (get ξ (zip∋₂ i))
msub ξ (box 𝒟)      = box (msub ξ 𝒟)
msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts* ξ) ℰ)


msubs : ∀ {d g n m} → {Δ : Asserts d} {Γ : Types g}
                       {τ : Terms* d n} {Ξ : Asserts n}
                       {υ : Terms n g m} {Ψ : Types m}
                    → Δ ⊢ τ ⦂ Ξ allvalid* → Ξ ⊢ υ ⦂ Ψ allvalid[ Γ ]
                    → Δ ⊢ MSUBS τ υ ⦂ Ψ allvalid[ Γ ]
msubs {υ = ∙}     {∙}     ξ ∙       = ∙
msubs {υ = υ , M} {Ψ , A} ξ (ψ , 𝒟) = msubs ξ ψ , msub ξ 𝒟


msubs* : ∀ {d n m} → {Δ : Asserts d}
                      {τ : Terms* d n} {Ξ : Asserts n}
                      {υ : Terms* n m} {Ψ : Asserts m}
                   → Δ ⊢ τ ⦂ Ξ allvalid* → Ξ ⊢ υ ⦂ Ψ allvalid*
                   → Δ ⊢ MSUBS* τ υ ⦂ Ψ allvalid*
msubs* {υ = ∙}     {∙}           ξ ∙       = ∙
msubs* {υ = υ , M} {Ψ , ⟪⊫ A ⟫} ξ (ψ , 𝒟) = msubs* ξ ψ , msub ξ 𝒟


--------------------------------------------------------------------------------


unlam : ∀ {d g M A B} → {Δ : Asserts d} {Γ : Types g}
                      → Δ ⊢ M ⦂ A ⊃ B valid[ Γ ]
                      → Δ ⊢ UNLAM M ⦂ B valid[ Γ , A ]
unlam 𝒟 = app (wk 𝒟) vz


cut : ∀ {d g M N A B} → {Δ : Asserts d} {Γ : Types g}
                      → Δ ⊢ M ⦂ A valid[ Γ ] → Δ ⊢ N ⦂ B valid[ Γ , A ]
                      → Δ ⊢ CUT M N ⦂ B valid[ Γ ]
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


pseudocut : ∀ {d g M N A B} → {Δ : Asserts d} {Γ : Types g}
                            → Δ ⊢ M ⦂ A valid[ Γ ] → Δ ⊢ N ⦂ B valid[ Γ , A ]
                            → Δ ⊢ PSEUDOCUT M N ⦂ B valid[ Γ ]
pseudocut 𝒟 ℰ = app (lam ℰ) 𝒟


pseudosub : ∀ {d g n M A} → {Δ : Asserts d} {Γ : Types g}
                             {τ : Terms d g n} {Ξ : Types n}
                          → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ] → Δ ⊢ M ⦂ A valid[ Ξ ]
                          → Δ ⊢ PSEUDOSUB τ M ⦂ A valid[ Γ ]
pseudosub {τ = ∙}     {∙}     ∙       𝒟 = ren bot⊇ 𝒟
pseudosub {τ = τ , M} {Ξ , B} (ξ , 𝒞) 𝒟 = app (pseudosub ξ (lam 𝒟)) 𝒞


exch : ∀ {d g M A B C} → {Δ : Asserts d} {Γ : Types g}
                       → Δ ⊢ M ⦂ C valid[ (Γ , A) , B ]
                       → Δ ⊢ EXCH M ⦂ C valid[ (Γ , B) , A ]
exch 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------


vau : ∀ {d g M A B} → {Δ : Asserts d} {Γ : Types g}
                    → Δ , ⟪⊫ A ⟫ ⊢ M ⦂ B valid[ Γ ]
                    → Δ ⊢ VAU M ⦂ B valid[ Γ , □ A ]
vau 𝒟 = letbox vz (wk 𝒟)


unvau : ∀ {d g M A B} → {Δ : Asserts d} {Γ : Types g}
                      → Δ ⊢ M ⦂ B valid[ Γ , □ A ]
                      → Δ , ⟪⊫ A ⟫ ⊢ UNVAU M ⦂ B valid[ Γ ]
unvau 𝒟 = app (lam (mwk 𝒟)) (box mvz)


boxapp : ∀ {d g M N A B} → {Δ : Asserts d} {Γ : Types g}
                         → Δ ⊢ M ⦂ □ (A ⊃ B) valid[ Γ ] → Δ ⊢ N ⦂ □ A valid[ Γ ]
                         → Δ ⊢ BOXAPP M N ⦂ □ B valid[ Γ ]
boxapp 𝒟 ℰ = letbox 𝒟 (letbox (mwk ℰ) (box (app (mwk mvz) mvz)))


unbox : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
                    → Δ ⊢ M ⦂ □ A valid[ Γ ]
                    → Δ ⊢ UNBOX M ⦂ A valid[ Γ ]
unbox 𝒟 = letbox 𝒟 mvz


-- NOTE: Local completeness of □

rebox : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
                    → Δ ⊢ M ⦂ □ A valid[ Γ ]
                    → Δ ⊢ REBOX M ⦂ □ A valid[ Γ ]
rebox 𝒟 = letbox 𝒟 (box mvz)


dupbox : ∀ {d g M A} → {Δ : Asserts d} {Γ : Types g}
                     → Δ ⊢ M ⦂ □ A valid[ Γ ]
                     → Δ ⊢ DUPBOX M ⦂ □ □ A valid[ Γ ]
dupbox 𝒟 = letbox 𝒟 (box (box mvz))


mcut : ∀ {d g M N A B} → {Δ : Asserts d} {Γ : Types g}
                       → Δ ⊢ M ⦂ A valid[ ∙ ] → Δ , ⟪⊫ A ⟫ ⊢ N ⦂ B valid[ Γ ]
                       → Δ ⊢ MCUT M N ⦂ B valid[ Γ ]
mcut 𝒟 ℰ = msub (mids* , 𝒟) ℰ


-- NOTE: Local soundness of □

pseudomcut : ∀ {d g M N A B} → {Δ : Asserts d} {Γ : Types g}
                             → Δ ⊢ M ⦂ A valid[ ∙ ] → Δ , ⟪⊫ A ⟫ ⊢ N ⦂ B valid[ Γ ]
                             → Δ ⊢ PSEUDOMCUT M N ⦂ B valid[ Γ ]
pseudomcut 𝒟 ℰ = letbox (box 𝒟) ℰ


pseudomsub : ∀ {d g n M A} → {Δ : Asserts d} {Γ : Types g}
                              {τ : Terms* d n} {Ξ : Asserts n}
                           → Δ ⊢ τ ⦂ Ξ allvalid* → Ξ ⊢ M ⦂ A valid[ Γ ]
                           → Δ ⊢ PSEUDOMSUB τ M ⦂ A valid[ Γ ]
pseudomsub {τ = ∙}     {∙}           ∙       𝒟 = mren bot⊇ 𝒟
pseudomsub {τ = τ , M} {Ξ , ⟪⊫ A ⟫} (ξ , 𝒞) 𝒟 = app (pseudomsub ξ (lam (vau 𝒟))) (box 𝒞)


mexch : ∀ {d g M A B C} → {Δ : Asserts d} {Γ : Types g}
                        → (Δ , ⟪⊫ A ⟫) , ⟪⊫ B ⟫ ⊢ M ⦂ C valid[ Γ ]
                        → (Δ , ⟪⊫ B ⟫) , ⟪⊫ A ⟫ ⊢ MEXCH M ⦂ C valid[ Γ ]
mexch 𝒟 = unvau (unvau (exch (vau (vau 𝒟))))


--------------------------------------------------------------------------------
