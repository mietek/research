module RealS4Derivations where

open import Prelude
open import Category
open import List
open import ListLemmas
open import ListConcatenation
open import AllList
open import S4Propositions
import IPLPropositions as IPL
import IPLDerivations as IPL


--------------------------------------------------------------------------------


record Assert : Set
  where
    constructor ⟪⊫_⟫
    field
      A : Prop


--------------------------------------------------------------------------------


infix 3 _⊢_valid[_]
data _⊢_valid[_] : List Assert → Prop → List Prop → Set
  where
    var : ∀ {A Δ Γ} → Γ ∋ A
                    → Δ ⊢ A valid[ Γ ]

    lam : ∀ {A B Δ Γ} → Δ ⊢ B valid[ Γ , A ]
                      → Δ ⊢ A ⊃ B valid[ Γ ]

    app : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B valid[ Γ ] → Δ ⊢ A valid[ Γ ]
                      → Δ ⊢ B valid[ Γ ]

    mvar : ∀ {A Δ Γ} → Δ ∋ ⟪⊫ A ⟫
                     → Δ ⊢ A valid[ Γ ]

    box : ∀ {A Δ Γ} → Δ ⊢ A valid[ ∙ ]
                    → Δ ⊢ □ A valid[ Γ ]

    letbox : ∀ {A B Δ Γ} → Δ ⊢ □ A valid[ Γ ] → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]
                         → Δ ⊢ B valid[ Γ ]


infix 3 _⊢_allvalid[_]
_⊢_allvalid[_] : List Assert → List Prop → List Prop → Set
Δ ⊢ Ξ allvalid[ Γ ] = All (\ A → Δ ⊢ A valid[ Γ ]) Ξ


infix 3 _⊢_allvalid*
_⊢_allvalid* : List Assert → List Assert → Set
Δ ⊢ Ξ allvalid* = All (\ { ⟪⊫ A ⟫ → Δ ⊢ A valid[ ∙ ] }) Ξ


--------------------------------------------------------------------------------


ren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⊢ A valid[ Γ ]
                   → Δ ⊢ A valid[ Γ′ ]
ren η (var i)      = var (ren∋ η i)
ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
ren η (mvar i)     = mvar i
ren η (box 𝒟)      = box 𝒟
ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren η ℰ)


rens : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⊢ Ξ allvalid[ Γ ]
                    → Δ ⊢ Ξ allvalid[ Γ′ ]
rens η ξ = maps (ren η) ξ


--------------------------------------------------------------------------------


mren : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⊢ A valid[ Γ ]
                    → Δ′ ⊢ A valid[ Γ ]
mren η (var i)      = var i
mren η (lam 𝒟)      = lam (mren η 𝒟)
mren η (app 𝒟 ℰ)    = app (mren η 𝒟) (mren η ℰ)
mren η (mvar i)     = mvar (ren∋ η i)
mren η (box 𝒟)      = box (mren η 𝒟)
mren η (letbox 𝒟 ℰ) = letbox (mren η 𝒟) (mren (keep η) ℰ)


mrens : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⊢ Ξ allvalid[ Γ ]
                     → Δ′ ⊢ Ξ allvalid[ Γ ]
mrens η ξ = maps (mren η) ξ


mrens* : ∀ {Δ Δ′ Ξ} → Δ′ ⊇ Δ → Δ ⊢ Ξ allvalid*
                    → Δ′ ⊢ Ξ allvalid*
mrens* η ξ = maps (mren η) ξ


--------------------------------------------------------------------------------


wk : ∀ {B A Δ Γ} → Δ ⊢ A valid[ Γ ]
                 → Δ ⊢ A valid[ Γ , B ]
wk 𝒟 = ren (drop id) 𝒟


vz : ∀ {A Δ Γ} → Δ ⊢ A valid[ Γ , A ]
vz = var zero


wks : ∀ {A Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                  → Δ ⊢ Ξ allvalid[ Γ , A ]
wks ξ = rens (drop id) ξ


lifts : ∀ {A Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                    → Δ ⊢ Ξ , A allvalid[ Γ , A ]
lifts ξ = wks ξ , vz


vars : ∀ {Δ Γ Γ′} → Γ′ ⊇ Γ
                  → Δ ⊢ Γ allvalid[ Γ′ ]
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {Δ Γ} → Δ ⊢ Γ allvalid[ Γ ]
ids = vars id


--------------------------------------------------------------------------------


mwk : ∀ {B A Δ Γ} → Δ ⊢ A valid[ Γ ]
                  → Δ , ⟪⊫ B ⟫ ⊢ A valid[ Γ ]
mwk 𝒟 = mren (drop id) 𝒟


mvz : ∀ {A Δ Γ} → Δ , ⟪⊫ A ⟫ ⊢ A valid[ Γ ]
mvz = mvar zero


mwks : ∀ {A Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                   → Δ , ⟪⊫ A ⟫ ⊢ Ξ allvalid[ Γ ]
mwks ξ = mrens (drop id) ξ


mwks* : ∀ {A Δ Ξ} → Δ ⊢ Ξ allvalid*
                  → Δ , ⟪⊫ A ⟫ ⊢ Ξ allvalid*
mwks* ξ = mrens* (drop id) ξ


mlifts* : ∀ {A Δ Ξ} → Δ ⊢ Ξ allvalid*
                    → Δ , ⟪⊫ A ⟫ ⊢ Ξ , ⟪⊫ A ⟫ allvalid*
mlifts* ξ = mwks* ξ , mvz


mvars* : ∀ {Δ Δ′} → Δ′ ⊇ Δ
                  → Δ′ ⊢ Δ allvalid*
mvars* done     = ∙
mvars* (drop η) = mwks* (mvars* η)
mvars* (keep η) = mlifts* (mvars* η)


mids* : ∀ {Δ} → Δ ⊢ Δ allvalid*
mids* = mvars* id


--------------------------------------------------------------------------------


sub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid[ Γ ] → Δ ⊢ A valid[ Ξ ]
                  → Δ ⊢ A valid[ Γ ]
sub ξ (var i)      = get ξ i
sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (mvar i)     = mvar i
sub ξ (box 𝒟)      = box 𝒟
sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)


subs : ∀ {Δ Γ Ξ Ψ} → Δ ⊢ Ξ allvalid[ Γ ] → Δ ⊢ Ψ allvalid[ Ξ ]
                   → Δ ⊢ Ψ allvalid[ Γ ]
subs ξ ψ = maps (sub ξ) ψ


--------------------------------------------------------------------------------


msub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid* → Ξ ⊢ A valid[ Γ ]
                   → Δ ⊢ A valid[ Γ ]
msub ξ (var i)      = var i
msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
msub ξ (mvar i)     = sub ∙ (get ξ i)
msub ξ (box 𝒟)      = box (msub ξ 𝒟)
msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts* ξ) ℰ)


msubs : ∀ {Δ Γ Ξ Ψ} → Δ ⊢ Ξ allvalid* → Ξ ⊢ Ψ allvalid[ Γ ]
                    → Δ ⊢ Ψ allvalid[ Γ ]
msubs ξ ψ = maps (msub ξ) ψ


msubs* : ∀ {Δ Ξ Ψ} → Δ ⊢ Ξ allvalid* → Ξ ⊢ Ψ allvalid*
                   → Δ ⊢ Ψ allvalid*
msubs* ξ ψ = maps (msub ξ) ψ


--------------------------------------------------------------------------------


unlam : ∀ {Δ Γ A B} → Δ ⊢ A ⊃ B valid[ Γ ]
                    → Δ ⊢ B valid[ Γ , A ]
unlam 𝒟 = app (wk 𝒟) vz


cut : ∀ {Δ Γ A B} → Δ ⊢ A valid[ Γ ] → Δ ⊢ B valid[ Γ , A ]
                  → Δ ⊢ B valid[ Γ ]
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


pseudocut : ∀ {Δ Γ A B} → Δ ⊢ A valid[ Γ ] → Δ ⊢ B valid[ Γ , A ]
                        → Δ ⊢ B valid[ Γ ]
pseudocut 𝒟 ℰ = app (lam ℰ) 𝒟


pseudosub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid[ Γ ] → Δ ⊢ A valid[ Ξ ]
                        → Δ ⊢ A valid[ Γ ]
pseudosub ∙       𝒟 = ren bot⊇ 𝒟
pseudosub (ξ , 𝒞) 𝒟 = app (pseudosub ξ (lam 𝒟)) 𝒞


exch : ∀ {Δ Γ A B C} → Δ ⊢ C valid[ Γ , A , B ]
                     → Δ ⊢ C valid[ Γ , B , A ]
exch 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------


vau : ∀ {Δ Γ A B} → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]
                  → Δ ⊢ B valid[ Γ , □ A ]
vau 𝒟 = letbox vz (wk 𝒟)


unvau : ∀ {Δ Γ A B} → Δ ⊢ B valid[ Γ , □ A ]
                    → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]
unvau 𝒟 = app (lam (mwk 𝒟)) (box mvz)


axiomK : ∀ {A B Δ Γ} → Δ ⊢ □ (A ⊃ B) valid[ Γ ] → Δ ⊢ □ A valid[ Γ ]
                     → Δ ⊢ □ B valid[ Γ ]
axiomK 𝒟 ℰ = letbox 𝒟 (letbox (mwk ℰ) (box (app (mwk mvz) mvz)))


axiomT : ∀ {A Δ Γ} → Δ ⊢ □ A valid[ Γ ]
                   → Δ ⊢ A valid[ Γ ]
axiomT 𝒟 = letbox 𝒟 mvz


axiom4 : ∀ {A Δ Γ} → Δ ⊢ □ A valid[ Γ ]
                   → Δ ⊢ □ □ A valid[ Γ ]
axiom4 𝒟 = letbox 𝒟 (box (box mvz))


mcut : ∀ {Δ Γ A B} → Δ ⊢ A valid[ ∙ ] → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]
                   → Δ ⊢ B valid[ Γ ]
mcut 𝒟 ℰ = msub (mids* , 𝒟) ℰ


pseudomcut : ∀ {Δ Γ A B} → Δ ⊢ A valid[ ∙ ] → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]
                   → Δ ⊢ B valid[ Γ ]
pseudomcut 𝒟 ℰ = letbox (box 𝒟) ℰ


pseudomsub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid* → Ξ ⊢ A valid[ Γ ]
                         → Δ ⊢ A valid[ Γ ]
pseudomsub ∙       𝒟 = mren bot⊇ 𝒟
pseudomsub (ξ , 𝒞) 𝒟 = app (pseudomsub ξ (lam (vau 𝒟))) (box 𝒞)


mexch : ∀ {Δ Γ A B C} → Δ , ⟪⊫ A ⟫ , ⟪⊫ B ⟫ ⊢ C valid[ Γ ]
                      → Δ , ⟪⊫ B ⟫ , ⟪⊫ A ⟫ ⊢ C valid[ Γ ]
mexch 𝒟 = unvau (unvau (exch (vau (vau 𝒟))))


--------------------------------------------------------------------------------


module IPL→S4
  where
    ⌈_⌉ : IPL.Prop → Prop
    ⌈ IPL.ι P ⌉   = ι P
    ⌈ A IPL.⊃ B ⌉ = ⌈ A ⌉ ⊃ ⌈ B ⌉

    ⌈_⌉* : List IPL.Prop → List Prop
    ⌈ Γ ⌉* = map ⌈_⌉ Γ

    ↑∋ : ∀ {Γ A} → Γ ∋ A
                 → ⌈ Γ ⌉* ∋ ⌈ A ⌉
    ↑∋ zero    = zero
    ↑∋ (suc i) = suc (↑∋ i)

    ↑ : ∀ {Δ Γ A} → Γ IPL.⊢ A true
                  → Δ ⊢ ⌈ A ⌉ valid[ ⌈ Γ ⌉* ]
    ↑ (IPL.var i)   = var (↑∋ i)
    ↑ (IPL.lam 𝒟)   = lam (↑ 𝒟)
    ↑ (IPL.app 𝒟 ℰ) = app (↑ 𝒟) (↑ ℰ)


module S4→IPL
  where
    ⌊_⌋ : Prop → IPL.Prop
    ⌊ ι P ⌋   = IPL.ι P
    ⌊ A ⊃ B ⌋ = ⌊ A ⌋ IPL.⊃ ⌊ B ⌋
    ⌊ □ A ⌋   = ⌊ A ⌋

    ⌊_⌋* : List Prop → List IPL.Prop
    ⌊ Γ ⌋* = map ⌊_⌋ Γ

    ⌊_⌋** : List Assert → List IPL.Prop
    ⌊ Δ ⌋** = map (\ { ⟪⊫ A ⟫ → ⌊ A ⌋ }) Δ

    ↓∋ : ∀ {Γ A} → Γ ∋ A
                 → ⌊ Γ ⌋* ∋ ⌊ A ⌋
    ↓∋ zero    = zero
    ↓∋ (suc i) = suc (↓∋ i)

    ↓∋* : ∀ {Δ A} → Δ ∋ ⟪⊫ A ⟫
                  → ⌊ Δ ⌋** ∋ ⌊ A ⌋
    ↓∋* zero    = zero
    ↓∋* (suc i) = suc (↓∋* i)

    ↓ : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
                  → ⌊ Δ ⌋** ⧺ ⌊ Γ ⌋* IPL.⊢ ⌊ A ⌋ true
    ↓ {Δ = Δ} (var i)      = IPL.ren (ldrops ⌊ Δ ⌋** id) (IPL.var (↓∋ i))
    ↓         (lam 𝒟)      = IPL.lam (↓ 𝒟)
    ↓         (app 𝒟 ℰ)    = IPL.app (↓ 𝒟) (↓ ℰ)
    ↓ {Γ = Γ} (mvar i)     = IPL.ren (rdrops ⌊ Γ ⌋* id) (IPL.var (↓∋* i))
    ↓ {Γ = Γ} (box 𝒟)      = IPL.ren (rdrops ⌊ Γ ⌋* id) (↓ 𝒟)
    ↓ {Γ = Γ} (letbox 𝒟 ℰ) = IPL.cut (↓ 𝒟) (IPL.pull ⌊ Γ ⌋* (↓ ℰ))


--------------------------------------------------------------------------------
