module S4Derivations where

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


infix 3 _⨾_⊢_true
data _⨾_⊢_true : List Prop → List Prop → Prop → Set
  where
    var : ∀ {A Δ Γ} → Γ ∋ A
                    → Δ ⨾ Γ ⊢ A true

    lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A ⊢ B true
                      → Δ ⨾ Γ ⊢ A ⊃ B true

    app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true → Δ ⨾ Γ ⊢ A true
                      → Δ ⨾ Γ ⊢ B true

    mvar : ∀ {A Δ Γ} → Δ ∋ A
                     → Δ ⨾ Γ ⊢ A true

    box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                    → Δ ⨾ Γ ⊢ □ A true

    letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ □ A true → Δ , A ⨾ Γ ⊢ B true
                         → Δ ⨾ Γ ⊢ B true


infix 3 _⨾_⊢_alltrue
_⨾_⊢_alltrue : List Prop → List Prop → List Prop → Set
Δ ⨾ Γ ⊢ Ξ alltrue = All (Δ ⨾ Γ ⊢_true) Ξ


--------------------------------------------------------------------------------


infix 3 _⊢_valid
_⊢_valid : List Prop → Prop → Set
Δ ⊢ A valid = Δ ⨾ ∙ ⊢ A true


infix 3 _⊢_allvalid
_⊢_allvalid : List Prop → List Prop → Set
Δ ⊢ Ξ allvalid = All (Δ ⊢_valid) Ξ


--------------------------------------------------------------------------------


ren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ A true
                   → Δ ⨾ Γ′ ⊢ A true
ren η (var i)      = var (ren∋ η i)
ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
ren η (mvar i)     = mvar i
ren η (box 𝒟)      = box 𝒟
ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren η ℰ)


rens : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ Ξ alltrue
                    → Δ ⨾ Γ′ ⊢ Ξ alltrue
rens η ξ = maps (ren η) ξ


--------------------------------------------------------------------------------


mren : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ A true
                    → Δ′ ⨾ Γ ⊢ A true
mren η (var i)      = var i
mren η (lam 𝒟)      = lam (mren η 𝒟)
mren η (app 𝒟 ℰ)    = app (mren η 𝒟) (mren η ℰ)
mren η (mvar i)     = mvar (ren∋ η i)
mren η (box 𝒟)      = box (mren η 𝒟)
mren η (letbox 𝒟 ℰ) = letbox (mren η 𝒟) (mren (keep η) ℰ)


mrens : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ Ξ alltrue
                     → Δ′ ⨾ Γ ⊢ Ξ alltrue
mrens η ξ = maps (mren η) ξ


--------------------------------------------------------------------------------


wk : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ A true
                 → Δ ⨾ Γ , B ⊢ A true
wk 𝒟 = ren (drop id) 𝒟


vz : ∀ {A Δ Γ} → Δ ⨾ Γ , A ⊢ A true
vz = var zero


wks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢ Ξ alltrue
                  → Δ ⨾ Γ , A ⊢ Ξ alltrue
wks ξ = rens (drop id) ξ


lifts : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢ Ξ alltrue
                    → Δ ⨾ Γ , A ⊢ Ξ , A alltrue
lifts ξ = wks ξ , vz


vars : ∀ {Δ Γ Γ′} → Γ′ ⊇ Γ
                  → Δ ⨾ Γ′ ⊢ Γ alltrue
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {Δ Γ} → Δ ⨾ Γ ⊢ Γ alltrue
ids = vars id


--------------------------------------------------------------------------------


mwk : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ A true
                  → Δ , B ⨾ Γ ⊢ A true
mwk 𝒟 = mren (drop id) 𝒟


mvz : ∀ {A Δ Γ} → Δ , A ⨾ Γ ⊢ A true
mvz = mvar zero


mwks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢ Ξ alltrue
                   → Δ , A ⨾ Γ ⊢ Ξ alltrue
mwks ξ = mrens (drop id) ξ


mlifts : ∀ {A Δ Ξ} → Δ ⊢ Ξ allvalid
                   → Δ , A ⊢ Ξ , A allvalid
mlifts ξ = mwks ξ , mvz


mvars : ∀ {Δ Δ′} → Δ′ ⊇ Δ
                 → Δ′ ⊢ Δ allvalid
mvars done     = ∙
mvars (drop η) = mwks (mvars η)
mvars (keep η) = mlifts (mvars η)


mids : ∀ {Δ} → Δ ⊢ Δ allvalid
mids = mvars id


--------------------------------------------------------------------------------


sub : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢ Ξ alltrue → Δ ⨾ Ξ ⊢ A true
                  → Δ ⨾ Γ ⊢ A true
sub ξ (var i)      = get ξ i
sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (mvar i)     = mvar i
sub ξ (box 𝒟)      = box 𝒟
sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)


subs : ∀ {Δ Γ Ξ Ψ} → Δ ⨾ Γ ⊢ Ξ alltrue → Δ ⨾ Ξ ⊢ Ψ alltrue
                   → Δ ⨾ Γ ⊢ Ψ alltrue
subs ξ ψ = maps (sub ξ) ψ


--------------------------------------------------------------------------------


msub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid → Ξ ⨾ Γ ⊢ A true
                   → Δ ⨾ Γ ⊢ A true
msub ξ (var i)      = var i
msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
msub ξ (mvar i)     = sub ∙ (get ξ i)
msub ξ (box 𝒟)      = box (msub ξ 𝒟)
msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts ξ) ℰ)


msubs : ∀ {Δ Γ Ξ Ψ} → Δ ⊢ Ξ allvalid → Ξ ⨾ Γ ⊢ Ψ alltrue
                    → Δ ⨾ Γ ⊢ Ψ alltrue
msubs ξ ψ = maps (msub ξ) ψ


--------------------------------------------------------------------------------


unlam : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A ⊃ B true
                    → Δ ⨾ Γ , A ⊢ B true
unlam 𝒟 = app (wk 𝒟) vz


cut : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A true → Δ ⨾ Γ , A ⊢ B true
                  → Δ ⨾ Γ ⊢ B true
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


cut′ : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A true → Δ ⨾ Γ , A ⊢ B true
                   → Δ ⨾ Γ ⊢ B true
cut′ 𝒟 ℰ = app (lam ℰ) 𝒟


wkn : ∀ {Δ Γ A} → Δ ⨾ ∙ ⊢ A true
                → Δ ⨾ Γ ⊢ A true
wkn {Γ = ∙}     𝒟 = 𝒟
wkn {Γ = Γ , B} 𝒟 = wk (wkn 𝒟)


sub′ : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢ Ξ alltrue → Δ ⨾ Ξ ⊢ A true
                   → Δ ⨾ Γ ⊢ A true
sub′ ∙       𝒟 = wkn 𝒟
sub′ (ξ , 𝒞) 𝒟 = app (sub′ ξ (lam 𝒟)) 𝒞


exch : ∀ {Δ Γ A B C} → Δ ⨾ Γ , A , B ⊢ C true
                     → Δ ⨾ Γ , B , A ⊢ C true
exch 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------


unbox : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ □ A true
                  → Δ ⨾ Γ ⊢ A true  -- the built-in weakening obscures the true shape!
unbox 𝒟 = letbox (box (letbox 𝒟 mvz)) mvz


vau : ∀ {Δ Γ A B} → Δ , A ⨾ Γ ⊢ B true
                  → Δ ⨾ Γ , □ A ⊢ B true
vau 𝒟 = letbox vz (wk 𝒟)


unvau : ∀ {Δ Γ A B} → Δ ⨾ Γ , □ A ⊢ B true
                    → Δ , A ⨾ Γ ⊢ B true
unvau 𝒟 = app (lam (mwk 𝒟)) (box mvz)


axiomK : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ □ (A ⊃ B) true → Δ ⨾ Γ ⊢ □ A true
                     → Δ ⨾ Γ ⊢ □ B true
axiomK 𝒟 ℰ = letbox 𝒟 (letbox (mwk ℰ) (box (app (mwk mvz) mvz)))


axiomT : ∀ {A Δ Γ} → Δ ⨾ Γ ⊢ □ A true
                   → Δ ⨾ Γ ⊢ A true
axiomT 𝒟 = letbox 𝒟 mvz


axiom4 : ∀ {A Δ Γ} → Δ ⨾ Γ ⊢ □ A true
                   → Δ ⨾ Γ ⊢ □ □ A true
axiom4 𝒟 = letbox 𝒟 (box (box mvz))


v→t : ∀ {A Δ Γ} → Δ ⊢ A valid
                 → Δ ⨾ Γ ⊢ A true
v→t 𝒟 = letbox (box 𝒟) mvz


t→v : ∀ {A Δ} → Δ ⨾ ∙ ⊢ A true
               → Δ ⊢ A valid
t→v 𝒟 = 𝒟


mcut : ∀ {Δ Γ A B} → Δ ⨾ ∙ ⊢ A true → Δ , A ⨾ Γ ⊢ B true
                   → Δ ⨾ Γ ⊢ B true
mcut 𝒟 ℰ = msub (mids , 𝒟) ℰ


mcut′ : ∀ {Δ Γ A B} → Δ ⨾ ∙ ⊢ A true → Δ , A ⨾ Γ ⊢ B true
                    → Δ ⨾ Γ ⊢ B true
mcut′ 𝒟 ℰ = letbox (box 𝒟) ℰ


mwkn : ∀ {Δ Γ A} → ∙ ⨾ Γ ⊢ A true
                 → Δ ⨾ Γ ⊢ A true
mwkn {∙}     𝒟 = 𝒟
mwkn {Δ , B} 𝒟 = mwk (mwkn 𝒟)


msub′ : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid → Ξ ⨾ Γ ⊢ A true
                    → Δ ⨾ Γ ⊢ A true
msub′ ∙       𝒟 = mwkn 𝒟
msub′ (ξ , 𝒞) 𝒟 = app (msub′ ξ (lam (vau 𝒟))) (box 𝒞)


mexch : ∀ {Δ Γ A B C} → Δ , A , B ⨾ Γ ⊢ C true
                      → Δ , B , A ⨾ Γ ⊢ C true
mexch 𝒟 = unvau (unvau (exch (vau (vau 𝒟))))


--------------------------------------------------------------------------------


-- module IPL→S4
--   where
--     ⌈_⌉ : IPL.Prop → Prop
--     ⌈ IPL.BASE ⌉  = BASE
--     ⌈ A IPL.⊃ B ⌉ = ⌈ A ⌉ ⊃ ⌈ B ⌉


--     ⌈_⌉* : List IPL.Prop → List Prop
--     ⌈ Γ ⌉* = map ⌈_⌉ Γ


--     ↑∋ : ∀ {Γ A} → Γ ∋ A
--                  → ⌈ Γ ⌉* ∋ ⌈ A ⌉
--     ↑∋ zero    = zero
--     ↑∋ (suc i) = suc (↑∋ i)


--     ↑ : ∀ {Δ Γ A} → Γ IPL.⊢ A true
--                   → Δ ⨾ ⌈ Γ ⌉* ⊢ ⌈ A ⌉ true
--     ↑ (IPL.var i)   = var (↑∋ i)
--     ↑ (IPL.lam 𝒟)   = lam (↑ 𝒟)
--     ↑ (IPL.app 𝒟 ℰ) = app (↑ 𝒟) (↑ ℰ)


-- --------------------------------------------------------------------------------


-- module S4→IPL
--   where
--     ⌊_⌋ : Prop → IPL.Prop
--     ⌊ BASE ⌋  = IPL.BASE
--     ⌊ A ⊃ B ⌋ = ⌊ A ⌋ IPL.⊃ ⌊ B ⌋
--     ⌊ □ A ⌋   = ⌊ A ⌋


--     ⌊_⌋* : List Prop → List IPL.Prop
--     ⌊ Γ ⌋* = map ⌊_⌋ Γ


--     ↓∋ : ∀ {Γ A} → Γ ∋ A
--                  → ⌊ Γ ⌋* ∋ ⌊ A ⌋
--     ↓∋ zero    = zero
--     ↓∋ (suc i) = suc (↓∋ i)


--     ↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
--                   → ⌊ Δ ⌋* ⧺ ⌊ Γ ⌋* IPL.⊢ ⌊ A ⌋ true
--     ↓ {Δ = Δ} (var i)      = IPL.ren (ldrops ⌊ Δ ⌋* id⊇) (IPL.var (↓∋ i))
--     ↓         (lam 𝒟)      = IPL.lam (↓ 𝒟)
--     ↓         (app 𝒟 ℰ)    = IPL.app (↓ 𝒟) (↓ ℰ)
--     ↓ {Γ = Γ} (mvar i)     = IPL.ren (rdrops ⌊ Γ ⌋* id⊇) (IPL.var (↓∋ i))
--     ↓ {Γ = Γ} (box 𝒟)      = IPL.ren (rdrops ⌊ Γ ⌋* id⊇) (↓ 𝒟)
--     ↓ {Γ = Γ} (letbox 𝒟 ℰ) = IPL.cut (↓ 𝒟) (IPL.pull ⌊ Γ ⌋* (↓ ℰ))


-- --------------------------------------------------------------------------------
