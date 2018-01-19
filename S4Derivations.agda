module S4Derivations where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions


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


infix 3 _⨾_⊢_true*
_⨾_⊢_true* : List Prop → List Prop → List Prop → Set
Δ ⨾ Γ ⊢ Ξ true* = All (Δ ⨾ Γ ⊢_true) Ξ


--------------------------------------------------------------------------------


infix 3 _⊢_valid
_⊢_valid : List Prop → Prop → Set
Δ ⊢ A valid = Δ ⨾ ∙ ⊢ A true


infix 3 _⊢_valid*
_⊢_valid* : List Prop → List Prop → Set
Δ ⊢ Ξ valid* = All (Δ ⊢_valid) Ξ


--------------------------------------------------------------------------------


ren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ A true
                   → Δ ⨾ Γ′ ⊢ A true
ren η (var i)      = var (ren∋ η i)
ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
ren η (mvar i)     = mvar i
ren η (box 𝒟)      = box 𝒟
ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren η ℰ)


rens : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ Ξ true*
                    → Δ ⨾ Γ′ ⊢ Ξ true*
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


mrens : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ Ξ true*
                     → Δ′ ⨾ Γ ⊢ Ξ true*
mrens η ξ = maps (mren η) ξ


mrens₁ : ∀ {Δ Δ′ Ξ} → Δ′ ⊇ Δ → Δ ⊢ Ξ valid*
                    → Δ′ ⊢ Ξ valid*
mrens₁ η ξ = maps (mren η) ξ


--------------------------------------------------------------------------------


wk : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ A true
                 → Δ ⨾ Γ , B ⊢ A true
wk 𝒟 = ren (drop id) 𝒟


vz : ∀ {A Δ Γ} → Δ ⨾ Γ , A ⊢ A true
vz = var zero


wks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢ Ξ true*
                  → Δ ⨾ Γ , A ⊢ Ξ true*
wks ξ = rens (drop id) ξ


lifts : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢ Ξ true*
                    → Δ ⨾ Γ , A ⊢ Ξ , A true*
lifts ξ = wks ξ , vz


vars : ∀ {Δ Γ Γ′} → Γ′ ⊇ Γ
                  → Δ ⨾ Γ′ ⊢ Γ true*
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {Δ Γ} → Δ ⨾ Γ ⊢ Γ true*
ids = vars id


--------------------------------------------------------------------------------


mwk : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ A true
                  → Δ , B ⨾ Γ ⊢ A true
mwk 𝒟 = mren (drop id) 𝒟


mvz : ∀ {A Δ Γ} → Δ , A ⨾ Γ ⊢ A true
mvz = mvar zero


mwks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢ Ξ true*
                   → Δ , A ⨾ Γ ⊢ Ξ true*
mwks ξ = mrens (drop id) ξ


mwks₁ : ∀ {A Δ Ξ} → Δ ⊢ Ξ valid*
                  → Δ , A ⊢ Ξ valid*
mwks₁ ξ = mrens₁ (drop id) ξ


mlifts₁ : ∀ {A Δ Ξ} → Δ ⊢ Ξ valid*
                    → Δ , A ⊢ Ξ , A valid*
mlifts₁ ξ = mwks₁ ξ , mvz


mvars₁ : ∀ {Δ Δ′} → Δ′ ⊇ Δ
                  → Δ′ ⊢ Δ valid*
mvars₁ done     = ∙
mvars₁ (drop η) = mwks₁ (mvars₁ η)
mvars₁ (keep η) = mlifts₁ (mvars₁ η)


mids₁ : ∀ {Δ} → Δ ⊢ Δ valid*
mids₁ = mvars₁ id


--------------------------------------------------------------------------------


sub : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢ Ξ true* → Δ ⨾ Ξ ⊢ A true
                  → Δ ⨾ Γ ⊢ A true
sub ξ (var i)      = get ξ i
sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (mvar i)     = mvar i
sub ξ (box 𝒟)      = box 𝒟
sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)


subs : ∀ {Δ Γ Ξ Ψ} → Δ ⨾ Γ ⊢ Ξ true* → Δ ⨾ Ξ ⊢ Ψ true*
                   → Δ ⨾ Γ ⊢ Ψ true*
subs ξ ψ = maps (sub ξ) ψ


--------------------------------------------------------------------------------


msub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ valid* → Ξ ⨾ Γ ⊢ A true
                   → Δ ⨾ Γ ⊢ A true
msub ξ (var i)      = var i
msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
msub ξ (mvar i)     = sub ∙ (get ξ i)
msub ξ (box 𝒟)      = box (msub ξ 𝒟)
msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts₁ ξ) ℰ)


msubs : ∀ {Δ Γ Ξ Ψ} → Δ ⊢ Ξ valid* → Ξ ⨾ Γ ⊢ Ψ true*
                    → Δ ⨾ Γ ⊢ Ψ true*
msubs ξ ψ = maps (msub ξ) ψ


msubs₁ : ∀ {Δ Ξ Ψ} → Δ ⊢ Ξ valid* → Ξ ⊢ Ψ valid*
                   → Δ ⊢ Ψ valid*
msubs₁ ξ ψ = maps (msub ξ) ψ


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


sub′ : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢ Ξ true* → Δ ⨾ Ξ ⊢ A true
                   → Δ ⨾ Γ ⊢ A true
sub′ ∙       𝒟 = wkn 𝒟
sub′ (ξ , 𝒞) 𝒟 = app (sub′ ξ (lam 𝒟)) 𝒞


exch : ∀ {Δ Γ A B C} → Δ ⨾ Γ , A , B ⊢ C true
                     → Δ ⨾ Γ , B , A ⊢ C true
exch 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------


unbox : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ □ A true
                  → Δ ⨾ Γ ⊢ A true
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
mcut 𝒟 ℰ = msub (mids₁ , 𝒟) ℰ


mcut′ : ∀ {Δ Γ A B} → Δ ⨾ ∙ ⊢ A true → Δ , A ⨾ Γ ⊢ B true
                    → Δ ⨾ Γ ⊢ B true
mcut′ 𝒟 ℰ = letbox (box 𝒟) ℰ


mwkn : ∀ {Δ Γ A} → ∙ ⨾ Γ ⊢ A true
                 → Δ ⨾ Γ ⊢ A true
mwkn {∙}     𝒟 = 𝒟
mwkn {Δ , B} 𝒟 = mwk (mwkn 𝒟)


msub′ : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ valid* → Ξ ⨾ Γ ⊢ A true
                    → Δ ⨾ Γ ⊢ A true
msub′ ∙       𝒟 = mwkn 𝒟
msub′ (ξ , 𝒞) 𝒟 = app (msub′ ξ (lam (vau 𝒟))) (box 𝒞)


mexch : ∀ {Δ Γ A B C} → Δ , A , B ⨾ Γ ⊢ C true
                      → Δ , B , A ⨾ Γ ⊢ C true
mexch 𝒟 = unvau (unvau (exch (vau (vau 𝒟))))


--------------------------------------------------------------------------------
