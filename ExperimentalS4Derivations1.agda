module ExperimentalS4Derivations1 where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions
import SimpleS4Derivations as S4


--------------------------------------------------------------------------------


infix 3 _⨾_⊢_
data _⨾_⊢_ : List Validity → List Truth → Truth → Set
  where
    vz : ∀ {A Δ Γ} → Δ ⨾ Γ , A true ⊢ A true

    wk : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true
                     → Δ ⨾ Γ , B true ⊢ A true

    lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A true ⊢ B true
                      → Δ ⨾ Γ ⊢ A ⊃ B true

    app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true → Δ ⨾ Γ ⊢ A true
                      → Δ ⨾ Γ ⊢ B true

    mvz : ∀ {A Δ Γ} → Δ , A valid ⨾ Γ ⊢ A true

    mwk : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true
                      → Δ , B valid ⨾ Γ ⊢ A true

    box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                    → Δ ⨾ Γ ⊢ □ A true

    letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ □ A true → Δ , A valid ⨾ Γ ⊢ B true
                         → Δ ⨾ Γ ⊢ B true


infix 3 _⨾_⊢⋆_
_⨾_⊢⋆_ : List Validity → List Truth → List Truth → Set
Δ ⨾ Γ ⊢⋆ Ξ = All (Δ ⨾ Γ ⊢_) Ξ


--------------------------------------------------------------------------------


infix 3 _⊢₁_
_⊢₁_ : List Validity → Validity → Set
Δ ⊢₁ A valid = Δ ⨾ ∙ ⊢ A true


infix 3 _⊢⋆₁_
_⊢⋆₁_ : List Validity → List Validity → Set
Δ ⊢⋆₁ Ξ = All (Δ ⊢₁_) Ξ


--------------------------------------------------------------------------------


wks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                  → Δ ⨾ Γ , A true ⊢⋆ Ξ
wks ξ = maps wk ξ


lifts : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                    → Δ ⨾ Γ , A true ⊢⋆ Ξ , A true
lifts ξ = wks ξ , vz


vars : ∀ {Δ Γ Γ′} → Γ′ ⊇ Γ
                  → Δ ⨾ Γ′ ⊢⋆ Γ
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {Δ Γ} → Δ ⨾ Γ ⊢⋆ Γ
ids = vars id


--------------------------------------------------------------------------------


mwks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                   → Δ , A valid ⨾ Γ ⊢⋆ Ξ
mwks ξ = maps mwk ξ


mwks₁ : ∀ {A Δ Ξ} → Δ ⊢⋆₁ Ξ
                  → Δ , A valid ⊢⋆₁ Ξ
mwks₁ ξ = maps mwk ξ


mlifts₁ : ∀ {A Δ Ξ} → Δ ⊢⋆₁ Ξ
                    → Δ , A valid ⊢⋆₁ Ξ , A valid
mlifts₁ ξ = mwks₁ ξ , mvz


mvars₁ : ∀ {Δ Δ′} → Δ′ ⊇ Δ
                  → Δ′ ⊢⋆₁ Δ
mvars₁ done     = ∙
mvars₁ (drop η) = mwks₁ (mvars₁ η)
mvars₁ (keep η) = mlifts₁ (mvars₁ η)


mids₁ : ∀ {Δ} → Δ ⊢⋆₁ Δ
mids₁ = mvars₁ id


--------------------------------------------------------------------------------


vau : ∀ {Δ Γ A B} → Δ , A valid ⨾ Γ ⊢ B true
                  → Δ ⨾ Γ , □ A true ⊢ B true
vau 𝒟 = letbox vz (wk 𝒟)


unvau : ∀ {Δ Γ A B} → Δ ⨾ Γ , □ A true ⊢ B true
                    → Δ , A valid ⨾ Γ ⊢ B true
unvau 𝒟 = app (lam (mwk 𝒟)) (box mvz)


vaus : ∀ {Δ Γ A Ξ} → Δ , A valid ⨾ Γ ⊢⋆ Ξ
                   → Δ ⨾ Γ , □ A true ⊢⋆ Ξ
vaus 𝒟 = maps vau 𝒟


sub : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢⋆ Ξ → Δ ⨾ Ξ ⊢ A true
                  → Δ ⨾ Γ ⊢ A true
sub (ξ , 𝒞) vz           = 𝒞
sub (ξ , 𝒞) (wk 𝒟)       = sub ξ 𝒟
sub ξ       (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub ξ       (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ       mvz          = mvz
sub ξ       (mwk 𝒟)      = unvau (sub (vaus ξ) 𝒟)  -- NOTE: Interesting
sub ξ       (box 𝒟)      = box 𝒟
sub ξ       (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)


subs : ∀ {Δ Γ Ξ Ψ} → Δ ⨾ Γ ⊢⋆ Ξ → Δ ⨾ Ξ ⊢⋆ Ψ
                   → Δ ⨾ Γ ⊢⋆ Ψ
subs ξ ψ = maps (sub ξ) ψ


--------------------------------------------------------------------------------


msub : ∀ {Δ Γ Ξ A} → Δ ⊢⋆₁ Ξ → Ξ ⨾ Γ ⊢ A true
                   → Δ ⨾ Γ ⊢ A true
msub ξ       vz           = vz
msub ξ       (wk 𝒟)       = wk (msub ξ 𝒟)
msub ξ       (lam 𝒟)      = lam (msub ξ 𝒟)
msub ξ       (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
msub (ξ , 𝒞) mvz          = letbox (box 𝒞) mvz
msub (ξ , 𝒞) (mwk 𝒟)      = msub ξ 𝒟
msub ξ       (box 𝒟)      = box (msub ξ 𝒟)
msub ξ       (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts₁ ξ) ℰ)


msubs₁ : ∀ {Δ Ξ Ψ} → Δ ⊢⋆₁ Ξ → Ξ ⊢⋆₁ Ψ
                   → Δ ⊢⋆₁ Ψ
msubs₁ ξ ψ = maps (msub ξ) ψ


--------------------------------------------------------------------------------


ren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ A true
                   → Δ ⨾ Γ′ ⊢ A true
ren η 𝒟 = sub (vars η) 𝒟


rens : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢⋆ Ξ
                    → Δ ⨾ Γ′ ⊢⋆ Ξ
rens η ξ = maps (ren η) ξ


ren′ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ A true
                    → Δ ⨾ Γ′ ⊢ A true
ren′ (drop η) vz           = wk (ren′ η vz)
ren′ (keep η) vz           = vz
ren′ (drop η) (wk 𝒟)       = wk (ren′ η (wk 𝒟))
ren′ (keep η) (wk 𝒟)       = wk (ren′ η 𝒟)
ren′ η        (lam 𝒟)      = lam (ren′ (keep η) 𝒟)
ren′ η        (app 𝒟 ℰ)    = app (ren′ η 𝒟) (ren′ η ℰ)
ren′ η        mvz          = mvz
ren′ η        (mwk 𝒟)      = mwk (ren′ η 𝒟)
ren′ η        (box 𝒟)      = box 𝒟
ren′ η        (letbox 𝒟 ℰ) = letbox (ren′ η 𝒟) (ren′ η ℰ)


--------------------------------------------------------------------------------


mren : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ A true
                    → Δ′ ⨾ Γ ⊢ A true
mren η 𝒟 = msub (mvars₁ η) 𝒟


mrens : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢⋆ Ξ
                     → Δ′ ⨾ Γ ⊢⋆ Ξ
mrens η ξ = maps (mren η) ξ


mrens₁ : ∀ {Δ Δ′ Ξ} → Δ′ ⊇ Δ → Δ ⊢⋆₁ Ξ
                    → Δ′ ⊢⋆₁ Ξ
mrens₁ η ξ = maps (mren η) ξ


mren′ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ A true
                     → Δ′ ⨾ Γ ⊢ A true
mren′ η        vz           = vz
mren′ η        (wk 𝒟)       = wk (mren′ η 𝒟)
mren′ η        (lam 𝒟)      = lam (mren′ η 𝒟)
mren′ η        (app 𝒟 ℰ)    = app (mren′ η 𝒟) (mren′ η ℰ)
mren′ (drop η) mvz          = mwk (mren′ η mvz)
mren′ (keep η) mvz          = mvz
mren′ (drop η) (mwk 𝒟)      = mwk (mren′ η (mwk 𝒟))
mren′ (keep η) (mwk 𝒟)      = mwk (mren′ η 𝒟)
mren′ η        (box 𝒟)      = box (mren′ η 𝒟)
mren′ η        (letbox 𝒟 ℰ) = letbox (mren′ η 𝒟) (mren′ (keep η) ℰ)


--------------------------------------------------------------------------------


var : ∀ {A Δ Γ} → Γ ∋ A true
                → Δ ⨾ Γ ⊢ A true
var zero    = vz
var (suc i) = wk (var i)


unlam : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A ⊃ B true
                    → Δ ⨾ Γ , A true ⊢ B true
unlam 𝒟 = app (wk 𝒟) vz


cut : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A true → Δ ⨾ Γ , A true ⊢ B true
                  → Δ ⨾ Γ ⊢ B true
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


cut′ : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A true → Δ ⨾ Γ , A true ⊢ B true
                   → Δ ⨾ Γ ⊢ B true
cut′ 𝒟 ℰ = app (lam ℰ) 𝒟


wkn : ∀ {Δ Γ A} → Δ ⨾ ∙ ⊢ A true
                → Δ ⨾ Γ ⊢ A true
wkn {Γ = ∙}          𝒟 = 𝒟
wkn {Γ = Γ , B true} 𝒟 = wk (wkn 𝒟)


sub′ : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢⋆ Ξ → Δ ⨾ Ξ ⊢ A true
                   → Δ ⨾ Γ ⊢ A true
sub′ ∙       𝒟 = wkn 𝒟
sub′ (ξ , 𝒞) 𝒟 = app (sub′ ξ (lam 𝒟)) 𝒞


exch : ∀ {Δ Γ A B C} → Δ ⨾ Γ , A true , B true ⊢ C true
                     → Δ ⨾ Γ , B true , A true ⊢ C true
exch 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------


mvar : ∀ {A Δ Γ} → Δ ∋ A valid
                 → Δ ⨾ Γ ⊢ A true
mvar zero    = mvz
mvar (suc i) = mwk (mvar i)


unbox : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ □ A true
                  → Δ ⨾ Γ ⊢ A true
unbox 𝒟 = letbox (box (letbox 𝒟 mvz)) mvz


axiomK : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ □ (A ⊃ B) true → Δ ⨾ Γ ⊢ □ A true
                     → Δ ⨾ Γ ⊢ □ B true
axiomK 𝒟 ℰ = letbox 𝒟 (letbox (mwk ℰ) (box (app (mwk mvz) mvz)))


axiomT : ∀ {A Δ Γ} → Δ ⨾ Γ ⊢ □ A true
                   → Δ ⨾ Γ ⊢ A true
axiomT 𝒟 = letbox 𝒟 mvz


axiom4 : ∀ {A Δ Γ} → Δ ⨾ Γ ⊢ □ A true
                   → Δ ⨾ Γ ⊢ □ □ A true
axiom4 𝒟 = letbox 𝒟 (box (box mvz))


v→t : ∀ {A Δ Γ} → Δ ⊢₁ A valid
                 → Δ ⨾ Γ ⊢ A true
v→t 𝒟 = letbox (box 𝒟) mvz


t→v : ∀ {A Δ} → Δ ⨾ ∙ ⊢ A true
               → Δ ⊢₁ A valid
t→v 𝒟 = 𝒟


mcut : ∀ {Δ Γ A B} → Δ ⨾ ∙ ⊢ A true → Δ , A valid ⨾ Γ ⊢ B true
                   → Δ ⨾ Γ ⊢ B true
mcut 𝒟 ℰ = msub (mids₁ , 𝒟) ℰ


mcut′ : ∀ {Δ Γ A B} → Δ ⨾ ∙ ⊢ A true → Δ , A valid ⨾ Γ ⊢ B true
                    → Δ ⨾ Γ ⊢ B true
mcut′ 𝒟 ℰ = letbox (box 𝒟) ℰ


mwkn : ∀ {Δ Γ A} → ∙ ⨾ Γ ⊢ A true
                 → Δ ⨾ Γ ⊢ A true
mwkn {∙}           𝒟 = 𝒟
mwkn {Δ , B valid} 𝒟 = mwk (mwkn 𝒟)


msub′ : ∀ {Δ Γ Ξ A} → Δ ⊢⋆₁ Ξ → Ξ ⨾ Γ ⊢ A true
                    → Δ ⨾ Γ ⊢ A true
msub′ ∙       𝒟 = mwkn 𝒟
msub′ (ξ , 𝒞) 𝒟 = app (msub′ ξ (lam (vau 𝒟))) (box 𝒞)


mexch : ∀ {Δ Γ A B C} → Δ , A valid , B valid ⨾ Γ ⊢ C true
                      → Δ , B valid , A valid ⨾ Γ ⊢ C true
mexch 𝒟 = unvau (unvau (exch (vau (vau 𝒟))))


--------------------------------------------------------------------------------


↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
              → Δ S4.⨾ Γ ⊢ A true
↓ vz           = S4.vz
↓ (wk 𝒟)       = S4.wk (↓ 𝒟)
↓ (lam 𝒟)      = S4.lam (↓ 𝒟)
↓ (app 𝒟 ℰ)    = S4.app (↓ 𝒟) (↓ ℰ)
↓ mvz          = S4.mvz
↓ (mwk 𝒟)      = S4.mwk (↓ 𝒟)
↓ (box 𝒟)      = S4.box (↓ 𝒟)
↓ (letbox 𝒟 ℰ) = S4.letbox (↓ 𝒟) (↓ ℰ)


↑ : ∀ {Δ Γ A} → Δ S4.⨾ Γ ⊢ A true
              → Δ ⨾ Γ ⊢ A true
↑ (S4.var i)      = var i
↑ (S4.lam 𝒟)      = lam (↑ 𝒟)
↑ (S4.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
↑ (S4.mvar i)     = mvar i
↑ (S4.box 𝒟)      = box (↑ 𝒟)
↑ (S4.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)


--------------------------------------------------------------------------------
