module SimpleS4Derivations where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions


--------------------------------------------------------------------------------


-- We read “B₁, …, Bₘ ⨾ A₁, …, Aₙ ⊢ A” as “from the assumptions that A₁ is
-- true, …, and that Aₙ is true, and that B₁ is valid, …, and that Bₘ is
-- valid, we deduce that A is true”.

infix 3 _⨾_⊢_
data _⨾_⊢_ : List Validity → List Truth → Truth → Set
  where
    var : ∀ {A Δ Γ} → Γ ∋ A true
                    → Δ ⨾ Γ ⊢ A true

    lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A true ⊢ B true
                      → Δ ⨾ Γ ⊢ A ⊃ B true

    app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true → Δ ⨾ Γ ⊢ A true
                      → Δ ⨾ Γ ⊢ B true

    mvar : ∀ {A Δ Γ} → Δ ∋ A valid
                     → Δ ⨾ Γ ⊢ A true

    box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                    → Δ ⨾ Γ ⊢ □ A true

    letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ □ A true → Δ , A valid ⨾ Γ ⊢ B true
                         → Δ ⨾ Γ ⊢ B true


infix 3 _⨾_⊢⋆_
_⨾_⊢⋆_ : List Validity → List Truth → List Truth → Set
Δ ⨾ Γ ⊢⋆ Ξ = All (Δ ⨾ Γ ⊢_) Ξ


--------------------------------------------------------------------------------


-- We read “A₁, …, Aₙ ⊢₁ A” as “from the assumptions that A₁ is valid, …,
-- and that Aₙ is valid, we deduce that A is valid”.

infix 3 _⊢₁_
_⊢₁_ : List Validity → Validity → Set
Δ ⊢₁ A valid = Δ ⨾ ∙ ⊢ A true


infix 3 _⊢⋆₁_
_⊢⋆₁_ : List Validity → List Validity → Set
Δ ⊢⋆₁ Ξ = All (Δ ⊢₁_) Ξ


--------------------------------------------------------------------------------


ren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ A true
                   → Δ ⨾ Γ′ ⊢ A true
ren η (var i)      = var (ren∋ η i)
ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
ren η (mvar i)     = mvar i
ren η (box 𝒟)      = box 𝒟
ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren η ℰ)


rens : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢⋆ Ξ
                    → Δ ⨾ Γ′ ⊢⋆ Ξ
rens η ξ = maps (ren η) ξ


--------------------------------------------------------------------------------


wk : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ A true
                 → Δ ⨾ Γ , B true ⊢ A true
wk 𝒟 = ren (drop id) 𝒟


vz : ∀ {A Δ Γ} → Δ ⨾ Γ , A true ⊢ A true
vz = var zero


wks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                  → Δ ⨾ Γ , A true ⊢⋆ Ξ
wks ξ = rens (drop id) ξ


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


mren : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ A true
                    → Δ′ ⨾ Γ ⊢ A true
mren η (var i)      = var i
mren η (lam 𝒟)      = lam (mren η 𝒟)
mren η (app 𝒟 ℰ)    = app (mren η 𝒟) (mren η ℰ)
mren η (mvar i)     = mvar (ren∋ η i)
mren η (box 𝒟)      = box (mren η 𝒟)
mren η (letbox 𝒟 ℰ) = letbox (mren η 𝒟) (mren (keep η) ℰ)


mrens : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢⋆ Ξ
                     → Δ′ ⨾ Γ ⊢⋆ Ξ
mrens η ξ = maps (mren η) ξ


mrens₁ : ∀ {Δ Δ′ Ξ} → Δ′ ⊇ Δ → Δ ⊢⋆₁ Ξ
                    → Δ′ ⊢⋆₁ Ξ
mrens₁ η ξ = maps (mren η) ξ


--------------------------------------------------------------------------------


mwk : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ A true
                  → Δ , B valid ⨾ Γ ⊢ A true
mwk 𝒟 = mren (drop id) 𝒟


mvz : ∀ {A Δ Γ} → Δ , A valid ⨾ Γ ⊢ A true
mvz = mvar zero


mwks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                   → Δ , A valid ⨾ Γ ⊢⋆ Ξ
mwks ξ = mrens (drop id) ξ


mwks₁ : ∀ {A Δ Ξ} → Δ ⊢⋆₁ Ξ
                  → Δ , A valid ⊢⋆₁ Ξ
mwks₁ ξ = mrens₁ (drop id) ξ


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


sub : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢⋆ Ξ → Δ ⨾ Ξ ⊢ A true
                  → Δ ⨾ Γ ⊢ A true
sub ξ (var i)      = get ξ i
sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (mvar i)     = mvar i
sub ξ (box 𝒟)      = box 𝒟
sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)


subs : ∀ {Δ Γ Ξ Ψ} → Δ ⨾ Γ ⊢⋆ Ξ → Δ ⨾ Ξ ⊢⋆ Ψ
                   → Δ ⨾ Γ ⊢⋆ Ψ
subs ξ ψ = maps (sub ξ) ψ


cut : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A true → Δ ⨾ Γ , A true ⊢ B true
                  → Δ ⨾ Γ ⊢ B true
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


--------------------------------------------------------------------------------


msub : ∀ {Δ Γ Ξ A} → Δ ⊢⋆₁ Ξ → Ξ ⨾ Γ ⊢ A true
                   → Δ ⨾ Γ ⊢ A true
msub ξ (var i)      = var i
msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
msub ξ (mvar i)     = sub ∙ (get ξ i)
msub ξ (box 𝒟)      = box (msub ξ 𝒟)
msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts₁ ξ) ℰ)


msubs : ∀ {Δ Γ Ξ Ψ} → Δ ⊢⋆₁ Ξ → Ξ ⨾ Γ ⊢⋆ Ψ
                    → Δ ⨾ Γ ⊢⋆ Ψ
msubs ξ ψ = maps (msub ξ) ψ


msubs₁ : ∀ {Δ Ξ Ψ} → Δ ⊢⋆₁ Ξ → Ξ ⊢⋆₁ Ψ
                   → Δ ⊢⋆₁ Ψ
msubs₁ ξ ψ = maps (msub ξ) ψ


mcut : ∀ {Δ Γ A B} → Δ ⊢₁ A valid → Δ , A valid ⨾ Γ ⊢ B true
                   → Δ ⨾ Γ ⊢ B true
mcut 𝒟 ℰ = msub (mids₁ , 𝒟) ℰ


--------------------------------------------------------------------------------


unlam : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A ⊃ B true
                    → Δ ⨾ Γ , A true ⊢ B true
unlam 𝒟 = app (wk 𝒟) vz


exch : ∀ {Δ Γ A B C} → Δ ⨾ Γ , A true , B true ⊢ C true
                     → Δ ⨾ Γ , B true , A true ⊢ C true
exch 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


up : ∀ {Δ Γ A B} → Δ ⨾ Γ , □ A true ⊢ B true
                 → Δ , A valid ⨾ Γ ⊢ B true
up 𝒟 = app (lam (mwk 𝒟)) (box mvz)


down : ∀ {Δ Γ A B} → Δ , A valid ⨾ Γ ⊢ B true
                   → Δ ⨾ Γ , □ A true ⊢ B true
down 𝒟 = letbox vz (wk 𝒟)


mexch : ∀ {Δ Γ A B C} → Δ , A valid , B valid ⨾ Γ ⊢ C true
                      → Δ , B valid , A valid ⨾ Γ ⊢ C true
mexch 𝒟 = up (up (exch (down (down 𝒟))))


--------------------------------------------------------------------------------
