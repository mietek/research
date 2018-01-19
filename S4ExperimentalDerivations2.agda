module S4ExperimentalDerivations2 where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions
import S4Derivations as S4


--------------------------------------------------------------------------------


infix 3 _⨾_⊢_true
data _⨾_⊢_true : List Prop → List Prop → Prop → Set
  where
    vz : ∀ {A Δ Γ} → Δ ⨾ Γ , A ⊢ A true

    wk : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true
                     → Δ ⨾ Γ , B ⊢ A true

    cut : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true → Δ ⨾ Γ , A ⊢ B true
                      → Δ ⨾ Γ ⊢ B true

    lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A ⊢ B true
                      → Δ ⨾ Γ ⊢ A ⊃ B true

    unlam : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true
                        → Δ ⨾ Γ , A ⊢ B true

    mvz : ∀ {A Δ Γ} → Δ , A ⨾ Γ ⊢ A true

    mwk : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true
                      → Δ , B ⨾ Γ ⊢ A true

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


wks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢ Ξ true*
                  → Δ ⨾ Γ , A ⊢ Ξ true*
wks ξ = maps wk ξ


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


mwks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢ Ξ true*
                   → Δ , A ⨾ Γ ⊢ Ξ true*
mwks ξ = maps mwk ξ


mwks₁ : ∀ {A Δ Ξ} → Δ ⊢ Ξ valid*
                  → Δ , A ⊢ Ξ valid*
mwks₁ ξ = maps mwk ξ


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


vau : ∀ {Δ Γ A B} → Δ , A ⨾ Γ ⊢ B true
                  → Δ ⨾ Γ , □ A ⊢ B true
vau 𝒟 = letbox vz (wk 𝒟)


unvau : ∀ {Δ Γ A B} → Δ ⨾ Γ , □ A ⊢ B true
                    → Δ , A ⨾ Γ ⊢ B true
unvau 𝒟 = cut (box mvz) (mwk 𝒟)


vaus : ∀ {Δ Γ A Ξ} → Δ , A ⨾ Γ ⊢ Ξ true*
                   → Δ ⨾ Γ , □ A ⊢ Ξ true*
vaus 𝒟 = maps vau 𝒟


sub : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢ Ξ true* → Δ ⨾ Ξ ⊢ A true
                  → Δ ⨾ Γ ⊢ A true
sub (ξ , 𝒞) vz           = 𝒞
sub (ξ , 𝒞) (wk 𝒟)       = sub ξ 𝒟
sub ξ       (cut 𝒟 ℰ)    = cut (sub ξ 𝒟) (sub (lifts ξ) ℰ)
sub ξ       (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub (ξ , 𝒞) (unlam 𝒟)    = cut 𝒞 (unlam (sub ξ 𝒟))
sub ξ       mvz          = mvz
sub ξ       (mwk 𝒟)      = unvau (sub (vaus ξ) 𝒟)  -- NOTE: Interesting
sub ξ       (box 𝒟)      = box 𝒟
sub ξ       (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)


--------------------------------------------------------------------------------


mcut′ : ∀ {Δ Γ A B} → Δ ⨾ ∙ ⊢ A true → Δ , A ⨾ Γ ⊢ B true
                    → Δ ⨾ Γ ⊢ B true
mcut′ 𝒟 ℰ = letbox (box 𝒟) ℰ


msub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ valid* → Ξ ⨾ Γ ⊢ A true
                   → Δ ⨾ Γ ⊢ A true
msub ξ       vz           = vz
msub ξ       (wk 𝒟)       = wk (msub ξ 𝒟)
msub ξ       (cut 𝒟 ℰ)    = cut (msub ξ 𝒟) (msub ξ ℰ)
msub ξ       (lam 𝒟)      = lam (msub ξ 𝒟)
msub ξ       (unlam 𝒟)    = unlam (msub ξ 𝒟)
msub (ξ , 𝒞) mvz          = mcut′ 𝒞 mvz
msub (ξ , 𝒞) (mwk 𝒟)      = msub ξ 𝒟
msub ξ       (box 𝒟)      = box (msub ξ 𝒟)
msub ξ       (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts₁ ξ) ℰ)


--------------------------------------------------------------------------------


var : ∀ {A Δ Γ} → Γ ∋ A
                → Δ ⨾ Γ ⊢ A true
var zero    = vz
var (suc i) = wk (var i)


app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true → Δ ⨾ Γ ⊢ A true
                  → Δ ⨾ Γ ⊢ B true
app 𝒟 ℰ = cut ℰ (unlam 𝒟)


--------------------------------------------------------------------------------


mvar : ∀ {A Δ Γ} → Δ ∋ A
                 → Δ ⨾ Γ ⊢ A true
mvar zero    = mvz
mvar (suc i) = mwk (mvar i)


--------------------------------------------------------------------------------


↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
              → Δ S4.⨾ Γ ⊢ A true
↓ vz           = S4.vz
↓ (wk 𝒟)       = S4.wk (↓ 𝒟)
↓ (cut 𝒟 ℰ)    = S4.cut (↓ 𝒟) (↓ ℰ)
↓ (lam 𝒟)      = S4.lam (↓ 𝒟)
↓ (unlam 𝒟)    = S4.unlam (↓ 𝒟)
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
