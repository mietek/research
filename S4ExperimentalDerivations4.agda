module S4ExperimentalDerivations4 where

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

    box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                    → Δ ⨾ Γ ⊢ □ A true

    unbox : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ □ A true
                      → Δ ⨾ Γ ⊢ A true

    vau : ∀ {A B Δ Γ} → Δ , A ⨾ Γ ⊢ B true
                      → Δ ⨾ Γ , □ A ⊢ B true

    unvau : ∀ {A B Δ Γ} → Δ ⨾ Γ , □ A ⊢ B true
                        → Δ , A ⨾ Γ ⊢ B true


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


mvz : ∀ {A Δ Γ} → Δ , A ⨾ Γ ⊢ A true
mvz = unbox (unvau vz)


mwk : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true
                  → Δ , B ⨾ Γ ⊢ A true
mwk 𝒟 = unvau (wk 𝒟)


mwks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢ Ξ true*
                   → Δ , A ⨾ Γ ⊢ Ξ true*
mwks ξ = maps mwk ξ


mlifts : ∀ {A Δ Ξ} → Δ ⊢ Ξ valid*
                   → Δ , A ⊢ Ξ , A valid*
mlifts ξ = mwks ξ , mvz


mvars : ∀ {Δ Δ′} → Δ′ ⊇ Δ
                 → Δ′ ⊢ Δ valid*
mvars done     = ∙
mvars (drop η) = mwks (mvars η)
mvars (keep η) = mlifts (mvars η)


mids : ∀ {Δ} → Δ ⊢ Δ valid*
mids = mvars id


--------------------------------------------------------------------------------


vaus : ∀ {Δ Γ A Ξ} → Δ , A ⨾ Γ ⊢ Ξ true*
                   → Δ ⨾ Γ , □ A ⊢ Ξ true*
vaus 𝒟 = maps vau 𝒟


-- NOTE: Similar shape to lift or cut

unnamed : ∀ {Δ Γ A Ξ} → Δ , A ⨾ Γ ⊢ Ξ true*
                      → Δ ⨾ Γ , □ A ⊢ Ξ , □ A true*
unnamed 𝒟 = vaus 𝒟 , vz


sub : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢ Ξ true* → Δ ⨾ Ξ ⊢ A true
                  → Δ ⨾ Γ ⊢ A true
sub (ξ , 𝒞) vz        = 𝒞
sub (ξ , 𝒞) (wk 𝒟)    = sub ξ 𝒟
sub ξ       (cut 𝒟 ℰ) = cut (sub ξ 𝒟) (sub (lifts ξ) ℰ)
sub ξ       (lam 𝒟)   = lam (sub (lifts ξ) 𝒟)
sub (ξ , 𝒞) (unlam 𝒟) = cut 𝒞 (unlam (sub ξ 𝒟))
sub ξ       (box 𝒟)   = box 𝒟
sub ξ       (unbox 𝒟) = unbox 𝒟
sub (ξ , 𝒞) (vau 𝒟)   = cut 𝒞 (vau (sub (mwks ξ) 𝒟))
sub ξ       (unvau 𝒟) = unvau (sub (unnamed ξ) 𝒟)  -- NOTE: Interesting


--------------------------------------------------------------------------------


msub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ valid* → Ξ ⨾ Γ ⊢ A true
                   → Δ ⨾ Γ ⊢ A true
msub ξ       vz         = vz
msub ξ       (wk 𝒟)     = wk (msub ξ 𝒟)
msub ξ       (cut 𝒟 ℰ)  = cut (msub ξ 𝒟) (msub ξ ℰ)
msub ξ       (lam 𝒟)    = lam (msub ξ 𝒟)
msub ξ       (unlam 𝒟)  = unlam (msub ξ 𝒟)
msub ξ       (box 𝒟)    = box (msub ξ 𝒟)
msub ξ       (unbox 𝒟)  = unbox (msub ξ 𝒟)
msub ξ       (vau 𝒟)    = vau (msub (mlifts ξ) 𝒟)
msub (ξ , 𝒞) (unvau 𝒟)  = cut (box 𝒞) (msub ξ 𝒟) -- NOTE: Interesting


--------------------------------------------------------------------------------


var : ∀ {A Δ Γ} → Γ ∋ A
                → Δ ⨾ Γ ⊢ A true
var zero    = vz
var (suc i) = wk (var i)


app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true → Δ ⨾ Γ ⊢ A true
                  → Δ ⨾ Γ ⊢ B true
app 𝒟 ℰ = cut ℰ (unlam 𝒟)


mvar : ∀ {A Δ Γ} → Δ ∋ A
                 → Δ ⨾ Γ ⊢ A true
mvar zero    = mvz
mvar (suc i) = mwk (mvar i)


letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ □ A true → Δ , A ⨾ Γ ⊢ B true
                     → Δ ⨾ Γ ⊢ B true
letbox 𝒟 ℰ = cut 𝒟 (vau ℰ)


--------------------------------------------------------------------------------


↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
              → Δ S4.⨾ Γ ⊢ A true
↓ vz        = S4.vz
↓ (wk 𝒟)    = S4.wk (↓ 𝒟)
↓ (cut 𝒟 ℰ) = S4.cut (↓ 𝒟) (↓ ℰ)
↓ (lam 𝒟)   = S4.lam (↓ 𝒟)
↓ (unlam 𝒟) = S4.unlam (↓ 𝒟)
↓ (box 𝒟)   = S4.box (↓ 𝒟)
↓ (unbox 𝒟) = S4.unbox (↓ 𝒟)
↓ (vau 𝒟)   = S4.vau (↓ 𝒟)
↓ (unvau 𝒟) = S4.unvau (↓ 𝒟)


↑ : ∀ {Δ Γ A} → Δ S4.⨾ Γ ⊢ A true
              → Δ ⨾ Γ ⊢ A true
↑ (S4.var i)      = var i
↑ (S4.lam 𝒟)      = lam (↑ 𝒟)
↑ (S4.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
↑ (S4.mvar i)     = mvar i
↑ (S4.box 𝒟)      = box (↑ 𝒟)
↑ (S4.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)


--------------------------------------------------------------------------------
