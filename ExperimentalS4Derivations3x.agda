module ExperimentalS4Derivations3x where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions
import SimpleS4Derivations as S4


--------------------------------------------------------------------------------


mutual
  infix 3 _⨾_⊢_
  data _⨾_⊢_ : List Validity → List Truth → Truth → Set
    where
      vz : ∀ {A Δ Γ} → Δ ⨾ Γ , A true ⊢ A true
   
      wk : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true
                       → Δ ⨾ Γ , B true ⊢ A true
   
      cut : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true → Δ ⨾ Γ , A true ⊢ B true
                        → Δ ⨾ Γ ⊢ B true
   
      lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A true ⊢ B true
                        → Δ ⨾ Γ ⊢ A ⊃ B true
   
      unlam : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true
                          → Δ ⨾ Γ , A true ⊢ B true
       
      vau : ∀ {A B Δ Γ} → Δ , A valid ⨾ Γ ⊢ B true
                        → Δ ⨾ Γ , □ A true ⊢ B true

      unvau : ∀ {A B Δ Γ} → Δ ⨾ Γ , □ A true ⊢ B true
                          → Δ , A valid ⨾ Γ ⊢ B true
                       
      v→t : ∀ {A Δ Γ} → Δ ⊢₁ A valid
                       → Δ ⨾ Γ ⊢ A true

  infix 3 _⊢₁_
  data _⊢₁_ : List Validity → Validity → Set
    where
      t→v : ∀ {A Δ} → Δ ⨾ ∙ ⊢ A true
                     → Δ ⊢₁ A valid

      mvz₁ : ∀ {A Δ} → Δ , A valid ⊢₁ A valid

      mwk₁ : ∀ {A B Δ} → Δ ⊢₁ A valid
                       → Δ , B valid ⊢₁ A valid

      mcut₁ : ∀ {A B Δ} → Δ ⊢₁ A valid → Δ , A valid ⊢₁ B valid
                        → Δ ⊢₁ B valid


infix 3 _⨾_⊢⋆_
_⨾_⊢⋆_ : List Validity → List Truth → List Truth → Set
Δ ⨾ Γ ⊢⋆ Ξ = All (Δ ⨾ Γ ⊢_) Ξ


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


mwks₁ : ∀ {A Δ Ξ} → Δ ⊢⋆₁ Ξ
                  → Δ , A valid ⊢⋆₁ Ξ
mwks₁ ξ = maps mwk₁ ξ


mlifts₁ : ∀ {A Δ Ξ} → Δ ⊢⋆₁ Ξ
                    → Δ , A valid ⊢⋆₁ Ξ , A valid
mlifts₁ ξ = mwks₁ ξ , mvz₁


mvars₁ : ∀ {Δ Δ′} → Δ′ ⊇ Δ
                  → Δ′ ⊢⋆₁ Δ
mvars₁ done     = ∙
mvars₁ (drop η) = mwks₁ (mvars₁ η)
mvars₁ (keep η) = mlifts₁ (mvars₁ η)


mids₁ : ∀ {Δ} → Δ ⊢⋆₁ Δ
mids₁ = mvars₁ id


--------------------------------------------------------------------------------


mwk : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A true
                  → Δ , B valid ⨾ Γ ⊢ A true
mwk 𝒟 = unvau (wk 𝒟)


mwks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                   → Δ , A valid ⨾ Γ ⊢⋆ Ξ
mwks ξ = maps mwk ξ


vaus : ∀ {Δ Γ A Ξ} → Δ , A valid ⨾ Γ ⊢⋆ Ξ
                   → Δ ⨾ Γ , □ A true ⊢⋆ Ξ
vaus 𝒟 = maps vau 𝒟


-- NOTE: Similar shape to lift or cut

unnamed : ∀ {Δ Γ A Ξ} → Δ , A valid ⨾ Γ ⊢⋆ Ξ 
                      → Δ ⨾ Γ , □ A true ⊢⋆ Ξ , □ A true
unnamed 𝒟 = vaus 𝒟 , vz


sub : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢⋆ Ξ → Δ ⨾ Ξ ⊢ A true
                  → Δ ⨾ Γ ⊢ A true
sub (ξ , 𝒞) vz           = 𝒞
sub (ξ , 𝒞) (wk 𝒟)       = sub ξ 𝒟
sub ξ       (cut 𝒟 ℰ)    = cut (sub ξ 𝒟) (sub (lifts ξ) ℰ)
sub ξ       (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub (ξ , 𝒞) (unlam 𝒟)    = cut 𝒞 (unlam (sub ξ 𝒟))
sub (ξ , 𝒞) (vau 𝒟)      = cut 𝒞 (vau (sub (mwks ξ) 𝒟)) 
sub ξ       (unvau 𝒟)    = unvau (sub (unnamed ξ) 𝒟)  -- NOTE: Interesting
sub ξ       (v→t 𝒟)     = v→t 𝒟


--------------------------------------------------------------------------------


box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                → Δ ⨾ Γ ⊢ □ A true
box 𝒟 = v→t (mcut₁ (t→v 𝒟) (t→v (unvau vz)))


letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ □ A true → Δ , A valid ⨾ Γ ⊢ B true
                     → Δ ⨾ Γ ⊢ B true
letbox 𝒟 ℰ = cut 𝒟 (vau ℰ)


mcut′ : ∀ {Δ Γ A B} → Δ ⨾ ∙ ⊢ A true → Δ , A valid ⨾ Γ ⊢ B true
                    → Δ ⨾ Γ ⊢ B true
mcut′ 𝒟 ℰ = cut (box 𝒟) (vau ℰ) 


mutual
  msub : ∀ {Δ Γ Ξ A} → Δ ⊢⋆₁ Ξ → Ξ ⨾ Γ ⊢ A true
                     → Δ ⨾ Γ ⊢ A true
  msub ξ       vz           = vz
  msub ξ       (wk 𝒟)       = wk (msub ξ 𝒟)
  msub ξ       (cut 𝒟 ℰ)    = cut (msub ξ 𝒟) (msub ξ ℰ)
  msub ξ       (lam 𝒟)      = lam (msub ξ 𝒟)
  msub ξ       (unlam 𝒟)    = unlam (msub ξ 𝒟)
  msub ξ       (vau 𝒟)      = vau (msub (mlifts₁ ξ) 𝒟)
  msub (ξ , 𝒞) (unvau 𝒟)    = mcut′ (v→t 𝒞) (unvau (msub ξ 𝒟))  -- NOTE: Interesting
  msub ξ       (v→t 𝒟)     = v→t (msub₁ ξ 𝒟)

  msub₁ : ∀ {Δ Ξ A} → Δ ⊢⋆₁ Ξ → Ξ ⊢₁ A valid
                    → Δ ⊢₁ A valid
  msub₁ ξ       (t→v 𝒟)    = t→v (msub ξ 𝒟)
  msub₁ (ξ , 𝒞) mvz₁        = 𝒞
  msub₁ (ξ , 𝒞) (mwk₁ 𝒟)    = msub₁ ξ 𝒟
  msub₁ ξ       (mcut₁ 𝒟 ℰ) = mcut₁ (msub₁ ξ 𝒟) (msub₁ (mlifts₁ ξ) ℰ)


--------------------------------------------------------------------------------


var : ∀ {A Δ Γ} → Γ ∋ A true
                → Δ ⨾ Γ ⊢ A true
var zero    = vz
var (suc i) = wk (var i)


app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true → Δ ⨾ Γ ⊢ A true
                  → Δ ⨾ Γ ⊢ B true
app 𝒟 ℰ = cut ℰ (unlam 𝒟)


--------------------------------------------------------------------------------


mvz : ∀ {A Δ Γ} → Δ , A valid ⨾ Γ ⊢ A true
mvz = v→t mvz₁


mvar : ∀ {A Δ Γ} → Δ ∋ A valid
                 → Δ ⨾ Γ ⊢ A true
mvar zero    = mvz
mvar (suc i) = mwk (mvar i)


--------------------------------------------------------------------------------


mutual
  ↓ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ A true
                → Δ S4.⨾ Γ ⊢ A true
  ↓ vz           = S4.vz
  ↓ (wk 𝒟)       = S4.wk (↓ 𝒟)
  ↓ (cut 𝒟 ℰ)    = S4.cut (↓ 𝒟) (↓ ℰ)
  ↓ (lam 𝒟)      = S4.lam (↓ 𝒟)
  ↓ (unlam 𝒟)    = S4.unlam (↓ 𝒟)
  ↓ (vau 𝒟)      = S4.vau (↓ 𝒟)
  ↓ (unvau 𝒟)    = S4.unvau (↓ 𝒟)
  ↓ (v→t 𝒟)     = S4.v→t (↓₁ 𝒟)

  ↓₁ : ∀ {Δ A} → Δ ⊢₁ A valid
               → Δ S4.⊢₁ A valid
  ↓₁ (t→v 𝒟)    = S4.t→v (↓ 𝒟)
  ↓₁ mvz₁        = S4.mvz
  ↓₁ (mwk₁ 𝒟)    = S4.mwk (↓₁ 𝒟)
  ↓₁ (mcut₁ 𝒟 ℰ) = S4.mcut (↓₁ 𝒟) (↓₁ ℰ)               


↑ : ∀ {Δ Γ A} → Δ S4.⨾ Γ ⊢ A true
              → Δ ⨾ Γ ⊢ A true
↑ (S4.var i)      = var i
↑ (S4.lam 𝒟)      = lam (↑ 𝒟)
↑ (S4.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
↑ (S4.mvar i)     = mvar i
↑ (S4.box 𝒟)      = box (↑ 𝒟)
↑ (S4.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)


--------------------------------------------------------------------------------
