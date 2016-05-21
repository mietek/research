module AltArtemov.G.Tm where

open import AltArtemov.Base public


data Tm (g : ℕ) : Set where
  VAR[_]  : ℕ → Fin g → Tm g
  LAM[_]  : ℕ → Tm (suc g) → Tm g
  APP[_]  : ℕ → Tm g → Tm g → Tm g
  PAIR[_] : ℕ → Tm g → Tm g → Tm g
  FST[_]  : ℕ → Tm g → Tm g
  SND[_]  : ℕ → Tm g → Tm g
  UP[_]   : ℕ → Tm g → Tm g
  DOWN[_] : ℕ → Tm g → Tm g

!_ : ∀ {g} → Tm g → Tm g
! VAR[ n ] i    = VAR[ suc n ] i
! LAM[ n ] t    = LAM[ suc n ] (! t)
! APP[ n ] t u  = APP[ suc n ] (! t) (! u)
! PAIR[ n ] t u = PAIR[ suc n ] (! t) (! u)
! FST[ n ] t    = FST[ suc n ] (! t)
! SND[ n ] t    = SND[ suc n ] (! t)
! UP[ n ] t     = UP[ suc n ] (! t)
! DOWN[ n ] t   = DOWN[ suc n ] (! t)

ren-tm : ∀ {g g′} → g′ ≥ g → Tm g → Tm g′
ren-tm h (VAR[ n ] i)    = VAR[ n ] (ren-fin h i)
ren-tm h (LAM[ n ] t)    = LAM[ n ] (ren-tm (lift h) t)
ren-tm h (APP[ n ] t u)  = APP[ n ] (ren-tm h t) (ren-tm h u)
ren-tm h (PAIR[ n ] t u) = PAIR[ n ] (ren-tm h t) (ren-tm h u)
ren-tm h (FST[ n ] t)    = FST[ n ] (ren-tm h t)
ren-tm h (SND[ n ] t)    = SND[ n ] (ren-tm h t)
ren-tm h (UP[ n ] t)     = UP[ n ] (ren-tm h t)
ren-tm h (DOWN[ n ] t)   = DOWN[ n ] (ren-tm h t)

wk-tm : ∀ {g} → Tm g → Tm (suc g)
wk-tm = ren-tm ≥wk

wk*-tm : ∀ {g} → Tm 0 → Tm g
wk*-tm = ren-tm ≥to

ren-tm-id : ∀ {g} (t : Tm g) → ren-tm ≥id t ≡ t
ren-tm-id (VAR[ n ] i)    = cong VAR[ n ] (ren-fin-id i)
ren-tm-id (LAM[ n ] t)    = cong LAM[ n ] (ren-tm-id t)
ren-tm-id (APP[ n ] t u)  = cong₂ APP[ n ] (ren-tm-id t) (ren-tm-id u)
ren-tm-id (PAIR[ n ] t u) = cong₂ PAIR[ n ] (ren-tm-id t) (ren-tm-id u)
ren-tm-id (FST[ n ] t)    = cong FST[ n ] (ren-tm-id t)
ren-tm-id (SND[ n ] t)    = cong SND[ n ] (ren-tm-id t)
ren-tm-id (UP[ n ] t)     = cong UP[ n ] (ren-tm-id t)
ren-tm-id (DOWN[ n ] t)   = cong DOWN[ n ] (ren-tm-id t)

ren-tm-○ : ∀ {g g′ g″} (h′ : g″ ≥ g′) (h : g′ ≥ g) (t : Tm g) →
             ren-tm h′ (ren-tm h t) ≡ ren-tm (h′ ○ h) t
ren-tm-○ h′ h (VAR[ n ] i)    = cong VAR[ n ] (ren-fin-○ h′ h i)
ren-tm-○ h′ h (LAM[ n ] t)    = cong LAM[ n ] (ren-tm-○ (lift h′) (lift h) t)
ren-tm-○ h′ h (APP[ n ] t u)  = cong₂ APP[ n ] (ren-tm-○ h′ h t) (ren-tm-○ h′ h u)
ren-tm-○ h′ h (PAIR[ n ] t u) = cong₂ PAIR[ n ] (ren-tm-○ h′ h t) (ren-tm-○ h′ h u)
ren-tm-○ h′ h (FST[ n ] t)    = cong FST[ n ] (ren-tm-○ h′ h t)
ren-tm-○ h′ h (SND[ n ] t)    = cong SND[ n ] (ren-tm-○ h′ h t)
ren-tm-○ h′ h (UP[ n ] t)     = cong UP[ n ] (ren-tm-○ h′ h t)
ren-tm-○ h′ h (DOWN[ n ] t)   = cong DOWN[ n ] (ren-tm-○ h′ h t)
