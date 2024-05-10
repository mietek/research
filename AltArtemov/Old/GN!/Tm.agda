module AltArtemov.Old.GN!.Tm where

open import AltArtemov.Library.Fin public


data Tm (g : ℕ) : ℕ → Set where
  VAR  : ∀ {n} → Fin g → Tm g n
  LAM  : ∀ {n} → Tm (suc g) n → Tm g n
  APP  : ∀ {n} → Tm g n → Tm g n → Tm g n
  PAIR : ∀ {n} → Tm g n → Tm g n → Tm g n
  FST  : ∀ {n} → Tm g n → Tm g n
  SND  : ∀ {n} → Tm g n → Tm g n
  UP   : ∀ {n} → Tm g n → Tm g n
  DOWN : ∀ {n} → Tm g n → Tm g n
  !_   : ∀ {n} → Tm g n → Tm g (suc n)

ren-tm : ∀ {g g′ n} → g′ ≥ g → Tm g n → Tm g′ n
ren-tm h (VAR i)    = VAR (ren-fin h i)
ren-tm h (LAM t)    = LAM (ren-tm (lift h) t)
ren-tm h (APP t u)  = APP (ren-tm h t) (ren-tm h u)
ren-tm h (PAIR t u) = PAIR (ren-tm h t) (ren-tm h u)
ren-tm h (FST t)    = FST (ren-tm h t)
ren-tm h (SND t)    = SND (ren-tm h t)
ren-tm h (UP t)     = UP (ren-tm h t)
ren-tm h (DOWN t)   = DOWN (ren-tm h t)
ren-tm h (! t)      = ! (ren-tm h t)

wk-tm : ∀ {g n} → Tm g n → Tm (suc g) n
wk-tm = ren-tm ≥wk

wk*-tm : ∀ {g n} → Tm 0 n → Tm g n
wk*-tm = ren-tm ≥to

ren-tm-id : ∀ {g n} (t : Tm g n) → ren-tm ≥id t ≡ t
ren-tm-id (VAR i)    = cong VAR (ren-fin-id i)
ren-tm-id (LAM t)    = cong LAM (ren-tm-id t)
ren-tm-id (APP t u)  = cong₂ APP (ren-tm-id t) (ren-tm-id u)
ren-tm-id (PAIR t u) = cong₂ PAIR (ren-tm-id t) (ren-tm-id u)
ren-tm-id (FST t)    = cong FST (ren-tm-id t)
ren-tm-id (SND t)    = cong SND (ren-tm-id t)
ren-tm-id (UP t)     = cong UP (ren-tm-id t)
ren-tm-id (DOWN t)   = cong DOWN (ren-tm-id t)
ren-tm-id (! t)      = cong !_ (ren-tm-id t)

ren-tm-○ : ∀ {g g′ g″ n} (h′ : g″ ≥ g′) (h : g′ ≥ g) (t : Tm g n) →
             ren-tm h′ (ren-tm h t) ≡ ren-tm (h′ ○ h) t
ren-tm-○ h′ h (VAR i)    = cong VAR (ren-fin-○ h′ h i)
ren-tm-○ h′ h (LAM t)    = cong LAM (ren-tm-○ (lift h′) (lift h) t)
ren-tm-○ h′ h (APP t u)  = cong₂ APP (ren-tm-○ h′ h t) (ren-tm-○ h′ h u)
ren-tm-○ h′ h (PAIR t u) = cong₂ PAIR (ren-tm-○ h′ h t) (ren-tm-○ h′ h u)
ren-tm-○ h′ h (FST t)    = cong FST (ren-tm-○ h′ h t)
ren-tm-○ h′ h (SND t)    = cong SND (ren-tm-○ h′ h t)
ren-tm-○ h′ h (UP t)     = cong UP (ren-tm-○ h′ h t)
ren-tm-○ h′ h (DOWN t)   = cong DOWN (ren-tm-○ h′ h t)
ren-tm-○ h′ h (! t)      = cong !_ (ren-tm-○ h′ h t)
