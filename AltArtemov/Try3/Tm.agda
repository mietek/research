module AltArtemov.Try3.Tm where

open import AltArtemov.Library.Fin public


data Tm (g : ℕ) : ℕ → Set where
  VAR  : ∀ {k} → Fin g → Tm g k
  LAM  : ∀ {k} → Tm (suc g) k → Tm g k
  APP  : ∀ {k} → Tm g k → Tm g k → Tm g k
  PAIR : ∀ {k} → Tm g k → Tm g k → Tm g k
  FST  : ∀ {k} → Tm g k → Tm g k
  SND  : ∀ {k} → Tm g k → Tm g k
  UP   : ∀ {k} → Tm g k → Tm g (suc k)
  DOWN : ∀ {k} → Tm g (suc k) → Tm g k

!_ : ∀ {g k} → Tm g k → Tm g (suc k)
! VAR i      = VAR i
! LAM t      = LAM (! t)
! APP t₁ t₂  = APP (! t₁) (! t₂)
! PAIR t₁ t₂ = PAIR (! t₁) (! t₂)
! FST t      = FST (! t)
! SND t      = SND (! t)
! UP t       = UP (! t)
! DOWN t     = DOWN (! t)

¡_ : ∀ {g k} → Tm g (suc k) → Tm g k
¡ VAR x      = VAR x
¡ LAM t      = LAM (¡ t)
¡ APP t₁ t₂  = APP (¡ t₁) (¡ t₂)
¡ PAIR t₁ t₂ = PAIR (¡ t₁) (¡ t₂)
¡ FST t      = FST (¡ t)
¡ SND t      = SND (¡ t)
¡_ {k = zero}  (UP t) = t
¡_ {k = suc k} (UP t) = UP (¡ t)
¡ DOWN t     = DOWN (¡ t)

!¡-id : ∀ {g k} (t : Tm g k) → ¡ (! t) ≡ t
!¡-id (VAR x)      = refl
!¡-id (LAM t)      = cong LAM (!¡-id t)
!¡-id (APP t₁ t₂)  = cong₂ APP (!¡-id t₁) (!¡-id t₂)
!¡-id (PAIR t₁ t₂) = cong₂ PAIR (!¡-id t₁) (!¡-id t₂)
!¡-id (FST t)      = cong FST (!¡-id t)
!¡-id (SND t)      = cong SND (!¡-id t)
!¡-id (UP t)       = cong UP (!¡-id t)
!¡-id (DOWN t)     = cong DOWN (!¡-id t)

ren-tm : ∀ {g g′ k} → g′ ≥ g → Tm g k → Tm g′ k
ren-tm h (VAR i)      = VAR (ren-fin h i)
ren-tm h (LAM t)      = LAM (ren-tm (lift h) t)
ren-tm h (APP t₁ t₂)  = APP (ren-tm h t₁) (ren-tm h t₂)
ren-tm h (PAIR t₁ t₂) = PAIR (ren-tm h t₁) (ren-tm h t₂)
ren-tm h (FST t)      = FST (ren-tm h t)
ren-tm h (SND t)      = SND (ren-tm h t)
ren-tm h (UP t)       = UP (ren-tm h t)
ren-tm h (DOWN t)     = DOWN (ren-tm h t)

wk-tm : ∀ {g k} → Tm g k → Tm (suc g) k
wk-tm = ren-tm ≥wk

wk*-tm : ∀ {g k} → Tm 0 k → Tm g k
wk*-tm = ren-tm ≥to

ren-tm-id : ∀ {g k} (t : Tm g k) → ren-tm ≥id t ≡ t
ren-tm-id (VAR i)      = cong VAR (ren-fin-id i)
ren-tm-id (LAM t)      = cong LAM (ren-tm-id t)
ren-tm-id (APP t₁ t₂)  = cong₂ APP (ren-tm-id t₁) (ren-tm-id t₂)
ren-tm-id (PAIR t₁ t₂) = cong₂ PAIR (ren-tm-id t₁) (ren-tm-id t₂)
ren-tm-id (FST t)      = cong FST (ren-tm-id t)
ren-tm-id (SND t)      = cong SND (ren-tm-id t)
ren-tm-id (UP t)       = cong UP (ren-tm-id t)
ren-tm-id (DOWN t)     = cong DOWN (ren-tm-id t)

ren-tm-○ : ∀ {g g′ g″ k} (h′ : g″ ≥ g′) (h : g′ ≥ g) (t : Tm g k) →
             ren-tm h′ (ren-tm h t) ≡ ren-tm (h′ ○ h) t
ren-tm-○ h′ h (VAR i)      = cong VAR (ren-fin-○ h′ h i)
ren-tm-○ h′ h (LAM t)      = cong LAM (ren-tm-○ (lift h′) (lift h) t)
ren-tm-○ h′ h (APP t₁ t₂)  = cong₂ APP (ren-tm-○ h′ h t₁) (ren-tm-○ h′ h t₂)
ren-tm-○ h′ h (PAIR t₁ t₂) = cong₂ PAIR (ren-tm-○ h′ h t₁) (ren-tm-○ h′ h t₂)
ren-tm-○ h′ h (FST t)      = cong FST (ren-tm-○ h′ h t)
ren-tm-○ h′ h (SND t)      = cong SND (ren-tm-○ h′ h t)
ren-tm-○ h′ h (UP t)       = cong UP (ren-tm-○ h′ h t)
ren-tm-○ h′ h (DOWN t)     = cong DOWN (ren-tm-○ h′ h t)
