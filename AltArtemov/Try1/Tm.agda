module A201605.AltArtemov.Try1.Tm where

open import A201605.AltArtemov.Library.Fin public


data Tm (g : ℕ) : ℕ → Set where
  VAR  : ∀ {n} → Fin g → Tm g n
  LAM  : ∀ {n} → Tm (suc g) n → Tm g n
  APP  : ∀ {n} → Tm g n → Tm g n → Tm g n
  PAIR : ∀ {n} → Tm g n → Tm g n → Tm g n
  FST  : ∀ {n} → Tm g n → Tm g n
  SND  : ∀ {n} → Tm g n → Tm g n
  UP   : ∀ {n} → Tm g n → Tm g n
  DOWN : ∀ {n} → Tm g n → Tm g n

!_ : ∀ {g n} → Tm g n → Tm g (suc n)
! VAR i      = VAR i
! LAM t      = LAM (! t)
! APP t₁ t₂  = APP (! t₁) (! t₂)
! PAIR t₁ t₂ = PAIR (! t₁) (! t₂)
! FST t      = FST (! t)
! SND t      = SND (! t)
! UP t       = UP (! t)
! DOWN t     = DOWN (! t)

¡_ : ∀ {g n} → Tm g (suc n) → Tm g n
¡ VAR x      = VAR x
¡ LAM t      = LAM (¡ t)
¡ APP t₁ t₂  = APP (¡ t₁) (¡ t₂)
¡ PAIR t₁ t₂ = PAIR (¡ t₁) (¡ t₂)
¡ FST t      = FST (¡ t)
¡ SND t      = SND (¡ t)
¡ UP t       = UP (¡ t)
¡ DOWN t     = DOWN (¡ t)

!¡-id : ∀ {g n} (t : Tm g n) → ¡ (! t) ≡ t
!¡-id (VAR x)      = refl
!¡-id (LAM t)      = cong LAM (!¡-id t)
!¡-id (APP t₁ t₂)  = cong₂ APP (!¡-id t₁) (!¡-id t₂)
!¡-id (PAIR t₁ t₂) = cong₂ PAIR (!¡-id t₁) (!¡-id t₂)
!¡-id (FST t)      = cong FST (!¡-id t)
!¡-id (SND t)      = cong SND (!¡-id t)
!¡-id (UP t)       = cong UP (!¡-id t)
!¡-id (DOWN t)     = cong DOWN (!¡-id t)

ren-tm : ∀ {g g′ n} → g′ ≥ g → Tm g n → Tm g′ n
ren-tm h (VAR i)      = VAR (ren-fin h i)
ren-tm h (LAM t)      = LAM (ren-tm (lift h) t)
ren-tm h (APP t₁ t₂)  = APP (ren-tm h t₁) (ren-tm h t₂)
ren-tm h (PAIR t₁ t₂) = PAIR (ren-tm h t₁) (ren-tm h t₂)
ren-tm h (FST t)      = FST (ren-tm h t)
ren-tm h (SND t)      = SND (ren-tm h t)
ren-tm h (UP t)       = UP (ren-tm h t)
ren-tm h (DOWN t)     = DOWN (ren-tm h t)

wk-tm : ∀ {g n} → Tm g n → Tm (suc g) n
wk-tm = ren-tm ≥wk

wk*-tm : ∀ {g n} → Tm 0 n → Tm g n
wk*-tm = ren-tm ≥to

ren-tm-id : ∀ {g n} (t : Tm g n) → ren-tm ≥id t ≡ t
ren-tm-id (VAR i)      = cong VAR (ren-fin-id i)
ren-tm-id (LAM t)      = cong LAM (ren-tm-id t)
ren-tm-id (APP t₁ t₂)  = cong₂ APP (ren-tm-id t₁) (ren-tm-id t₂)
ren-tm-id (PAIR t₁ t₂) = cong₂ PAIR (ren-tm-id t₁) (ren-tm-id t₂)
ren-tm-id (FST t)      = cong FST (ren-tm-id t)
ren-tm-id (SND t)      = cong SND (ren-tm-id t)
ren-tm-id (UP t)       = cong UP (ren-tm-id t)
ren-tm-id (DOWN t)     = cong DOWN (ren-tm-id t)

ren-tm-○ : ∀ {g g′ g″ n} (h′ : g″ ≥ g′) (h : g′ ≥ g) (t : Tm g n) →
             ren-tm h′ (ren-tm h t) ≡ ren-tm (h′ ○ h) t
ren-tm-○ h′ h (VAR i)      = cong VAR (ren-fin-○ h′ h i)
ren-tm-○ h′ h (LAM t)      = cong LAM (ren-tm-○ (lift h′) (lift h) t)
ren-tm-○ h′ h (APP t₁ t₂)  = cong₂ APP (ren-tm-○ h′ h t₁) (ren-tm-○ h′ h t₂)
ren-tm-○ h′ h (PAIR t₁ t₂) = cong₂ PAIR (ren-tm-○ h′ h t₁) (ren-tm-○ h′ h t₂)
ren-tm-○ h′ h (FST t)      = cong FST (ren-tm-○ h′ h t)
ren-tm-○ h′ h (SND t)      = cong SND (ren-tm-○ h′ h t)
ren-tm-○ h′ h (UP t)       = cong UP (ren-tm-○ h′ h t)
ren-tm-○ h′ h (DOWN t)     = cong DOWN (ren-tm-○ h′ h t)
