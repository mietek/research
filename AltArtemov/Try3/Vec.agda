module AltArtemov.Try3.Vec where

open import AltArtemov.Try3.Tm public


data Vec (g k : ℕ) : ℕ → Set where
  []  : Vec g k 0
  _∷_ : ∀ {n} → Tm g (n + k) → Vec g k n → Vec g k (suc n)

infixr 15 _∷_

[_] : ∀ {g k} → Tm g k → Vec g k 1
[ t ] = t ∷ []

VARs : ∀ {g k n} → Fin g → Vec g k n
VARs {n = zero}  i = []
VARs {n = suc n} i = VAR i ∷ VARs i

LAMs : ∀ {g k n} → Vec (suc g) k n → Vec g k n
LAMs []       = []
LAMs (t ∷ ts) = LAM t ∷ LAMs ts

APPs : ∀ {g k n} → Vec g k n → Vec g k n → Vec g k n
APPs []       []           = []
APPs (t₁ ∷ ts₁) (t₂ ∷ ts₂) = APP t₁ t₂ ∷ APPs ts₁ ts₂

PAIRs : ∀ {g k n} → Vec g k n → Vec g k n → Vec g k n
PAIRs []         []         = []
PAIRs (t₁ ∷ ts₁) (t₂ ∷ ts₂) = PAIR t₁ t₂ ∷ PAIRs ts₁ ts₂

FSTs : ∀ {g k n} → Vec g k n → Vec g k n
FSTs []       = []
FSTs (t ∷ ts) = FST t ∷ FSTs ts

SNDs : ∀ {g k n} → Vec g k n → Vec g k n
SNDs []       = []
SNDs (t ∷ ts) = SND t ∷ SNDs ts

UPs : ∀ {g k n} → Vec g k n → Vec g (suc k) n
UPs []                       = []
UPs {g} {k} {suc n} (t ∷ ts) = subst (Tm g) (suc-plus k n) (UP t) ∷ UPs ts

DOWNs : ∀ {g k n} → Vec g (suc k) n → Vec g k n
DOWNs []                       = []
DOWNs {g} {k} {suc n} (t ∷ ts) = DOWN (subst (Tm g) (sym (suc-plus k n)) t) ∷ DOWNs ts

head : ∀ {g k n} → Vec g k (suc n) → Tm g (n + k)
head (t ∷ ts) = t

head-LAMs : ∀ {g k n} (ts : Vec (suc g) k (suc n)) →
              head (LAMs ts) ≡ LAM (head ts)
head-LAMs (t ∷ ts) = refl

head-APPs : ∀ {g k n} (ts₁ ts₂ : Vec g k (suc n)) →
              head (APPs ts₁ ts₂) ≡ APP (head ts₁) (head ts₂)
head-APPs (t₁ ∷ ts₁) (t₂ ∷ ts₂) = refl

head-PAIRs : ∀ {g k n} (ts₁ ts₂ : Vec g k (suc n)) →
               head (PAIRs ts₁ ts₂) ≡ PAIR (head ts₁) (head ts₂)
head-PAIRs (t₁ ∷ ts₁) (t₂ ∷ ts₂) = refl

head-FSTs : ∀ {g k n} (ts : Vec g k (suc n)) →
              head (FSTs ts) ≡ FST (head ts)
head-FSTs (t ∷ ts) = refl

head-SNDs : ∀ {g k n} (ts : Vec g k (suc n)) →
              head (SNDs ts) ≡ SND (head ts)
head-SNDs (t ∷ ts) = refl

head-UPs : ∀ {g k n} (ts : Vec g k (suc n)) →
             head (UPs ts) ≡ subst (Tm g) (suc-plus k n) (UP (head ts))
head-UPs (t ∷ ts) = refl

head-DOWNs : ∀ {g k n} (ts : Vec g (suc k) (suc n)) →
               head (DOWNs ts) ≡ DOWN (subst (Tm g) (sym (suc-plus k n)) (head ts))
head-DOWNs (t ∷ ts) = refl

tail : ∀ {g k n} → Vec g k (suc n) → Vec g k n
tail (t ∷ ts) = ts

tail-LAMs : ∀ {g k n} (ts : Vec (suc g) k (suc n)) →
              tail (LAMs ts) ≡ LAMs (tail ts)
tail-LAMs (t ∷ ts) = refl

tail-APPs : ∀ {g k n} (ts₁ ts₂ : Vec g k (suc n)) →
              tail (APPs ts₁ ts₂) ≡ APPs (tail ts₁) (tail ts₂)
tail-APPs (t₁ ∷ ts₁) (t₂ ∷ ts₂) = refl

tail-PAIRs : ∀ {g k n} (ts₁ ts₂ : Vec g k (suc n)) →
               tail (PAIRs ts₁ ts₂) ≡ PAIRs (tail ts₁) (tail ts₂)
tail-PAIRs (t₁ ∷ ts₁) (t₂ ∷ ts₂) = refl

tail-FSTs : ∀ {g k n} (ts : Vec g k (suc n)) →
              tail (FSTs ts) ≡ FSTs (tail ts)
tail-FSTs (t ∷ ts) = refl

tail-SNDs : ∀ {g k n} (ts : Vec g k (suc n)) →
              tail (SNDs ts) ≡ SNDs (tail ts)
tail-SNDs (t ∷ ts) = refl

tail-UPs : ∀ {g k n} (ts : Vec g k (suc n)) →
             tail (UPs ts) ≡ UPs (tail ts)
tail-UPs (t ∷ ts) = refl

tail-DOWNs : ∀ {g k n} (ts : Vec g (suc k) (suc n)) →
               tail (DOWNs ts) ≡ DOWNs (tail ts)
tail-DOWNs (t ∷ ts) = refl

ren-vec : ∀ {g g′ k n} → g′ ≥ g → Vec g k n → Vec g′ k n
ren-vec h []       = []
ren-vec h (t ∷ ts) = ren-tm h t ∷ ren-vec h ts

wk-vec : ∀ {g k n} → Vec g k n → Vec (suc g) k n
wk-vec = ren-vec ≥wk

wk*-vec : ∀ {g k n} → Vec 0 k n → Vec g k n
wk*-vec = ren-vec ≥to

ren-vec-id : ∀ {g k n} (ts : Vec g k n) → ren-vec ≥id ts ≡ ts
ren-vec-id []       = refl
ren-vec-id (t ∷ ts) = cong₂ _∷_ (ren-tm-id t) (ren-vec-id ts)

ren-vec-○ : ∀ {g g′ g″ k n} (h′ : g″ ≥ g′) (h : g′ ≥ g) (ts : Vec g k n) →
              ren-vec h′ (ren-vec h ts) ≡ ren-vec (h′ ○ h) ts
ren-vec-○ h′ h []       = refl
ren-vec-○ h′ h (t ∷ ts) = cong₂ _∷_ (ren-tm-○ h′ h t) (ren-vec-○ h′ h ts)

ren-VARs : ∀ {g g′ k n} (h : g′ ≥ g) (i : Fin g) →
             ren-vec h (VARs {k = k} {n = n} i) ≡ VARs (ren-fin h i)
ren-VARs {n = zero}  h i = refl
ren-VARs {n = suc n} h i = cong₂ _∷_ refl (ren-VARs h i)

ren-LAMs : ∀ {g g′ k n} (h : g′ ≥ g) (ts : Vec (suc g) k n) →
             ren-vec h (LAMs ts) ≡ LAMs (ren-vec (lift h) ts)
ren-LAMs h []       = refl
ren-LAMs h (t ∷ ts) = cong₂ _∷_ refl (ren-LAMs h ts)

ren-APPs : ∀ {g g′ k n} (h : g′ ≥ g) (ts₁ ts₂ : Vec g k n) →
            ren-vec h (APPs ts₁ ts₂) ≡ APPs (ren-vec h ts₁) (ren-vec h ts₂)
ren-APPs h []         []         = refl
ren-APPs h (t₁ ∷ ts₁) (t₂ ∷ ts₂) = cong₂ _∷_ refl (ren-APPs h ts₁ ts₂)

ren-PAIRs : ∀ {g g′ k n} (h : g′ ≥ g) (ts₁ ts₂ : Vec g k n) →
              ren-vec h (PAIRs ts₁ ts₂) ≡ PAIRs (ren-vec h ts₁) (ren-vec h ts₂)
ren-PAIRs h []         []         = refl
ren-PAIRs h (t₁ ∷ ts₁) (t₂ ∷ ts₂) = cong₂ _∷_ refl (ren-PAIRs h ts₁ ts₂)

ren-FSTs : ∀ {g g′ k n} (h : g′ ≥ g) (ts : Vec g k n) →
             ren-vec h (FSTs ts) ≡ FSTs (ren-vec h ts)
ren-FSTs h []       = refl
ren-FSTs h (t ∷ ts) = cong₂ _∷_ refl (ren-FSTs h ts)

ren-SNDs : ∀ {g g′ k n} (h : g′ ≥ g) (ts : Vec g k n) →
             ren-vec h (SNDs ts) ≡ SNDs (ren-vec h ts)
ren-SNDs h []       = refl
ren-SNDs h (t ∷ ts) = cong₂ _∷_ refl (ren-SNDs h ts)

-- ren-UPs : ∀ {g g′ k n} (h : g′ ≥ g) (ts : Vec g k n) →
--             ren-vec h (UPs ts) ≡ UPs (ren-vec h ts)
-- ren-UPs h []       = refl
-- ren-UPs {k = k} {suc n} h (t ∷ ts) = cong₂ _∷_ {!!} (ren-UPs h ts)

-- ren-DOWNs : ∀ {g g′ k n} (h : g′ ≥ g) (ts : Vec g (suc k) n) →
--               ren-vec h (DOWNs ts) ≡ DOWNs (ren-vec h ts)
-- ren-DOWNs h []     = refl
-- ren-DOWNs {k = k} {suc n} h (t ∷ ts) = cong₂ _∷_ {!!} (ren-DOWNs h ts)

-- ren-subst-UP : ∀ {g g′ k n} {h : g′ ≥ g} (t : Tm g (n + k)) →
--                  ren-tm h (subst (Tm g) (suc-plus k n) (UP t)) ≡
--                  subst (Tm g′) (suc-plus k n) (UP (ren-tm h t))
-- ren-subst-UP {k = k} {n = zero}  t = refl
-- ren-subst-UP {k = k} {n = suc n} t = {!!}

-- ren-subst-DOWN : ∀ {g g′ k n} {h : g′ ≥ g} (t : Tm g (n + suc k)) →
--                    DOWN (ren-tm h (subst (Tm g) (sym (suc-plus k n)) t)) ≡
--                    DOWN (subst (Tm g′) (sym (suc-plus k n)) (ren-tm h t))
-- ren-subst-DOWN {k = k} {n} t rewrite suc-plus (suc k) n = cong DOWN {!!}
