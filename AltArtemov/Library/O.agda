module AltArtemov.Library.O where

open import AltArtemov.Library public


data _≥_ : ℕ → ℕ → Set where
  base : zero ≥ zero
  weak : ∀ {g g′} → g′ ≥ g → suc g′ ≥ g
  lift : ∀ {g g′} → g′ ≥ g → suc g′ ≥ suc g

≥id : ∀ {g} → g ≥ g
≥id {zero}  = base
≥id {suc g} = lift ≥id

≥to : ∀ {g} → g ≥ zero
≥to {zero}  = base
≥to {suc g} = weak ≥to

≥wk : ∀ {g} → suc g ≥ g
≥wk = weak ≥id

≥str : ∀ {g g′} → g′ ≥ suc g → g′ ≥ g
≥str (weak h) = weak (≥str h)
≥str (lift h) = weak h

≥drop : ∀ {g g′} → suc g′ ≥ suc g → g′ ≥ g
≥drop (weak h) = ≥str h
≥drop (lift h) = h

_○_ : ∀ {g g′ g″} → g″ ≥ g′ → g′ ≥ g → g″ ≥ g
base    ○ h      = h
weak h′ ○ h      = weak (h′ ○ h)
lift h′ ○ weak h = weak (h′ ○ h)
lift h′ ○ lift h = lift (h′ ○ h)

h○id : ∀ {g g′} (h : g′ ≥ g) → h ○ ≥id ≡ h
h○id base     = refl
h○id (weak h) = cong weak (h○id h)
h○id (lift h) = cong lift (h○id h)

id○h : ∀ {g g′} (h : g′ ≥ g) → ≥id ○ h ≡ h
id○h base     = refl
id○h (weak h) = cong weak (id○h h)
id○h (lift h) = cong lift (id○h h)
