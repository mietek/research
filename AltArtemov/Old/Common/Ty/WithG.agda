module AltArtemov.Old.Common.Ty.WithG where

open import AltArtemov.Try2.Tm public


data Ty (g : ℕ) : ℕ → Set where
  ⊥  : ∀ {n} → Ty g n
  _⊃_ : ∀ {n} → Ty g n → Ty g n → Ty g n
  _∧_ : ∀ {n} → Ty g n → Ty g n → Ty g n
  _∶_ : ∀ {n} → Tm g n → Ty g n → Ty g (suc n)

infixr 5 _⊃_
infixr 15 _∶_

ren-ty : ∀ {g g′ n} → g′ ≥ g → Ty g n → Ty g′ n
ren-ty h ⊥      = ⊥
ren-ty h (A ⊃ B) = ren-ty h A ⊃ ren-ty h B
ren-ty h (A ∧ B) = ren-ty h A ∧ ren-ty h B
ren-ty h (t ∶ A) = ren-tm h t ∶ ren-ty h A

wk-ty : ∀ {g n} → Ty g n → Ty (suc g) n
wk-ty = ren-ty ≥wk

wk*-ty : ∀ {g n} → Ty 0 n → Ty g n
wk*-ty = ren-ty ≥to

ren-ty-id : ∀ {g n} (A : Ty g n) → ren-ty ≥id A ≡ A
ren-ty-id ⊥      = refl
ren-ty-id (A ⊃ B) = cong₂ _⊃_ (ren-ty-id A) (ren-ty-id B)
ren-ty-id (A ∧ B) = cong₂ _∧_ (ren-ty-id A) (ren-ty-id B)
ren-ty-id (t ∶ A) = cong₂ _∶_ (ren-tm-id t) (ren-ty-id A)

ren-ty-○ : ∀ {g g′ g″ n} (h′ : g″ ≥ g′) (h : g′ ≥ g) (A : Ty g n) →
             ren-ty h′ (ren-ty h A) ≡ ren-ty (h′ ○ h) A
ren-ty-○ h′ h ⊥      = refl
ren-ty-○ h′ h (A ⊃ B) = cong₂ _⊃_ (ren-ty-○ h′ h A) (ren-ty-○ h′ h B)
ren-ty-○ h′ h (A ∧ B) = cong₂ _∧_ (ren-ty-○ h′ h A) (ren-ty-○ h′ h B)
ren-ty-○ h′ h (t ∶ A) = cong₂ _∶_ (ren-tm-○ h′ h t) (ren-ty-○ h′ h A)
