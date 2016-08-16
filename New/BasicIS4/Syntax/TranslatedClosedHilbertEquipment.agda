module New.BasicIS4.Syntax.TranslatedClosedHilbertEquipment where

open import New.BasicIS4.Syntax.ClosedHilbert public
open import New.BasicIS4.Syntax.Translation public

import New.BasicIS4.Syntax.OpenHilbert as TC


-- Translated equipment.

ᵀmono⊢ : ∀ {Π Π′ A} → Π ⊆ Π′ → ⊢ Π ▻⋯▻ A → ⊢ Π′ ▻⋯▻ A
ᵀmono⊢ θ t = tc→t (TC.mono⊢ θ (t→tc t))

ᵀml : ∀ {Π Π′ A} → Π ⊆ Π′ → ⊢ □⋆ Π ▻⋯▻ A → ⊢ □⋆ Π′ ▻⋯▻ A
ᵀml = ᵀmono⊢ ∘ lift⊆

ᵀapp : ∀ {Π A B} → ⊢ Π ▻⋯▻ A ▻ B → ⊢ Π ▻⋯▻ A → ⊢ Π ▻⋯▻ B
ᵀapp {Π} t u = tc→t (TC.app {Π} (t→tc t) (t→tc u))

ᵀk₁ : ∀ {Π A B} → ⊢ Π ▻⋯▻ A → ⊢ Π ▻⋯▻ B ▻ A
ᵀk₁ {Π} t = tc→t (TC.app {Π} TC.ck (t→tc t))

ᵀs₁ : ∀ {Π A B C} → ⊢ Π ▻⋯▻ A ▻ B ▻ C → ⊢ Π ▻⋯▻ (A ▻ B) ▻ A ▻ C
ᵀs₁ {Π} t = tc→t (TC.app {Π} TC.cs (t→tc t))

ᵀs₂ : ∀ {Π A B C} → ⊢ Π ▻⋯▻ A ▻ B ▻ C → ⊢ Π ▻⋯▻ A ▻ B → ⊢ Π ▻⋯▻ A ▻ C
ᵀs₂ {Π} t u = tc→t (TC.app {Π} (TC.app TC.cs (t→tc t)) (t→tc u))

ᵀdist₁ : ∀ {Π A B} → ⊢ Π ▻⋯▻ □ (A ▻ B) → ⊢ Π ▻⋯▻ □ A ▻ □ B
ᵀdist₁ {Π} t = tc→t (TC.app {Π} TC.cdist (t→tc t))

ᵀpair₁ : ∀ {Π A B} → ⊢ Π ▻⋯▻ A → ⊢ Π ▻⋯▻ B ▻ A ∧ B
ᵀpair₁ {Π} t = tc→t (TC.app {Π} TC.cpair (t→tc t))

ᵀpair : ∀ {Π A B} → ⊢ Π ▻⋯▻ A → ⊢ Π ▻⋯▻ B → ⊢ Π ▻⋯▻ A ∧ B
ᵀpair {Π} t u = tc→t (TC.pair {_} {_} {Π} (t→tc t) (t→tc u))

ᵀlift : ∀ {Π A} → ⊢ Π ▻⋯▻ A → ⊢ □⋆ Π ▻⋯▻ □ A
ᵀlift {Π} t = tc→t (TC.lift {Π} (t→tc t))

ᵀcxdown : ∀ {Π A} → ⊢ □⋆ □⋆ Π ▻⋯▻ A → ⊢ □⋆ Π ▻⋯▻ A
ᵀcxdown {Π} t = tc→t (TC.cxdown {Π} (t→tc t))
