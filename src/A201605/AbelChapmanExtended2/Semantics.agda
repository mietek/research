{-# OPTIONS --sized-types #-}

module A201605.AbelChapmanExtended2.Semantics where

open import Data.Product using (∃ ; _×_)
open import Data.Unit using () renaming (⊤ to Unit)
open import Size using (∞)

open import A201605.AbelChapmanExtended.Delay
open import A201605.AbelChapmanExtended.Convergence

open import A201605.AbelChapmanExtended2.Syntax
open import A201605.AbelChapmanExtended2.OPE
open import A201605.AbelChapmanExtended2.Renaming
open import A201605.AbelChapmanExtended2.Normalization




mutual
  V⟦_⟧_ : ∀ {Γ} (a : Ty) → Val Γ a → Set
  V⟦ ⊥ ⟧     ne v  = readback-ne v ⇓
  V⟦ a ∨ b ⟧  ne v  = readback-ne v ⇓
  V⟦ a ∨ b ⟧  inl v = C⟦ a ⟧ (now v)
  V⟦ a ∨ b ⟧  inr v = C⟦ b ⟧ (now v)
  V⟦ a ⇒ b ⟧ v     = ∀ {Δ} (η : Δ ⊇ _) (w : Val Δ a) →
                      V⟦ a ⟧ w → C⟦ b ⟧ (β-reduce (ren-val η v) w)
  V⟦ a ∧ b ⟧  v     = C⟦ a ⟧ (π₁-reduce v) × C⟦ b ⟧ (π₂-reduce v)
  V⟦ ⊤ ⟧     v     = Unit

  C⟦_⟧_ : ∀ {Γ} (a : Ty) → Delay ∞ (Val Γ a) → Set
  C⟦ a ⟧ v? = ∃ λ v → v? ⇓ v × V⟦ a ⟧ v


E⟦_⟧_ : ∀ {Δ} (Γ : Cx) → Env Δ Γ → Set
E⟦ ∅ ⟧     ∅       = Unit
E⟦ Γ , a ⟧ (ρ , v) = E⟦ Γ ⟧ ρ × V⟦ a ⟧ v
