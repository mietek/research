module A201606.STLC.Examples where

open import A201606.STLC.Syntax public


I : ∀ {A Γ} → Tm Γ (A ⊃ A)
I = lam v₀

K : ∀ {A B Γ} → Tm Γ (A ⊃ B ⊃ A)
K = lam (lam v₁)

S : ∀ {A B C Γ} → Tm Γ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))
