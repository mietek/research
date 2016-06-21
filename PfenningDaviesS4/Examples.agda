module PfenningDaviesS4.Examples where

open import PfenningDaviesS4.CoinductiveNormalisationByEvaluation public


I : ∀ {A Γ Δ} → Tm Γ Δ (A ⊃ A)
I = lam v₀

K : ∀ {A B Γ Δ} → Tm Γ Δ (A ⊃ B ⊃ A)
K = lam (lam v₁)

S : ∀ {A B C Γ Δ} → Tm Γ Δ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))


D : ∀ {A B Γ Δ} → Tm Γ Δ (□ (A ⊃ B) ⊃ □ A ⊃ □ B)
D = lam (lam (unbox v₁ (unbox v₀ (box (app ⋆v₁ ⋆v₀)))))

T : ∀ {A Γ Δ} → Tm Γ Δ (□ A ⊃ A)
T = lam (unbox v₀ ⋆v₀)

#4 : ∀ {A Γ Δ} → Tm Γ Δ (□ A ⊃ □ □ A)
#4 = lam (unbox v₀ (box (box ⋆v₀)))


E00 : ∀ {A B Γ Δ} → Tm Γ Δ (A ⊃ B ⊃ A ∧ B)
E00 = lam (lam (pair v₁ v₀))


E01 : ∀ {A B Γ Δ} → Tm Γ Δ (□ A ⊃ □ B ⊃ □ □ (A ∧ B))
E01 = lam (lam (unbox v₁ (unbox v₀ (box (box (pair ⋆v₁ ⋆v₀))))))

E02 : ∀ {A B Γ Δ} → Tm Γ Δ (□ A ⊃ □ B ⊃ □ (A ∧ B))
E02 = lam (lam (unbox v₁ (unbox v₀ (box (pair ⋆v₁ ⋆v₀)))))

E03 : ∀ {A B Γ Δ} → Tm Γ Δ (□ A ∧ □ B ⊃ □ □ (A ∧ B))
E03 = lam (unbox (fst v₀) (unbox (snd v₀) (box (box (pair ⋆v₁ ⋆v₀)))))

E04 : ∀ {A B Γ Δ} → Tm Γ Δ (□ A ∧ □ B ⊃ □ (A ∧ B))
E04 = lam (unbox (fst v₀) (unbox (snd v₀) (box (pair ⋆v₁ ⋆v₀))))


E11 : ∀ {A Γ Δ} → Tm Γ Δ (□ (□ A ⊃ A))
E11 = box T

E12 : ∀ {A Γ Δ} → Tm Γ Δ (□ (□ A ⊃ □ □ A))
E12 = box #4

E13 : ∀ {A B Γ Δ} → Tm Γ Δ (□ □ (A ⊃ B ⊃ A ∧ B))
E13 = box (box (lam (lam (pair v₁ v₀))))

E14 : ∀ {A B Γ Δ} → Tm Γ Δ (□ (□ A ⊃ □ B ⊃ □ □ (A ∧ B)))
E14 = box (lam (lam (unbox v₁ (unbox v₀ (box (box (pair ⋆v₁ ⋆v₀)))))))
