----------------------------------------------------------------------------------------------------

-- normalization-by-evaluation to β-short η-long normal forms, after Abel

module STLC-Naturals2-NF-NBE where

open import STLC-Naturals2-NF public
open import Kit4 public


----------------------------------------------------------------------------------------------------

infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ⊑ W′ → W′ ⊩ A → W′ ⊩ B
W ⊩ ⌜ℕ⌝     = W ⊢≪ ⌜ℕ⌝

vren : ∀ {A W W′} → W ⊑ W′ → W ⊩ A → W′ ⊩ A
vren {A ⌜⊃⌝ B} ρ v = λ ρ′ → v (trans⊑ ρ ρ′)
vren {⌜ℕ⌝}     ρ v = ren≪ ρ v

open ValKit (kit _⊩_ vren) public


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {A Γ} → Γ ⊢≫ A → Γ ⊩ A
  ↑ {A ⌜⊃⌝ B} t = λ ρ v → ↑ (ren≫ ρ t ⌜$⌝ ↓ v)
  ↑ {⌜ℕ⌝}     t = nnf t

  ↓ : ∀ {A Γ} → Γ ⊩ A → Γ ⊢≪ A
  ↓ {A ⌜⊃⌝ B} v = ⌜λ⌝ (↓ (v (wk⊑ id⊑) (↑ (var zero))))
  ↓ {⌜ℕ⌝}     v = v

vid§ : ∀ {Γ} → Γ ⊩§ Γ
vid§ {∙}     = ∙
vid§ {Γ , A} = vren§ (wk⊑ id⊑) vid§ , ↑ (var zero)

⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Γ ⊢≪ A
⟦ v ⟧⁻¹ = ↓ (v vid§)


----------------------------------------------------------------------------------------------------

⟦zero⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝
⟦zero⟧ = ⌜zero⌝

⟦suc⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝ ⌜⊃⌝ ⌜ℕ⌝
⟦suc⟧ ρ v = ⌜suc⌝ v

-- TODO: typo in Abel p.11
⟦rec⟧ : ∀ {Γ A} → Γ ⊩ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ (⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A) ⌜⊃⌝ A
⟦rec⟧ ρ ⌜zero⌝     ρ′ v₀ ρ″ vₛ = vren ρ″ v₀
⟦rec⟧ ρ (⌜suc⌝ vₙ) ρ′ v₀ ρ″ vₛ = vₛ id⊑ (ren≪ (trans⊑ ρ′ ρ″) vₙ) id⊑ (⟦rec⟧ ρ vₙ ρ′ v₀ ρ″ vₛ)
⟦rec⟧ ρ (nnf tₙ)   ρ′ v₀ ρ″ vₛ = ↑ (⌜rec⌝ (ren≫ (trans⊑ ρ′ ρ″) tₙ) (ren≪ ρ″ (↓ v₀)) (↓ vₛ))

⟦_⟧Con : ∀ {Γ A} → Con A → Γ ⊨ A
⟦ ⌜zero⌝ ⟧Con γ = ⟦zero⟧
⟦ ⌜suc⌝  ⟧Con γ = ⟦suc⟧
⟦ ⌜rec⌝  ⟧Con γ = ⟦rec⟧

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ con k     ⟧ γ = ⟦ k ⟧Con γ
⟦ var i     ⟧ γ = ⟦ i ⟧∋ γ
⟦ ⌜λ⌝ t     ⟧ γ = λ ρ v → ⟦ t ⟧ (vren§ ρ γ , v)
⟦ t₁ ⌜$⌝ t₂ ⟧ γ = ⟦ t₁ ⟧ γ id⊑ $ ⟦ t₂ ⟧ γ

nbe : ∀ {Γ A} → Γ ⊢ A → Γ ⊢≪ A
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
