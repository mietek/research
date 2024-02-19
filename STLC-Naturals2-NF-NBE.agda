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
vren {A ⌜⊃⌝ B} ϱ v = λ ϱ′ → v (trans⊑ ϱ ϱ′)
vren {⌜ℕ⌝}     ϱ v = ren≪ ϱ v

open ValKit (kit _⊩_ vren) public


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {A Γ} → Γ ⊢≫ A → Γ ⊩ A
  ↑ {A ⌜⊃⌝ B} t = λ ϱ v → ↑ (ren≫ ϱ t ⌜$⌝ ↓ v)
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
⟦suc⟧ ϱ v = ⌜suc⌝ v

-- TODO: typo in Abel p.11
⟦rec⟧ : ∀ {Γ A} → Γ ⊩ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ (⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A) ⌜⊃⌝ A
⟦rec⟧ ϱ ⌜zero⌝     ϱ′ v₀ ϱ″ vₛ = vren ϱ″ v₀
⟦rec⟧ ϱ (⌜suc⌝ vₙ) ϱ′ v₀ ϱ″ vₛ = vₛ id⊑ (ren≪ (trans⊑ ϱ′ ϱ″) vₙ) id⊑ (⟦rec⟧ ϱ vₙ ϱ′ v₀ ϱ″ vₛ)
⟦rec⟧ ϱ (nnf tₙ)   ϱ′ v₀ ϱ″ vₛ = ↑ (⌜rec⌝ (ren≫ (trans⊑ ϱ′ ϱ″) tₙ) (ren≪ ϱ″ (↓ v₀)) (↓ vₛ))

⟦_⟧Con : ∀ {Γ A} → Con A → Γ ⊨ A
⟦ ⌜zero⌝ ⟧Con γ = ⟦zero⟧
⟦ ⌜suc⌝  ⟧Con γ = ⟦suc⟧
⟦ ⌜rec⌝  ⟧Con γ = ⟦rec⟧

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ con k     ⟧ γ = ⟦ k ⟧Con γ
⟦ var i     ⟧ γ = ⟦ i ⟧∋ γ
⟦ ⌜λ⌝ t     ⟧ γ = λ ϱ v → ⟦ t ⟧ (vren§ ϱ γ , v)
⟦ t₁ ⌜$⌝ t₂ ⟧ γ = ⟦ t₁ ⟧ γ id⊑ $ ⟦ t₂ ⟧ γ

nbe : ∀ {Γ A} → Γ ⊢ A → Γ ⊢≪ A
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
