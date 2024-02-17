----------------------------------------------------------------------------------------------------

-- normalization-by-evaluation to β-short semi-weak normal form

module STLC-Naturals-SWNF-NBE where

open import STLC-Naturals-SWNF public
open import Kit4 public


----------------------------------------------------------------------------------------------------

infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ⊑ W′ → W′ ⊩ A → W′ ⊩ B
W ⊩ ⌜ℕ⌝     = Σ (W ⊢ ⌜ℕ⌝) NF

vren : ∀ {A W W′} → W ⊑ W′ → W ⊩ A → W′ ⊩ A
vren {A ⌜⊃⌝ B} ρ v       = λ ρ′ → v (trans⊑ ρ ρ′)
vren {⌜ℕ⌝}     ρ (_ , p) = _ , renNF ρ p

open ValKit (kit _⊩_ vren) public


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {A Γ} → Σ (Γ ⊢ A) NNF → Γ ⊩ A
  ↑ {A ⌜⊃⌝ B} (_ , p₁) = λ ρ v₂ → let _ , p₂ = ↓ v₂
                                     in ↑ (_ , renNNF ρ p₁ ⌜$⌝ p₂)
  ↑ {⌜ℕ⌝}     (_ , p)  = _ , nnf p

  ↓ : ∀ {A Γ} → Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {A ⌜⊃⌝ B} v = let t , p = ↓ (v (wk⊑ id⊑) (↑ (var zero , var-)))
                    in ⌜λ⌝ t , ⌜λ⌝-
  ↓ {⌜ℕ⌝}     v = v

vid§ : ∀ {Γ} → Γ ⊩§ Γ
vid§ {∙}     = ∙
vid§ {Γ , A} = vren§ (wk⊑ id⊑) vid§ , ↑ (var zero , var-)

⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v vid§)


----------------------------------------------------------------------------------------------------

⟦zero⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝
⟦zero⟧ = _ , ⌜zero⌝

⟦suc⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝ → Γ ⊩ ⌜ℕ⌝
⟦suc⟧ (_ , p) = _ , ⌜suc⌝ p

⟦rec⟧ : ∀ {Γ A} → Γ ⊩ ⌜ℕ⌝ → Γ ⊩ A → Γ ⊩ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A → Γ ⊩ A
⟦rec⟧ (_ , ⌜zero⌝)   v₀ vₛ = v₀
⟦rec⟧ (_ , ⌜suc⌝ pₙ) v₀ vₛ = vₛ id⊑ (_ , pₙ) id⊑ v₀
⟦rec⟧ (_ , nnf pₙ)   v₀ vₛ = let _ , p₀ = ↓ v₀
                                 _ , pₛ = ↓ (vₛ (wk⊑ (wk⊑ id⊑)) (↑ (var (wk∋ zero) , var-))
                                            id⊑ (↑ (var zero , var-)))
                               in ↑ (_ , ⌜rec⌝ pₙ p₀ pₛ)

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var i          ⟧ γ = ⟦ i ⟧∋ γ
⟦ ⌜λ⌝ t          ⟧ γ = λ ρ v → ⟦ t ⟧ (vren§ ρ γ , v)
⟦ t₁ ⌜$⌝ t₂      ⟧ γ = ⟦ t₁ ⟧ γ id⊑ $ ⟦ t₂ ⟧ γ
⟦ ⌜zero⌝         ⟧ γ = ⟦zero⟧
⟦ ⌜suc⌝ t        ⟧ γ = ⟦suc⟧ (⟦ t ⟧ γ)
⟦ ⌜rec⌝ tₙ t₀ tₛ ⟧ γ = ⟦rec⟧ (⟦ tₙ ⟧ γ) (⟦ t₀ ⟧ γ) λ { ρ (tₙ′ , pₙ′) ρ′ vₐ →
                         ⟦ tₛ ⟧ ((vren§ (trans⊑ ρ ρ′) γ , (_ , renNF ρ′ pₙ′)) , vₐ) }

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
