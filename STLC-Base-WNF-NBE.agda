----------------------------------------------------------------------------------------------------

-- normalization-by-evaluation to β-short weak normal form

module STLC-Base-WNF-NBE where

open import STLC-Base-WNF public
open import Kit4 public


----------------------------------------------------------------------------------------------------

infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ ⌜◦⌝     = Σ (W ⊢ ⌜◦⌝) NNF
W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ⊑ W′ → W′ ⊩ A → W′ ⊩ B

vren : ∀ {A W W′} → W ⊑ W′ → W ⊩ A → W′ ⊩ A
vren {⌜◦⌝}     ρ (_ , p) = _ , renNNF ρ p
vren {A ⌜⊃⌝ B} ρ v       = λ ρ′ → v (trans⊑ ρ ρ′)

open ValKit (kit _⊩_ vren) public

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var i     ⟧ γ = ⟦ i ⟧∋ γ
⟦ ⌜λ⌝ t     ⟧ γ = λ ρ v → ⟦ t ⟧ (vren§ ρ γ , v)
⟦ t₁ ⌜$⌝ t₂ ⟧ γ = ⟦ t₁ ⟧ γ id⊑ $ ⟦ t₂ ⟧ γ


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {A Γ} → Σ (Γ ⊢ A) NNF → Γ ⊩ A
  ↑ {⌜◦⌝}     (_ , p)  = _ , p
  ↑ {A ⌜⊃⌝ B} (_ , p₁) = λ ρ v₂ → let _ , p₂ = ↓ v₂
                                     in ↑ (_ , renNNF ρ p₁ ⌜$⌝ p₂)

  ↓ : ∀ {A Γ} → Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {⌜◦⌝}     (_ , p) = _ , nnf p
  ↓ {A ⌜⊃⌝ B} v       = let t , p = ↓ (v (wk⊑ id⊑) (↑ (var zero , var-)))
                          in ⌜λ⌝ t , ⌜λ⌝-

vid§ : ∀ {Γ} → Γ ⊩§ Γ
vid§ {∙}     = ∙
vid§ {Γ , A} = vren§ (wk⊑ id⊑) vid§ , ↑ (var zero , var-)

⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v vid§)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
