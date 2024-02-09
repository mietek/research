----------------------------------------------------------------------------------------------------

-- normalization by evaluation to β-short weak normal form

module STLC-Base-WNF-NBE where

open import STLC-Base-WNF public
open import Kit4 public


----------------------------------------------------------------------------------------------------

infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ ⌜◦⌝     = Σ (W ⊢ ⌜◦⌝) NNF
W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ⊆ W′ → W′ ⊩ A → W′ ⊩ B

vren : ∀ {A W W′} → W ⊆ W′ → W ⊩ A → W′ ⊩ A
vren {⌜◦⌝}     e (_ , p) = _ , renNNF e p
vren {A ⌜⊃⌝ B} e v       = λ e′ → v (trans⊆ e e′)

open ValKit (kit _⊩_ vren) public

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var i     ⟧ vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t     ⟧ vs = λ e v → ⟦ t ⟧ (v ∷ vrens e vs)
⟦ t₁ ⌜$⌝ t₂ ⟧ vs = ⟦ t₁ ⟧ vs id⊆ $ ⟦ t₂ ⟧ vs


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {A Γ} → Σ (Γ ⊢ A) NNF → Γ ⊩ A
  ↑ {⌜◦⌝}     (_ , p)  = _ , p
  ↑ {A ⌜⊃⌝ B} (_ , p₁) = λ e v₂ → let _ , p₂ = ↓ v₂
                                     in ↑ (_ , renNNF e p₁ ⌜$⌝ p₂)

  ↓ : ∀ {A Γ} → Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {⌜◦⌝}     (_ , p) = _ , nnf p
  ↓ {A ⌜⊃⌝ B} v       = let t , p = ↓ (v (wk⊆ id⊆) (↑ (var zero , var-)))
                          in ⌜λ⌝ t , ⌜λ⌝-

vids : ∀ {Γ} → Γ ⊩* Γ
vids {[]}    = []
vids {A ∷ Γ} = ↑ (var zero , var-) ∷ vrens (wk⊆ id⊆) vids

⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v vids)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
