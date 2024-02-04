module STLC-Base-Weak-NotEtaLong-ConcreteNbE where

open import STLC-Base-Weak-NotEtaLong public
open import Kit4 public


----------------------------------------------------------------------------------------------------

infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ ⌜◦⌝     = Σ (W ⊢ ⌜◦⌝) NNF
W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ⊆ W′ → W′ ⊩ A → W′ ⊩ B

vren : ∀ {W W′ A} → W ⊆ W′ → W ⊩ A → W′ ⊩ A
vren {A = ⌜◦⌝}     e (_ , p) = _ , renNNF e p
vren {A = A ⌜⊃⌝ B} e v       = λ e′ → v (trans⊆ e e′)

open ValKit (kit _⊩_ (λ {W} {W′} {A} → vren {A = A})) public

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var i     ⟧ vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t     ⟧ vs = λ e v → ⟦ t ⟧ (v ∷ vrens e vs)
⟦ t₁ ⌜$⌝ t₂ ⟧ vs = ⟦ t₁ ⟧ vs id⊆ $ ⟦ t₂ ⟧ vs


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → Γ ⊩ A
  ↑ {A = ⌜◦⌝}     (_ , p)  = _ , p
  ↑ {A = A ⌜⊃⌝ B} (_ , p₁) = λ e v₂ → let _ , p₂ = ↓ v₂
                                         in ↑ (_ , renNNF e p₁ ⌜$⌝ p₂)

  ↓ : ∀ {Γ A} → Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {A = ⌜◦⌝}     (_ , p) = _ , nnf p
  ↓ {A = A ⌜⊃⌝ B} v       = let t , p = ↓ (v (wk⊆ id⊆) (↑ (var zero , var-)))
                              in ⌜λ⌝ t , ⌜λ⌝-

vids : ∀ {Γ} → Γ ⊩* Γ
vids {[]}    = []
vids {A ∷ Γ} = ↑ (var zero , var-) ∷ vrens (wk⊆ id⊆) vids

⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v vids)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
