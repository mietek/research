----------------------------------------------------------------------------------------------------

-- normalization by evaluation to β-short semi-weak normal form

module STLC-Naturals-SWNF-NBE where

open import STLC-Naturals-SWNF public
open import Kit4 public


----------------------------------------------------------------------------------------------------

infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ⊆ W′ → W′ ⊩ A → W′ ⊩ B
W ⊩ ⌜ℕ⌝     = Σ (W ⊢ ⌜ℕ⌝) NF

vren : ∀ {A W W′} → W ⊆ W′ → W ⊩ A → W′ ⊩ A
vren {A ⌜⊃⌝ B} e v       = λ e′ → v (trans⊆ e e′)
vren {⌜ℕ⌝}     e (_ , p) = _ , renNF e p

open ValKit (kit _⊩_ vren) public


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {A Γ} → Σ (Γ ⊢ A) NNF → Γ ⊩ A
  ↑ {A ⌜⊃⌝ B} (_ , p₁) = λ e v₂ → let _ , p₂ = ↓ v₂
                                     in ↑ (_ , renNNF e p₁ ⌜$⌝ p₂)
  ↑ {⌜ℕ⌝}     (_ , p)  = _ , nnf p

  ↓ : ∀ {A Γ} → Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {A ⌜⊃⌝ B} v = let t , p = ↓ (v (wk⊆ id⊆) (↑ (var zero , var-)))
                    in ⌜λ⌝ t , ⌜λ⌝-
  ↓ {⌜ℕ⌝}     v = v

vids : ∀ {Γ} → Γ ⊩* Γ
vids {[]}    = []
vids {A ∷ Γ} = ↑ (var zero , var-) ∷ vrens (wk⊆ id⊆) vids

⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v vids)


----------------------------------------------------------------------------------------------------

⟦zero⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝
⟦zero⟧ = _ , ⌜zero⌝

⟦suc⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝ → Γ ⊩ ⌜ℕ⌝
⟦suc⟧ (_ , p) = _ , ⌜suc⌝ p

⟦rec⟧ : ∀ {Γ A} → Γ ⊩ ⌜ℕ⌝ → Γ ⊩ A → Γ ⊩ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A → Γ ⊩ A
⟦rec⟧ (_ , ⌜zero⌝)   v₀ vₛ = v₀
⟦rec⟧ (_ , ⌜suc⌝ pₙ) v₀ vₛ = vₛ id⊆ (_ , pₙ) id⊆ v₀
⟦rec⟧ (_ , nnf pₙ)   v₀ vₛ = let _ , p₀ = ↓ v₀
                                 _ , pₛ = ↓ (vₛ (wk⊆ (wk⊆ id⊆)) (↑ (var (suc zero) , var-))
                                            id⊆ (↑ (var zero , var-)))
                               in ↑ (_ , ⌜rec⌝ pₙ p₀ pₛ)

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var i          ⟧ vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t          ⟧ vs = λ e v → ⟦ t ⟧ (v ∷ vrens e vs)
⟦ t₁ ⌜$⌝ t₂      ⟧ vs = ⟦ t₁ ⟧ vs id⊆ $ ⟦ t₂ ⟧ vs
⟦ ⌜zero⌝         ⟧ vs = ⟦zero⟧
⟦ ⌜suc⌝ t        ⟧ vs = ⟦suc⟧ (⟦ t ⟧ vs)
⟦ ⌜rec⌝ tₙ t₀ tₛ ⟧ vs = ⟦rec⟧ (⟦ tₙ ⟧ vs) (⟦ t₀ ⟧ vs) λ { e (tₙ′ , pₙ′) e′ vₐ →
                          ⟦ tₛ ⟧ (vₐ ∷ (_ , renNF e′ pₙ′) ∷ vrens (trans⊆ e e′) vs) }

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
