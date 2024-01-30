module STLC-Naturals-Weak-NotEtaLong-ConcreteNbE where

open import STLC-Naturals-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

-- semantic values
infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ⊆ W′ → W′ ⊩ A → W′ ⊩ B
W ⊩ ⌜ℕ⌝     = Σ (W ⊢ ⌜ℕ⌝) NF

ren⊩ : ∀ {W W′ A} → W ⊆ W′ → W ⊩ A → W′ ⊩ A
ren⊩ {A = A ⌜⊃⌝ B} e v       = λ e′ → v (trans⊆ e e′)
ren⊩ {A = ⌜ℕ⌝}     e (_ , p) = _ , ren⊢NF e p

open ⊩Kit _⊩_ (λ {W} {W′} {A} → ren⊩ {A = A}) public


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → Γ ⊩ A
  ↑ {A = A ⌜⊃⌝ B} (_ , p₁) = λ e v₂ → let _ , p₂ = ↓ v₂ in
                               ↑ (_ , ren⊢NNF e p₁ ⌜$⌝ p₂)
  ↑ {A = ⌜ℕ⌝}     (_ , p)  = _ , nnf p

  ↓ : ∀ {Γ A} → Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {A = A ⌜⊃⌝ B} v = let t , p = ↓ (v wk⊆ (↑ (⌜v⌝ zero , ⌜v⌝-))) in
                        ⌜λ⌝ t , ⌜λ⌝-
  ↓ {A = ⌜ℕ⌝}     v = v

refl⊩* : ∀ {Γ} → Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ (⌜v⌝ zero , ⌜v⌝-) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v refl⊩*)


----------------------------------------------------------------------------------------------------

⟦zero⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝
⟦zero⟧ = _ , ⌜zero⌝

⟦suc⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝ → Γ ⊩ ⌜ℕ⌝
⟦suc⟧ (_ , p′) = _ , ⌜suc⌝ p′

⟦rec⟧ : ∀ {Γ A} → Γ ⊩ ⌜ℕ⌝ → Γ ⊩ A → Γ ⊩ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A → Γ ⊩ A
⟦rec⟧ (_ , ⌜zero⌝)   v₀ vₛ = v₀
⟦rec⟧ (_ , ⌜suc⌝ pₙ) v₀ vₛ = vₛ refl⊆ (_ , pₙ) refl⊆ v₀
⟦rec⟧ (_ , nnf pₙ)   v₀ vₛ = let _ , p₀ = ↓ v₀
                                 _ , pₛ = ↓ (vₛ (drop (drop refl⊆)) (↑ (⌜v⌝ (suc zero) , ⌜v⌝-))
                                            refl⊆ (↑ (⌜v⌝ zero , ⌜v⌝-))) in
                               ↑ (_ , ⌜rec⌝ pₙ p₀ pₛ)

-- reflection
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ ⌜v⌝ i          ⟧ vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t          ⟧ vs = λ e v → ⟦ t ⟧ (v ∷ ren⊩* e vs)
⟦ t₁ ⌜$⌝ t₂      ⟧ vs = ⟦ t₁ ⟧ vs refl⊆ $ ⟦ t₂ ⟧ vs
⟦ ⌜zero⌝         ⟧ vs = ⟦zero⟧
⟦ ⌜suc⌝ t        ⟧ vs = ⟦suc⟧ (⟦ t ⟧ vs)
⟦ ⌜rec⌝ tₙ t₀ tₛ ⟧ vs = ⟦rec⟧ (⟦ tₙ ⟧ vs) (⟦ t₀ ⟧ vs) λ { e (tₙ′ , pₙ′) e′ vₐ →
                          ⟦ tₛ ⟧ (vₐ ∷ (_ , ren⊢NF e′ pₙ′) ∷ ren⊩* (trans⊆ e e′) vs) }

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
