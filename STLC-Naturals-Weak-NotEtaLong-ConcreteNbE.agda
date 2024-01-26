module STLC-Naturals-Weak-NotEtaLong-ConcreteNbE where

open import STLC-Naturals-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

-- semantic values
infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ⊆ W′ → W′ ⊩ A → W′ ⊩ B
W ⊩ ⌜ℕ⌝     = ∀ {W′} → W ⊆ W′ → Σ (W′ ⊢ ⌜ℕ⌝) NF

ren⊩ : ∀ {W W′ A} → W ⊆ W′ → W ⊩ A → W′ ⊩ A
ren⊩ {A = A ⌜⊃⌝ B} e v = λ e′ → v (trans⊆ e e′)
ren⊩ {A = ⌜ℕ⌝}     e v = λ e′ → v (trans⊆ e e′)

open ConcreteKit _⊩_ (λ {_} {_} {A} → ren⊩ {_} {_} {A}) public


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → Γ ⊩ A
  ↑ {A = A ⌜⊃⌝ B} (t , p) = λ e v → ↑ (_ , renNNF e p ⌜$⌝ proj₂ (↓ v))
  ↑ {A = ⌜ℕ⌝}     (t , p) = λ e → _ , nnf (renNNF e p)

  ↓ : ∀ {Γ A} → Γ ⊩ A → Σ (Γ ⊢ A) λ t → NF t
  ↓ {A = A ⌜⊃⌝ B} v with ↓ (v wk⊆ (↑ (⌜v⌝ zero , ⌜v⌝-)))
  ... | t , p         = ⌜λ⌝ t , ⌜λ⌝-
  ↓ {A = ⌜ℕ⌝}     v = v refl⊆

refl⊩* : ∀ {Γ} → Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ (⌜v⌝ zero , ⌜v⌝-) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v refl⊩*)


----------------------------------------------------------------------------------------------------

-- TODO: isn't there a better way?
{-# TERMINATING #-}
⟦rec⟧ : ∀ {Γ A} → Γ ⊨ ⌜ℕ⌝ → Γ ⊨ A → A ∷ ⌜ℕ⌝ ∷ Γ ⊨ A → Γ ⊨ A
⟦rec⟧ vₙ v₀ vₛ vs         with vₙ vs refl⊆
... | ⌜zero⌝ , ⌜zero⌝       = v₀ vs
... | ⌜suc⌝ tₙ , ⌜suc⌝ pₙ   = vₛ (⟦rec⟧ vₙ v₀ vₛ vs ∷ (λ e → ren e tₙ , renNF e pₙ) ∷ vs)
... | tₙ , nnf pₙ           =
  let t₀ , p₀ = ↓ (v₀ vs)
      tₛ , pₛ = ↓ (vₛ (aux vs))
  in  ↑ (⌜rec⌝ tₙ t₀ tₛ , ⌜rec⌝ pₙ p₀ pₛ)
  where
    aux : ∀ {W Γ A B} → W ⊩* Γ → A ∷ B ∷ W ⊩* A ∷ B ∷ Γ
    aux vs = ↑ (⌜v⌝ zero , ⌜v⌝-) ∷ (↑ (⌜v⌝ (suc zero) , ⌜v⌝-) ∷ ren⊩* (drop wk⊆) vs)

-- reflection
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ ⌜v⌝ i          ⟧ vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t          ⟧ vs = λ e v → ⟦ t ⟧ (v ∷ ren⊩* e vs)
⟦ t₁ ⌜$⌝ t₂      ⟧ vs = ⟦ t₁ ⟧ vs refl⊆ $ ⟦ t₂ ⟧ vs
⟦ ⌜zero⌝         ⟧ vs = λ e → ⌜zero⌝ , ⌜zero⌝
⟦ ⌜suc⌝ t        ⟧ vs = λ e → let t′ , p′ = ⟦ t ⟧ vs e in ⌜suc⌝ t′ , ⌜suc⌝ p′
⟦ ⌜rec⌝ tₙ t₀ tₛ ⟧ vs = ⟦rec⟧ ⟦ tₙ ⟧ ⟦ t₀ ⟧ ⟦ tₛ ⟧ vs

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


----------------------------------------------------------------------------------------------------
