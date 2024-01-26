module STLC-Naturals2-Strong-EtaLong-ConcreteNBE where

open import STLC-Naturals2-Strong-EtaLong public


----------------------------------------------------------------------------------------------------

-- semantic values
infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ⊆ W′ → W′ ⊩ A → W′ ⊩ B
W ⊩ ⌜ℕ⌝     = ∀ {W′} → W ⊆ W′ → W′ ⋘ ⌜ℕ⌝

ren⊩ : ∀ {W W′ A} → W ⊆ W′ → W ⊩ A → W′ ⊩ A
ren⊩ {A = A ⌜⊃⌝ B} e v = λ e′ → v (trans⊆ e e′)
ren⊩ {A = ⌜ℕ⌝}     e v = λ e′ → v (trans⊆ e e′)

open ConcreteKit _⊩_ (λ {_} {_} {A} → ren⊩ {_} {_} {A}) public


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {Γ A} → Γ ⋙ A → Γ ⊩ A
  ↑ {A = A ⌜⊃⌝ B} t = λ e v → ↑ (ren⋙ e t ⌜$⌝ ↓ v)
  ↑ {A = ⌜ℕ⌝}     t = λ e → nnf (ren⋙ e t)

  ↓ : ∀ {Γ A} → Γ ⊩ A → Γ ⋘ A
  ↓ {A = A ⌜⊃⌝ B} v = ⌜λ⌝ (↓ (v wk⊆ (↑ (⌜v⌝ zero))))
  ↓ {A = ⌜ℕ⌝}     v = v refl⊆

refl⊩* : ∀ {Γ} → Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ (⌜v⌝ zero) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Γ ⋘ A
⟦ v ⟧⁻¹ = ↓ (v refl⊩*)


----------------------------------------------------------------------------------------------------

⟦zero⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝
⟦zero⟧ e = ⌜zero⌝

⟦suc⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝ ⌜⊃⌝ ⌜ℕ⌝
⟦suc⟧ e v e′ = v e′

-- TODO: typo in Abel p.11?
-- TODO: isn't there a better way?
{-# TERMINATING #-}
⟦rec⟧ : ∀ {Γ A} → Γ ⊩ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ (⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A) ⌜⊃⌝ A
⟦rec⟧ e vₙ e′ v₀ e″ vₛ with vₙ e′
... | ⌜zero⌝             = ren⊩ e″ v₀
... | ⌜suc⌝ tₙ           = vₛ refl⊆ (λ e‴ → ren⋘ (trans⊆ e″ e‴) tₙ) refl⊆
                             (⟦rec⟧ e′ (λ e‴ → ren⋘ e‴ tₙ) refl⊆ v₀ e″ vₛ)
... | nnf tₙ             = ↑ (⌜rec⌝ (ren⋙ e″ tₙ) (ren⋘ e″ (↓ v₀)) (↓ vₛ))

⟦_⟧C : ∀ {Γ A} → Con A → Γ ⊨ A
⟦ ⌜zero⌝ ⟧C vs = ⟦zero⟧
⟦ ⌜suc⌝  ⟧C vs = ⟦suc⟧
⟦ ⌜rec⌝  ⟧C vs = ⟦rec⟧

-- reflection
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ ⌜c⌝ k     ⟧ vs = ⟦ k ⟧C vs
⟦ ⌜v⌝ i     ⟧ vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t     ⟧ vs = λ e v → ⟦ t ⟧ (v ∷ ren⊩* e vs)
⟦ t₁ ⌜$⌝ t₂ ⟧ vs = ⟦ t₁ ⟧ vs refl⊆ $ ⟦ t₂ ⟧ vs

nbe : ∀ {Γ A} → Γ ⊢ A → Γ ⋘ A
nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


----------------------------------------------------------------------------------------------------
