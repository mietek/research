module STLC-Naturals2-Strong-EtaLong-ConcreteNBE where

open import STLC-Naturals2-Strong-EtaLong public


----------------------------------------------------------------------------------------------------

-- semantic values
infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ⊆ W′ → W′ ⊩ A → W′ ⊩ B
W ⊩ ⌜ℕ⌝     = W ⋘ ⌜ℕ⌝

ren⊩ : ∀ {W W′ A} → W ⊆ W′ → W ⊩ A → W′ ⊩ A
ren⊩ {A = A ⌜⊃⌝ B} e v = λ e′ → v (trans⊆ e e′)
ren⊩ {A = ⌜ℕ⌝}     e v = ren⋘ e v

open ConcreteKit _⊩_ (λ {_} {_} {A} → ren⊩ {_} {_} {A}) public


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {Γ A} → Γ ⋙ A → Γ ⊩ A
  ↑ {A = A ⌜⊃⌝ B} t = λ e v → ↑ (ren⋙ e t ⌜$⌝ ↓ v)
  ↑ {A = ⌜ℕ⌝}     t = nnf t

  ↓ : ∀ {Γ A} → Γ ⊩ A → Γ ⋘ A
  ↓ {A = A ⌜⊃⌝ B} v = ⌜λ⌝ (↓ (v wk⊆ (↑ (⌜v⌝ zero))))
  ↓ {A = ⌜ℕ⌝}     v = v

refl⊩* : ∀ {Γ} → Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ (⌜v⌝ zero) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Γ ⋘ A
⟦ v ⟧⁻¹ = ↓ (v refl⊩*)


----------------------------------------------------------------------------------------------------

⟦zero⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝
⟦zero⟧ = ⌜zero⌝

⟦suc⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝ ⌜⊃⌝ ⌜ℕ⌝
⟦suc⟧ e v = ⌜suc⌝ v

-- TODO: typo in Abel p.11
⟦rec⟧ : ∀ {Γ A} → Γ ⊩ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ (⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A) ⌜⊃⌝ A
⟦rec⟧ e ⌜zero⌝     e′ v₀ e″ vₛ = ren⊩ e″ v₀
⟦rec⟧ e (⌜suc⌝ vₙ) e′ v₀ e″ vₛ = vₛ refl⊆ (ren⋘ (trans⊆ e′ e″) vₙ) refl⊆ (⟦rec⟧ e vₙ e′ v₀ e″ vₛ)
⟦rec⟧ e (nnf tₙ)   e′ v₀ e″ vₛ = ↑ (⌜rec⌝ (ren⋙ (trans⊆ e′ e″) tₙ) (ren⋘ e″ (↓ v₀)) (↓ vₛ))

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
