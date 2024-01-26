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
ren⊩ {A = ⌜ℕ⌝}     e (t , p) = ren e t , renNF e p

open ConcreteKit _⊩_ (λ {_} {_} {A} → ren⊩ {_} {_} {A}) public


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → Γ ⊩ A
  ↑ {A = A ⌜⊃⌝ B} (t , p) = λ e v → ↑ (_ , renNNF e p ⌜$⌝ proj₂ (↓ v))
  ↑ {A = ⌜ℕ⌝}     (t , p) = t , nnf p

  ↓ : ∀ {Γ A} → Γ ⊩ A → Σ (Γ ⊢ A) λ t → NF t
  ↓ {A = A ⌜⊃⌝ B} v with ↓ (v wk⊆ (↑ (⌜v⌝ zero , ⌜v⌝-)))
  ... | t , p         = ⌜λ⌝ t , ⌜λ⌝-
  ↓ {A = ⌜ℕ⌝}     v = v

refl⊩* : ∀ {Γ} → Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ (⌜v⌝ zero , ⌜v⌝-) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v refl⊩*)


----------------------------------------------------------------------------------------------------

⟦zero⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝
⟦zero⟧ = ⌜zero⌝ , ⌜zero⌝

⟦suc⟧ : ∀ {Γ} → Γ ⊩ ⌜ℕ⌝ → Γ ⊩ ⌜ℕ⌝
⟦suc⟧ (t′ , p′) = ⌜suc⌝ t′ , ⌜suc⌝ p′

⟦rec⟧ : ∀ {Γ A} → Γ ⊩ ⌜ℕ⌝ → Γ ⊩ A → A ∷ ⌜ℕ⌝ ∷ Γ ⊩ A → Γ ⊩ A
⟦rec⟧ (_ , ⌜zero⌝)    v₀ vₛ = v₀
⟦rec⟧ (_ , ⌜suc⌝ snd) v₀ vₛ = {!!}
⟦rec⟧ (_ , nnf pₙ)    v₀ vₛ = ↑ (_ , ⌜rec⌝ pₙ (proj₂ (↓ v₀)) (proj₂ (↓ vₛ)))

-- reflection
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ ⌜v⌝ i          ⟧ vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t          ⟧ vs = λ e v → ⟦ t ⟧ (v ∷ ren⊩* e vs)
⟦ t₁ ⌜$⌝ t₂      ⟧ vs = ⟦ t₁ ⟧ vs refl⊆ $ ⟦ t₂ ⟧ vs
⟦ ⌜zero⌝         ⟧ vs = ⟦zero⟧
⟦ ⌜suc⌝ t        ⟧ vs = ⟦suc⟧ (⟦ t ⟧ vs)
⟦ ⌜rec⌝ tₙ t₀ tₛ ⟧ vs = ⟦rec⟧ (⟦ tₙ ⟧ vs) (⟦ t₀ ⟧ vs) (⟦ tₛ ⟧ {!!})

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


----------------------------------------------------------------------------------------------------
