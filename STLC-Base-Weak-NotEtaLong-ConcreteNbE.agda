module STLC-Base-Weak-NotEtaLong-ConcreteNbE where

open import STLC-Base-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

-- semantic objects
infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ `◦     = Σ (W ⊢ `◦) NNF
W ⊩ A `⊃ B = ∀ {W′} → W ⊆ W′ → W′ ⊩ A → W′ ⊩ B

ren⊩ : ∀ {W W′ A} → W ⊆ W′ → W ⊩ A → W′ ⊩ A
ren⊩ {A = `◦}     e (t , p) = ren e t , renNNF e p
ren⊩ {A = A `⊃ B} e f       = λ e′ → f (trans⊆ e e′)

open ConcreteKit _⊩_ (λ {_} {_} {A} → ren⊩ {_} {_} {A}) public

-- reflection
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ `v i     ⟧ os = ⟦ i ⟧∋ os
⟦ `λ t     ⟧ os = λ e o → ⟦ t ⟧ (o ∷ ren⊩* e os)
⟦ t₁ `$ t₂ ⟧ os = ⟦ t₁ ⟧ os refl⊆ $ ⟦ t₂ ⟧ os


----------------------------------------------------------------------------------------------------

mutual
  ↑ : ∀ {Γ A} {t : Γ ⊢ A} → NNF t → Γ ⊩ A
  ↑ {A = `◦}     p = _ , p
  ↑ {A = A `⊃ B} p = λ e o → ↑ (renNNF e p `$ proj₂ (↓ o))

  ↓ : ∀ {Γ A} → Γ ⊩ A → Σ (Γ ⊢ A) λ t → NF t
  ↓ {A = `◦}     (t , p) = t , `nnf p
  ↓ {A = A `⊃ B} f       with ↓ (f wk⊆ (↑ {A = A} (`v {i = zero})))
  ... | t , p              = `λ t , `λ

refl⊩* : ∀ {Γ} → Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ {A = A} (`v {i = zero}) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) λ t′ → NF t′
⟦ o ⟧⁻¹ = ↓ (o refl⊩*)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) λ t′ → NF t′
nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


----------------------------------------------------------------------------------------------------
