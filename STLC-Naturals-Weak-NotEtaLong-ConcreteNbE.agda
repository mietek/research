module STLC-Naturals-Weak-NotEtaLong-ConcreteNbE where

open import STLC-Naturals-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

-- semantic values
infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ A `⊃ B = ∀ {W′} → W ⊆ W′ → W′ ⊩ A → W′ ⊩ B
W ⊩ `ℕ     = ∀ {W′} → W ⊆ W′ → Σ (W′ ⊢ `ℕ) NF

ren⊩ : ∀ {W W′ A} → W ⊆ W′ → W ⊩ A → W′ ⊩ A
ren⊩ {A = A `⊃ B} e f = λ e′ → f (trans⊆ e e′)
ren⊩ {A = `ℕ}     e f = λ e′ → f (trans⊆ e e′)

open ConcreteKit _⊩_ (λ {_} {_} {A} → ren⊩ {_} {_} {A}) public

mutual
  ↑ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → Γ ⊩ A
  ↑ {A = A `⊃ B} (t , p) = λ e v → ↑ (_ , renNNF e p `$ proj₂ (↓ v))
  ↑ {A = `ℕ}     (t , p) = λ e → _ , `nnf (renNNF e p)

  ↓ : ∀ {Γ A} → Γ ⊩ A → Σ (Γ ⊢ A) λ t → NF t
  ↓ {A = A `⊃ B} f with ↓ (f wk⊆ (↑ (`v zero , `v)))
  ... | t , p        = `λ t , `λ
  ↓ {A = `ℕ}     v = v refl⊆

refl⊩* : ∀ {Γ} → Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ (`v zero , `v) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v refl⊩*)

-- recℕ : ∀ {𝓍} {X : Set 𝓍} → ℕ → X → (ℕ → X → X) → X
-- recℕ zero    z s = z
-- recℕ (suc n) z s = s n (recℕ n z s)

-- -- reflection
-- mutual
--   {-# TERMINATING #-}
--   ⟦rec⟧ : ∀ {Γ A} → Γ ⊨ `ℕ → Γ ⊨ A → A ∷ `ℕ ∷ Γ ⊨ A → Γ ⊨ A
--   ⟦rec⟧ o₁ o₂ o₃ os with o₁ os refl⊆
--   ⟦rec⟧ o₁ o₂ o₃ os | `zero , `zero = o₂ os
--   ⟦rec⟧ o₁ o₂ o₃ os | `suc t₁ , `suc p₁ = o₃ (⟦rec⟧ {!⟦ t₁ ⟧!} o₂ o₃ os ∷ (λ e → ren e t₁ , renNF e p₁) ∷ os)
--   ⟦rec⟧ o₁ o₂ o₃ os | t₁ , `nnf p₁ =
--     let t₂ , p₂ = ↓ (o₂ os)
--         t₃ , p₃ = ↓ (o₃ (aux os))
--     in  ↑ (`rec p₁ p₂ p₃)
--     where
--       aux : ∀ {W Γ A B} → W ⊩* Γ → A ∷ B ∷ W ⊩* A ∷ B ∷ Γ
--       aux os = ↑ (`v {i = zero}) ∷ (↑ (`v {i = suc zero}) ∷ ren⊩* (drop wk⊆) os)

--   ⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
--   ⟦ `v i          ⟧ os = ⟦ i ⟧∋ os
--   ⟦ `λ t          ⟧ os = λ e o → ⟦ t ⟧ (o ∷ ren⊩* e os)
--   ⟦ t₁ `$ t₂      ⟧ os = ⟦ t₁ ⟧ os refl⊆ $ ⟦ t₂ ⟧ os
--   ⟦ `zero         ⟧ os = λ e → `zero , `zero
--   ⟦ `suc t        ⟧ os = λ e → let t′ , p′ = ⟦ t ⟧ os e in `suc t′ , `suc p′
--   ⟦ `rec t₁ t₂ t₃ ⟧ os = ⟦rec⟧ ⟦ t₁ ⟧ ⟦ t₂ ⟧ ⟦ t₃ ⟧ os

-- nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
-- nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


-- ----------------------------------------------------------------------------------------------------
