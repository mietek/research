module STLC-Naturals2-Strong-EtaLong-ConcreteNBE where

open import STLC-Naturals2-Strong-EtaLong public


----------------------------------------------------------------------------------------------------

-- semantic values
infix 3 _⊩_
_⊩_ : Ctx → Ty → Set
W ⊩ `ℕ     = ∀ {W′} → W ⊆ W′ → W′ ⇇ `ℕ
W ⊩ A `⊃ B = ∀ {W′} → W ⊆ W′ → W′ ⊩ A → W′ ⊩ B

ren⊩ : ∀ {W W′ A} → W ⊆ W′ → W ⊩ A → W′ ⊩ A
ren⊩ {A = `ℕ}     e f = λ e′ → f (trans⊆ e e′)
ren⊩ {A = A `⊃ B} e f = λ e′ → f (trans⊆ e e′)

open ConcreteKit _⊩_ (λ {_} {_} {A} → ren⊩ {_} {_} {A}) public

mutual
  ↑ : ∀ {Γ A} → Γ ⇉ A → Γ ⊩ A
  ↑ {A = `ℕ}     t = λ e → `nnf (ren⇉ e t)
  ↑ {A = A `⊃ B} t = λ e v → ↑ (ren⇉ e t `$ ↓ v)

  ↓ : ∀ {Γ A} → Γ ⊩ A → Γ ⇇ A
  ↓ {A = `ℕ}     v = v refl⊆
  ↓ {A = A `⊃ B} f = `λ (↓ (f wk⊆ (↑ (`v zero))))

refl⊩* : ∀ {Γ} → Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ (`v zero) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Γ ⇇ A
⟦ v ⟧⁻¹ = ↓ (v refl⊩*)

-- -- TODO: typo in Abel p.11?
-- rec⊩* : ∀ {Γ A} → Γ ⊩ A `⊃ (`ℕ `⊃ A `⊃ A) `⊃ `ℕ `⊃ A
-- rec⊩* e f₀ e′ f₁ e″ f = f₁ {!!} (λ e‴ → {!v!}) {!!} (rec⊩* {!!} {!!} {!!} {!!} {!!} {!!})
-- -- zero:
-- -- ren⊩ (trans⊆ e′ e″) f₀

-- ⟦_⟧C : ∀ {Γ A} → Con A → Γ ⊨ A
-- ⟦ `zero ⟧C os = λ e → `zero
-- ⟦ `suc  ⟧C os = λ e f e′ → {!!}
-- ⟦ `rec  ⟧C os = {!!}

-- ⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
-- ⟦ `c k     ⟧ vs = ⟦ k ⟧C vs
-- ⟦ `v i     ⟧ vs = ⟦ i ⟧∋ vs
-- ⟦ `λ t     ⟧ vs = λ e v → ⟦ t ⟧ (v ∷ ren⊩* e vs)
-- ⟦ t₁ `$ t₂ ⟧ vs = ⟦ t₁ ⟧ vs refl⊆ $ ⟦ t₂ ⟧ vs

-- nbe : ∀ {Γ A} → Γ ⊢ A → Γ ⇇ A
-- nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


-- ----------------------------------------------------------------------------------------------------
