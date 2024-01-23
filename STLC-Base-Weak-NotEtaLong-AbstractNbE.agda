module STLC-Base-Weak-NotEtaLong-AbstractNbE where

open import STLC-Base-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

record Model : Set₁ where
  field
    World   : Set
    Base    : World → Set
    _≤_     : World → World → Set
    refl≤   : ∀ {W} → W ≤ W
    trans≤  : ∀ {W W′ W″} → W ≤ W′ → W′ ≤ W″ → W ≤ W″
    renBase : ∀ {W W′} → W ≤ W′ → Base W → Base W′

open Model public

module _ {ℳ : Model} where
  private
    module ℳ = Model ℳ

  -- semantic values
  infix 3 _⊩_
  _⊩_ : ℳ.World → Ty → Set
  W ⊩ `◦     = ℳ.Base W
  W ⊩ A `⊃ B = ∀ {W′} → W ℳ.≤ W′ → W′ ⊩ A → W′ ⊩ B

  ren⊩ : ∀ {W W′ A} → W ℳ.≤ W′ → W ⊩ A → W′ ⊩ A
  ren⊩ {A = `◦}     e v = ℳ.renBase e v
  ren⊩ {A = A `⊃ B} e f = λ e′ → f (ℳ.trans≤ e e′)

open AbstractKit (λ {ℳ} → _⊩_ {ℳ}) (λ {_} {_} {_} {A} → ren⊩ {_} {_} {_} {A}) public

-- reflection
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ `v i     ⟧     vs = ⟦ i ⟧∋ vs
⟦ `λ t     ⟧     vs = λ e v → ⟦ t ⟧ (v ∷ ren⊩* e vs)
⟦ t₁ `$ t₂ ⟧ {ℳ} vs = ⟦ t₁ ⟧ vs (refl≤ ℳ) $ ⟦ t₂ ⟧ vs


----------------------------------------------------------------------------------------------------

-- canonical model
𝒞 : Model
𝒞 = record
      { World   = Ctx
      ; Base    = λ Γ → Σ (Γ ⊢ `◦) NNF
      ; _≤_     = _⊆_
      ; refl≤   = refl⊆
      ; trans≤  = trans⊆
      ; renBase = λ { e (t , p) → ren e t , renNNF e p }
      }

mutual
  ↑ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → 𝒞 / Γ ⊩ A
  ↑ {A = `◦}     (t , p) = t , p
  ↑ {A = A `⊃ B} (t , p) = λ e v → ↑ (_ , renNNF e p `$ proj₂ (↓ v))

  ↓ : ∀ {Γ A} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {A = `◦}     (t , p) = t , `nnf p
  ↓ {A = A `⊃ B} f       with ↓ (f wk⊆ (↑ (`v {A = A} zero , `v)))
  ... | t , p              = `λ t , `λ

refl⊩* : ∀ {Γ} → 𝒞 / Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ (`v {A = A} zero , `v) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v refl⊩*)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


----------------------------------------------------------------------------------------------------
