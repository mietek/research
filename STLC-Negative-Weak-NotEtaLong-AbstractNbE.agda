module STLC-Negative-Weak-NotEtaLong-AbstractNbE where

open import STLC-Negative-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

record Model : Set₁ where
  field
    World  : Set
    _≤_    : World → World → Set
    refl≤  : ∀ {W} → W ≤ W
    trans≤ : ∀ {W W′ W″} → W ≤ W′ → W′ ≤ W″ → W ≤ W″

open Model public

module _ {ℳ : Model} where
  private
    module ℳ = Model ℳ

  -- semantic values
  infix 3 _⊩_
  _⊩_ : ℳ.World → Ty → Set
  W ⊩ A `⊃ B = ∀ {W′} → W ℳ.≤ W′ → W′ ⊩ A → W′ ⊩ B
  W ⊩ A `∧ B = W ⊩ A × W ⊩ B
  W ⊩ `𝟙     = 𝟙

  ren⊩ : ∀ {W W′ A} → W ℳ.≤ W′ → W ⊩ A → W′ ⊩ A
  ren⊩ {A = A `⊃ B} e f         = λ e′ → f (ℳ.trans≤ e e′)
  ren⊩ {A = A `∧ B} e (v₁ , v₂) = ren⊩ e v₁ , ren⊩ e v₂
  ren⊩ {A = `𝟙}     e unit      = unit

open AbstractKit (λ {ℳ} → _⊩_ {ℳ}) (λ {_} {_} {_} {A} → ren⊩ {_} {_} {_} {A}) public

-- reflection
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ `v i     ⟧     vs = ⟦ i ⟧∋ vs
⟦ `λ t     ⟧     vs = λ e v → ⟦ t ⟧ (v ∷ ren⊩* e vs)
⟦ t₁ `$ t₂ ⟧ {ℳ} vs = ⟦ t₁ ⟧ vs (refl≤ ℳ) $ ⟦ t₂ ⟧ vs
⟦ t₁ `, t₂ ⟧     vs = ⟦ t₁ ⟧ vs , ⟦ t₂ ⟧ vs
⟦ `proj₁ t ⟧     vs = proj₁ (⟦ t ⟧ vs)
⟦ `proj₂ t ⟧     vs = proj₂ (⟦ t ⟧ vs)
⟦ `unit    ⟧     vs = unit


----------------------------------------------------------------------------------------------------

-- canonical model
𝒞 : Model
𝒞 = record
      { World  = Ctx
      ; _≤_    = _⊆_
      ; refl≤  = refl⊆
      ; trans≤ = trans⊆
      }

mutual
  ↑ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → 𝒞 / Γ ⊩ A
  ↑ {A = A `⊃ B} (t , p) = λ e v → ↑ (_ , renNNF e p `$ proj₂ (↓ v))
  ↑ {A = A `∧ B} (t , p) = ↑ (_ , `proj₁ p) , ↑ (_ , `proj₂ p)
  ↑ {A = `𝟙}     (t , p) = unit

  ↓ : ∀ {Γ A} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) λ t → NF t
  ↓ {A = A `⊃ B} f         with ↓ (f wk⊆ (↑ (`v zero , `v)))
  ... | t , p                = `λ t , `λ
  ↓ {A = A `∧ B} (v₁ , v₂) with ↓ v₁ | ↓ v₂
  ... | t₁ , p₁ | t₂ , p₂    = t₁ `, t₂ , _`,_
  ↓ {A = `𝟙}     unit      = `unit , `unit

refl⊩* : ∀ {Γ} → 𝒞 / Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ (`v zero , `v) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v refl⊩*)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


----------------------------------------------------------------------------------------------------
