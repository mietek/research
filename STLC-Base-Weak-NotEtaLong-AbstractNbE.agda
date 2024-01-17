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

  -- semantic objects
  infix 3 _⊩_
  _⊩_ : ℳ.World → Ty → Set
  W ⊩ `◦     = ℳ.Base W
  W ⊩ A `⊃ B = ∀ {W′} → W ℳ.≤ W′ → W′ ⊩ A → W′ ⊩ B

  ren⊩ : ∀ {W W′ A} → W ℳ.≤ W′ → W ⊩ A → W′ ⊩ A
  ren⊩ {A = `◦}     e o = ℳ.renBase e o
  ren⊩ {A = A `⊃ B} e f = λ e′ → f (ℳ.trans≤ e e′)

open AbstractKit (λ {ℳ} → _⊩_ {ℳ}) (λ {_} {_} {_} {A} → ren⊩ {_} {_} {_} {A}) public

-- reflection
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ `v i     ⟧     os = ⟦ i ⟧∋ os
⟦ `λ t     ⟧     os = λ e o → ⟦ t ⟧ (o ∷ ren⊩* e os)
⟦ t₁ `$ t₂ ⟧ {ℳ} os = ⟦ t₁ ⟧ os (refl≤ ℳ) $ ⟦ t₂ ⟧ os


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
  ↑ : ∀ {Γ A} {t : Γ ⊢ A} → NNF t → 𝒞 / Γ ⊩ A
  ↑ {A = `◦}     p = _ , p
  ↑ {A = A `⊃ B} p = λ e o → ↑ (renNNF e p `$ proj₂ (↓ o))

  ↓ : ∀ {Γ A} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) λ t → NF t
  ↓ {A = `◦}     (t , p) = t , `nnf p
  ↓ {A = A `⊃ B} f       with ↓ (f wk⊆ (↑ {A = A} (`v {i = zero})))
  ... | t , p              = `λ t , `λ

refl⊩* : ∀ {Γ} → 𝒞 / Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ {A = A} (`v {i = zero}) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) λ t′ → NF t′
⟦ o ⟧⁻¹ = ↓ (o refl⊩*)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) λ t′ → NF t′
nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


----------------------------------------------------------------------------------------------------
