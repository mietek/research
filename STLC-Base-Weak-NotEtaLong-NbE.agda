module STLC-Base-Weak-NotEtaLong-NbE where

open import STLC-Base-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

record Model : Set₁ where
  field
    World   : Set
    Base    : World → Set
    _≤_     : World → World → Set
    refl≤   : ∀ {W} → W ≤ W
    trans≤  : ∀ {W W′ W″} → W ≤ W′ → W′ ≤ W″ → W ≤ W″
    movBase : ∀ {W W′} → W ≤ W′ → Base W → Base W′

open Model public

module _ {ℳ : Model} where
  private
    module ℳ = Model ℳ

  infix 3 _⊩_
  _⊩_ : ℳ.World → Ty → Set
  W ⊩ `◦     = ℳ.Base W
  W ⊩ A `⊃ B = ∀ {W′} → W ℳ.≤ W′ → W′ ⊩ A → W′ ⊩ B

  mov : ∀ {W W′ A} → W ℳ.≤ W′ → W ⊩ A → W′ ⊩ A
  mov {A = `◦}     e o = ℳ.movBase e o
  mov {A = A `⊃ B} e f = λ e′ → f (ℳ.trans≤ e e′)

open SemKit S⟨ (λ {ℳ} → _⊩_ {ℳ}) , (λ {_} {_} {_} {A} → mov {_} {_} {_} {A}) ⟩ public

⟦_⟧∋ : ∀ {Γ A} → Γ ∋ A → Γ ⊨ A
⟦ zero  ⟧∋ (o ∷ os) = o
⟦ suc i ⟧∋ (o ∷ os) = ⟦ i ⟧∋ os

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ `v i     ⟧     os = ⟦ i ⟧∋ os
⟦ `λ t     ⟧     os = λ e o → ⟦ t ⟧ (o ∷ mov* e os)
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
      ; movBase = λ { e (t , p) → ren e t , renNNF e p }
      }

mutual
  ↓ : ∀ {Γ A} {t : Γ ⊢ A} → NNF t → 𝒞 / Γ ⊩ A
  ↓ {A = `◦}     p = _ , p
  ↓ {A = A `⊃ B} p = λ e o → ↓ (renNNF e p `$ proj₂ (↑ o))

  ↑ : ∀ {Γ A} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) λ t → NF t
  ↑ {A = `◦}     (t , p) = t , `nnf p
  ↑ {A = A `⊃ B} f       with ↑ (f wk⊆ (↓ {A = A} (`v {i = zero})))
  ... | t , p              = `λ t , `λ

refl⊩* : ∀ {Γ} → 𝒞 / Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↓ {A = A} (`v {i = zero}) ∷ mov* wk⊆ refl⊩*

⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) λ t′ → NF t′
⟦ o ⟧⁻¹ = ↑ (o refl⊩*)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) λ t′ → NF t′
nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


----------------------------------------------------------------------------------------------------
