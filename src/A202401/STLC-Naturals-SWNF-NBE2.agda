----------------------------------------------------------------------------------------------------

-- normalization-by-evaluation to β-short semi-weak normal form, with explicit model

-- unfortunately, the model needs to be split into two records in order to include a `⟦rec⟧` field
-- after the definition of `_⊩_`

module A202401.STLC-Naturals-SWNF-NBE2 where

open import A202401.STLC-Naturals-SWNF public
open import A202401.Kit4 public


----------------------------------------------------------------------------------------------------

record BaseModel : Set₁ where
  infix 4 _≤_
  field
    World  : Set
    _≤_    : World → World → Set
    refl≤  : ∀ {W} → W ≤ W
    trans≤ : ∀ {W W′ W″} → W ≤ W′ → W′ ≤ W″ → W ≤ W″
    ⟦ℕ⟧    : World → Set
    ren⟦ℕ⟧ : ∀ {W W′} → W ≤ W′ → ⟦ℕ⟧ W → ⟦ℕ⟧ W′
    ⟦zero⟧ : ∀ {W} → ⟦ℕ⟧ W
    ⟦suc⟧  : ∀ {W} → ⟦ℕ⟧ W → ⟦ℕ⟧ W

  infix 3 _⊩_
  _⊩_ : World → Ty → Set
  W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ≤ W′ → W′ ⊩ A → W′ ⊩ B
  W ⊩ ⌜ℕ⌝     = ⟦ℕ⟧ W

record SplitModel (ℬ : BaseModel) : Set₁ where
  open BaseModel ℬ public

  field
    ⟦rec⟧ : ∀ {W A} → W ⊩ ⌜ℕ⌝ → W ⊩ A → W ⊩ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A → W ⊩ A

open SplitModel public

module _ {ℬ} {ℳ : SplitModel ℬ} where
  private
    module ℳ = SplitModel ℳ

  vren : ∀ {A W W′} → W ℳ.≤ W′ → W ℳ.⊩ A → W′ ℳ.⊩ A
  vren {A ⌜⊃⌝ B} ϱ v = λ ϱ′ → v (ℳ.trans≤ ϱ ϱ′)
  vren {⌜ℕ⌝}     ϱ v = ℳ.ren⟦ℕ⟧ ϱ v

open SplitModelKit (kit _⊩_ (λ {ℬ} {ℳ} {A} → vren {ℬ} {ℳ} {A})) public

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var i                  ⟧         γ = ⟦ i ⟧∋ γ
⟦ ⌜λ⌝ t                  ⟧         γ = λ ϱ v → ⟦ t ⟧ (vren§ ϱ γ , v)
⟦ t₁ ⌜$⌝ t₂              ⟧ {ℳ = ℳ} γ = ⟦ t₁ ⟧ γ (refl≤ ℳ) $ ⟦ t₂ ⟧ γ
⟦ ⌜zero⌝                 ⟧ {ℳ = ℳ} γ = ⟦zero⟧ ℳ
⟦ ⌜suc⌝ t                ⟧ {ℳ = ℳ} γ = ⟦suc⟧ ℳ (⟦ t ⟧ γ)
⟦ ⌜rec⌝ {A = A} tₙ t₀ tₛ ⟧ {ℳ = ℳ} γ = ⟦rec⟧ ℳ {A = A} (⟦ tₙ ⟧ γ) (⟦ t₀ ⟧ γ) λ ϱ vₙ ϱ′ vₐ →
                                         ⟦ tₛ ⟧ ((vren§ (trans≤ ℳ ϱ ϱ′) γ , ren⟦ℕ⟧ ℳ ϱ′ vₙ) , vₐ)


----------------------------------------------------------------------------------------------------

ℬ : BaseModel
ℬ = record
      { World  = Ctx
      ; _≤_    = _⊑_
      ; refl≤  = refl⊑
      ; trans≤ = trans⊑
      ; ⟦ℕ⟧    = λ Γ → Σ (Γ ⊢ ⌜ℕ⌝) NF
      ; ren⟦ℕ⟧ = λ { ϱ (_ , p) → _ , renNF ϱ p }
      ; ⟦zero⟧ = _ , ⌜zero⌝
      ; ⟦suc⟧  = λ { (_ , p) → _ , ⌜suc⌝ p }
      }

-- canonical model
mutual
  𝒞 : SplitModel ℬ
  𝒞 .⟦rec⟧         (_ , ⌜zero⌝)   v₀ vₛ = v₀
  𝒞 .⟦rec⟧         (_ , ⌜suc⌝ pₙ) v₀ vₛ = vₛ id⊑ (_ , pₙ) id⊑ v₀
  𝒞 .⟦rec⟧ {A = A} (_ , nnf pₙ)   v₀ vₛ = let _ , p₀ = ↓ {A} v₀
                                              _ , pₛ = ↓ (vₛ (wk⊑ (wk⊑ id⊑))
                                                         (↑ {⌜ℕ⌝} (var (wk∋ zero) , var-))
                                                         id⊑ (↑ {A} (var zero , var-)))
                                            in ↑ (_ , ⌜rec⌝ pₙ p₀ pₛ)

  ↑ : ∀ {A Γ} → Σ (Γ ⊢ A) NNF → 𝒞 / Γ ⊩ A
  ↑ {A ⌜⊃⌝ B} (_ , p₁) = λ ϱ v₂ → let _ , p₂ = ↓ v₂
                                     in ↑ (_ , renNNF ϱ p₁ ⌜$⌝ p₂)
  ↑ {⌜ℕ⌝}     (_ , p)  = _ , nnf p

  ↓ : ∀ {A Γ} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {A ⌜⊃⌝ B} v = let t , p = ↓ (v (wk⊑ id⊑) (↑ {A} (var zero , var-)))
                    in ⌜λ⌝ t , ⌜λ⌝-
  ↓ {⌜ℕ⌝}     v = v

vid§ : ∀ {Γ} → 𝒞 / Γ ⊩§ Γ
vid§ {∙}     = ∙
vid§ {Γ , A} = vren§ (wk⊑ id⊑) vid§ , ↑ {A} (var zero , var-)

⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v vid§)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
