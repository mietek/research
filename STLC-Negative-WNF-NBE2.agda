----------------------------------------------------------------------------------------------------

-- normalization by evaluation to β-short weak normal form
-- with an explicit model construction

module STLC-Negative-WNF-NBE2 where

open import STLC-Negative-WNF public
open import Kit4 public


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

  infix 3 _⊩_
  _⊩_ : ℳ.World → Ty → Set
  W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ℳ.≤ W′ → W′ ⊩ A → W′ ⊩ B
  W ⊩ A ⌜∧⌝ B = W ⊩ A × W ⊩ B
  W ⊩ ⌜𝟙⌝     = 𝟙

  vren : ∀ {A W W′} → W ℳ.≤ W′ → W ⊩ A → W′ ⊩ A
  vren {A ⌜⊃⌝ B} e v         = λ e′ → v (ℳ.trans≤ e e′)
  vren {A ⌜∧⌝ B} e (v₁ , v₂) = vren e v₁ , vren e v₂
  vren {⌜𝟙⌝}     e unit      = unit

open ModelKit (kit (λ {ℳ} → _⊩_ {ℳ}) (λ {ℳ} {A} → vren {ℳ} {A})) public

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var i     ⟧     vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t     ⟧     vs = λ e v → ⟦ t ⟧ (v ∷ vrens e vs)
⟦ t₁ ⌜$⌝ t₂ ⟧ {ℳ} vs = ⟦ t₁ ⟧ vs (refl≤ ℳ) $ ⟦ t₂ ⟧ vs
⟦ t₁ ⌜,⌝ t₂ ⟧     vs = ⟦ t₁ ⟧ vs , ⟦ t₂ ⟧ vs
⟦ ⌜fst⌝ t   ⟧     vs = fst (⟦ t ⟧ vs)
⟦ ⌜snd⌝ t   ⟧     vs = snd (⟦ t ⟧ vs)
⟦ ⌜unit⌝    ⟧     vs = unit


----------------------------------------------------------------------------------------------------

𝒞 : Model
𝒞 = record
      { World  = Ctx
      ; _≤_    = _⊆_
      ; refl≤  = refl⊆
      ; trans≤ = trans⊆
      }

mutual
  ↑ : ∀ {A Γ} → Σ (Γ ⊢ A) NNF → 𝒞 / Γ ⊩ A
  ↑ {A ⌜⊃⌝ B} (_ , p₁) = λ e v₂ → let _ , p₂ = ↓ v₂
                                     in ↑ (_ , renNNF e p₁ ⌜$⌝ p₂)
  ↑ {A ⌜∧⌝ B} (_ , p)  = ↑ (_ , ⌜fst⌝ p) , ↑ (_ , ⌜snd⌝ p)
  ↑ {⌜𝟙⌝}     (_ , p)  = unit

  ↓ : ∀ {A Γ} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {A ⌜⊃⌝ B} v         = let t , p = ↓ (v (wk⊆ id⊆) (↑ (var zero , var-)))
                            in ⌜λ⌝ t , ⌜λ⌝-
  ↓ {A ⌜∧⌝ B} (v₁ , v₂) = let t₁ , p₁ = ↓ v₁
                              t₂ , p₂ = ↓ v₂
                            in t₁ ⌜,⌝ t₂ , -⌜,⌝-
  ↓ {⌜𝟙⌝}     unit      = _ , ⌜unit⌝

vids : ∀ {Γ} → 𝒞 / Γ ⊩§ Γ
vids {[]}    = []
vids {A ∷ Γ} = ↑ (var zero , var-) ∷ vrens (wk⊆ id⊆) vids

⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v vids)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
