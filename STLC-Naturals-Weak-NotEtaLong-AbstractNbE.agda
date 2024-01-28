module STLC-Naturals-Weak-NotEtaLong-AbstractNbE where

open import STLC-Naturals-Weak-NotEtaLong public


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

  -- semantic values
  infix 3 _⊩_
  _⊩_ : World → Ty → Set
  -- W ⊩ A ⌜⊃⌝ B = ∀ {W′} → W ≤ W′ → W′ ⊩ A → W′ ⊩ B
  -- W ⊩ ⌜ℕ⌝     = ⟦ℕ⟧ W
  W ⊩ A = recTy A
             (λ A recA B recB W → ∀ {W′} → W ≤ W′ → recA W′ → recB W′)
             (λ W → ⟦ℕ⟧ W)
             W

record SplitModel (ℳ◦ : BaseModel) : Set₁ where
  open BaseModel ℳ◦ public

  field
    ⟦rec⟧ : ∀ {W A} → W ⊩ ⌜ℕ⌝ → W ⊩ A → W ⊩ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A → W ⊩ A

open SplitModel public

module _ {ℳ◦} {ℳ : SplitModel ℳ◦} where
  private
    module ℳ = SplitModel ℳ

  ren⊩ : ∀ {W W′ A} → W ℳ.≤ W′ → W ℳ.⊩ A → W′ ℳ.⊩ A
  ren⊩ {A = A ⌜⊃⌝ B} e v = λ e′ → v (ℳ.trans≤ e e′)
  ren⊩ {A = ⌜ℕ⌝}     e v = ℳ.ren⟦ℕ⟧ e v

open SplitModelKit _⊩_ (λ {ℳ◦} {ℳ} {W} {W′} {A} → ren⊩ {ℳ◦} {ℳ} {A = A}) public

-- reflection
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ ⌜v⌝ i                  ⟧         vs = ⟦ i ⟧∋ vs
⟦ ⌜λ⌝ t                  ⟧         vs = λ e v → ⟦ t ⟧ (v ∷ ren⊩* e vs)
⟦ t₁ ⌜$⌝ t₂              ⟧ {ℳ = ℳ} vs = ⟦ t₁ ⟧ vs (refl≤ ℳ) $ ⟦ t₂ ⟧ vs
⟦ ⌜zero⌝                 ⟧ {ℳ = ℳ} vs = ⟦zero⟧ ℳ
⟦ ⌜suc⌝ t                ⟧ {ℳ = ℳ} vs = ⟦suc⟧ ℳ (⟦ t ⟧ vs)
⟦ ⌜rec⌝ {A = A} tₙ t₀ tₛ ⟧ {ℳ = ℳ} vs = ⟦rec⟧ ℳ {A = A} (⟦ tₙ ⟧ vs) (⟦ t₀ ⟧ vs) λ e vₙ e′ vₐ →
                                          ⟦ tₛ ⟧ (vₐ ∷ ren⟦ℕ⟧ ℳ e′ vₙ ∷ ren⊩* (trans≤ ℳ e e′) vs)


----------------------------------------------------------------------------------------------------

𝒞◦ : BaseModel
𝒞◦ = record
       { World  = Ctx
       ; _≤_    = _⊆_
       ; refl≤  = refl⊆
       ; trans≤ = trans⊆
       ; ⟦ℕ⟧    = λ Γ → Σ (Γ ⊢ ⌜ℕ⌝) NF
       ; ren⟦ℕ⟧ = λ { e (_ , p) → _ , renNF e p }
       ; ⟦zero⟧ = _ , ⌜zero⌝
       ; ⟦suc⟧  = λ { (_ , p′) → _ , ⌜suc⌝ p′ }
       }

-- canonical model
mutual
  𝒞 : SplitModel 𝒞◦
  𝒞 = record
        { ⟦rec⟧ =
            λ { {A = A} (_ , ⌜zero⌝)   v₀ vₛ → v₀
              ; {A = A} (_ , ⌜suc⌝ pₙ) v₀ vₛ → vₛ refl⊆ (_ , pₙ) refl⊆ v₀
              ; {A = A} (_ , nnf pₙ)   v₀ vₛ →
                  let _ , p₀ = ↓ {A = A} v₀
                      _ , pₛ = ↓ (vₛ (drop (drop refl⊆)) (↑ (⌜v⌝ {A = ⌜ℕ⌝} (suc zero) , ⌜v⌝-))
                                 refl⊆ (↑ (⌜v⌝ {A = A} zero , ⌜v⌝-))) in
                    ↑ (_ , ⌜rec⌝ pₙ p₀ pₛ)
              }
        }

  ↑ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → 𝒞 / Γ ⊩ A
  ↑ {A = A ⌜⊃⌝ B} (_ , p₁) = λ e v₂ → let _ , p₂ = ↓ v₂ in
                               ↑ (_ , renNNF e p₁ ⌜$⌝ p₂)
  ↑ {A = ⌜ℕ⌝}     (_ , p)  = _ , nnf p

  ↓ : ∀ {Γ A} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) NF
  ↓ {A = A ⌜⊃⌝ B} v = let t , p = ↓ (v wk⊆ (↑ (⌜v⌝ {A = A} zero , ⌜v⌝-))) in
                        ⌜λ⌝ t , ⌜λ⌝-
  ↓ {A = ⌜ℕ⌝}     v = v

refl⊩* : ∀ {Γ} → 𝒞 / Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↑ (⌜v⌝ {A = A} zero , ⌜v⌝-) ∷ ren⊩* wk⊆ refl⊩*

-- reification
⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
⟦ v ⟧⁻¹ = ↓ (v refl⊩*)

nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
nbe t = ⟦ ⟦ t ⟧ ⟧⁻¹


----------------------------------------------------------------------------------------------------
