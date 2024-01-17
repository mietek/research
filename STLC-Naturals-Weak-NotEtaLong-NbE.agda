module STLC-Naturals-Weak-NotEtaLong-NbE where

open import STLC-Naturals-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

record Model : Set₁ where
  infix 4 _≤_
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
  W ⊩ A `⊃ B = ∀ {W′} → W ℳ.≤ W′ → W′ ⊩ A → W′ ⊩ B
  W ⊩ `ℕ     = ℳ.Base W

  mov : ∀ {W W′ A} → W ℳ.≤ W′ → W ⊩ A → W′ ⊩ A
  mov {A = A `⊃ B} e f = λ e′ → f (ℳ.trans≤ e e′)
  mov {A = `ℕ}     e o = ℳ.movBase e o

open SemKit (λ {ℳ} → _⊩_ {ℳ}) (λ {_} {_} {_} {A} → mov {_} {_} {_} {A}) public

⟦_⟧∋ : ∀ {Γ A} → Γ ∋ A → Γ ⊨ A
⟦ zero  ⟧∋ (o ∷ os) = o
⟦ suc i ⟧∋ (o ∷ os) = ⟦ i ⟧∋ os

-- ⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
-- ⟦ `v i          ⟧     os = ⟦ i ⟧∋ os
-- ⟦ `λ t          ⟧     os = λ e o → ⟦ t ⟧ (o ∷ mov* e os)
-- ⟦ t₁ `$ t₂      ⟧ {ℳ} os = ⟦ t₁ ⟧ os (refl≤ ℳ) $ ⟦ t₂ ⟧ os
-- ⟦ `zero         ⟧     os = {!!} -- zero
-- ⟦ `suc t        ⟧     os = {!!} -- suc (⟦ t ⟧ os)
-- ⟦ `rec t₁ t₂ t₃ ⟧     os = {!!} -- recℕ (⟦ t₁ ⟧ os) (⟦ t₂ ⟧ os) λ n o → ⟦ t₃ ⟧ (o ∷ n ∷ os)


-- ----------------------------------------------------------------------------------------------------

-- -- canonical model
-- 𝒞 : Model
-- 𝒞 = record
--       { World   = Ctx
--       ; Base    = λ Γ → Σ (Γ ⊢ `ℕ) NNF
--       ; _≤_     = _⊆_
--       ; refl≤   = refl⊆
--       ; trans≤  = trans⊆
--       ; movBase = λ { e (t , p) → ren e t , renNNF e p }
--       }

-- -- TODO: interpret `ℕ per Abel p.10 §2.3
-- mutual
--   ↓ : ∀ {Γ A} {t : Γ ⊢ A} (p : NNF t) → 𝒞 / Γ ⊩ A
--   ↓ {A = A `⊃ B} p = λ e o → ↓ (renNNF e p `$ proj₂ (↑ o))
--   ↓ {A = `ℕ}     p = {!!}

--   ↑ : ∀ {Γ A} (v : 𝒞 / Γ ⊩ A) → Σ (Γ ⊢ A) λ t → NF t
--   ↑ {A = A `⊃ B} f with ↑ (f wk⊆ (↓ {A = A} (`v {i = zero})))
--   ... | t , p        = `λ t , `λ
--   ↑ {A = `ℕ}     o = {!!}

-- refl⊩* : ∀ {Γ} → 𝒞 / Γ ⊩* Γ
-- refl⊩* {[]}    = []
-- refl⊩* {A ∷ Γ} = ↓ (`v {A = A} {i = zero}) ∷ mov* wk⊆ refl⊩*

-- ⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) λ t′ → NF t′
-- ⟦ o ⟧⁻¹ = ↑ (o refl⊩*)

-- nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) λ t′ → NF t′
-- nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


-- ----------------------------------------------------------------------------------------------------
