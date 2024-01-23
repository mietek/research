module STLC-Naturals-Weak-NotEtaLong-AbstractNbE where

open import STLC-Naturals-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

record Model : Set₁ where
  infix 4 _≤_
  field
    World  : Set
    Base   : World → Set
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
  W ⊩ `ℕ     = ∀ {W′} → W ℳ.≤ W′ → ℳ.Base W′

  ren⊩ : ∀ {W W′ A} → W ℳ.≤ W′ → W ⊩ A → W′ ⊩ A
  ren⊩ {A = A `⊃ B} e f = λ e′ → f (ℳ.trans≤ e e′)
  ren⊩ {A = `ℕ}     e f = λ e′ → f (ℳ.trans≤ e e′)

open AbstractKit (λ {ℳ} → _⊩_ {ℳ}) (λ {_} {_} {_} {A} → ren⊩ {_} {_} {_} {A}) public

-- -- reflection
-- ⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
-- ⟦ `v i          ⟧     vs = ⟦ i ⟧∋ vs
-- ⟦ `λ t          ⟧     vs = λ e v → ⟦ t ⟧ (v ∷ ren⊩* e vs)
-- ⟦ t₁ `$ t₂      ⟧ {ℳ} vs = ⟦ t₁ ⟧ vs (refl≤ ℳ) $ ⟦ t₂ ⟧ vs
-- ⟦ `zero         ⟧     vs = `zero , `zero
-- ⟦ `suc t        ⟧     vs = `suc (proj₁ (⟦ t ⟧ vs)) , `suc (proj₂ (⟦ t ⟧ vs))
-- ⟦ `rec t₁ t₂ t₃ ⟧     vs = {!⟦ t₃ ⟧ (? ∷ ? ∷ vs) !}
-- -- recℕ (⟦ t₁ ⟧ vs) (⟦ t₂ ⟧ vs) λ n v → ⟦ t₃ ⟧ (v ∷ n ∷ vs)


----------------------------------------------------------------------------------------------------

data NF* {Γ : Ctx} : ∀ {Δ} → Γ ⊢* Δ → Set where
  []  : NF* []
  _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} (p : NF t) (ps : NF* ts) → NF* (t ∷ ts)

data NNF* {Γ : Ctx} : ∀ {Δ} → Γ ⊢* Δ → Set where
  []  : NNF* []
  _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} (p : NNF t) (ps : NNF* ts) → NNF* (t ∷ ts)

renNNF* : ∀ {Γ Γ′ Δ} {ts : Γ ⊢* Δ} (e : Γ ⊆ Γ′) → NNF* ts → NNF* (ren* e ts)
renNNF* e []       = []
renNNF* e (p ∷ ps) = renNNF e p ∷ renNNF* e ps


----------------------------------------------------------------------------------------------------

-- canonical model
𝒞 : Model
𝒞 = record
      { World   = Ctx
      ; Base    = λ Γ → Σ (Γ ⊢ `ℕ) NNF
      ; _≤_     = _⊆_
      ; refl≤   = refl⊆
      ; trans≤  = trans⊆
      }

-- mutual
--   ↑ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → 𝒞 / Γ ⊩ A
--   ↑ {A = A `⊃ B} (t , p) = λ e v → ↑ (_ , renNNF e p `$ proj₂ (↓ v))
--   ↑ {A = `ℕ}     (t , p) = λ e → {!t , `nnf p!}

--   ↓ : ∀ {Γ A} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) λ t → NF t
--   ↓ {A = A `⊃ B} f with ↓ (f wk⊆ (↑ (`v zero , `v)))
--   ... | t , p        = `λ t , `λ
--   ↓ {A = `ℕ}     v = {!o!}

-- ↑* : ∀ {Γ Δ} {ts : Γ ⊢* Δ} → NNF* ts → 𝒞 / Γ ⊩* Δ
-- ↑* []       = []
-- ↑* (p ∷ ps) = ↑ (_ , p) ∷ ↑* ps

-- ↓* : ∀ {Γ Δ} → 𝒞 / Γ ⊩* Δ → Σ (Γ ⊢* Δ) λ ts → NF* ts
-- ↓* []       = [] , []
-- ↓* (v ∷ vs) = let t , p = ↓ v
--                   ts , ps = ↓* vs
--               in t ∷ ts , p ∷ ps

-- reflNNF* : ∀ {Γ} → NNF* (refl* {Γ})
-- reflNNF* {[]}    = []
-- reflNNF* {A ∷ Γ} = `v ∷ renNNF* wk⊆ reflNNF*

-- refl⊩* : ∀ {Γ} → 𝒞 / Γ ⊩* Γ
-- refl⊩* = ↑* reflNNF*

-- -- reification
-- ⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) NF
-- ⟦ v ⟧⁻¹ = ↓ (v refl⊩*)

-- -- nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) NF
-- -- nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


-- -- ----------------------------------------------------------------------------------------------------
