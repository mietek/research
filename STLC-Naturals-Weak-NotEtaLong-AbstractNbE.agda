module STLC-Naturals-Weak-NotEtaLong-AbstractNbE where

open import STLC-Naturals-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

record Model : Set₁ where
  infix 4 _≤_
  field
    World  : Set
--    Base   : World → Set
    _≤_    : World → World → Set
    refl≤  : ∀ {W} → W ≤ W
    trans≤ : ∀ {W W′ W″} → W ≤ W′ → W′ ≤ W″ → W ≤ W″
--    movBase : ∀ {W W′} → W ≤ W′ → Base W → Base W′

open Model public

module _ {ℳ : Model} where
  private
    module ℳ = Model ℳ

  -- semantic objects
  infix 3 _⊩_
  _⊩_ : ℳ.World → Ty → Set
  W ⊩ A `⊃ B = ∀ {W′} → W ℳ.≤ W′ → W′ ⊩ A → W′ ⊩ B
  W ⊩ `ℕ     = Σ ([] ⊢ `ℕ) λ t → NF t

  ren⊩ : ∀ {W W′ A} → W ℳ.≤ W′ → W ⊩ A → W′ ⊩ A
  ren⊩ {A = A `⊃ B} e f = λ e′ → f (ℳ.trans≤ e e′)
  ren⊩ {A = `ℕ}     e o = o

open AbstractKit (λ {ℳ} → _⊩_ {ℳ}) (λ {_} {_} {_} {A} → ren⊩ {_} {_} {_} {A}) public

-- -- reflection
-- ⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
-- ⟦ `v i          ⟧     os = ⟦ i ⟧∋ os
-- ⟦ `λ t          ⟧     os = λ e o → ⟦ t ⟧ (o ∷ ren⊩* e os)
-- ⟦ t₁ `$ t₂      ⟧ {ℳ} os = ⟦ t₁ ⟧ os (refl≤ ℳ) $ ⟦ t₂ ⟧ os
-- ⟦ `zero         ⟧     os = `zero , `zero
-- ⟦ `suc t        ⟧     os = `suc (proj₁ (⟦ t ⟧ os)) , `suc (proj₂ (⟦ t ⟧ os))
-- ⟦ `rec t₁ t₂ t₃ ⟧     os = {!⟦ t₃ ⟧ (? ∷ ? ∷ os) !}
-- -- recℕ (⟦ t₁ ⟧ os) (⟦ t₂ ⟧ os) λ n o → ⟦ t₃ ⟧ (o ∷ n ∷ os)


-- ----------------------------------------------------------------------------------------------------

-- data NF* {Γ : Ctx} : ∀ {Δ} → Γ ⊢* Δ → Set where
--   []  : NF* []
--   _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} (p : NF t) (ps : NF* ts) → NF* (t ∷ ts)

-- data NNF* {Γ : Ctx} : ∀ {Δ} → Γ ⊢* Δ → Set where
--   []  : NNF* []
--   _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} (p : NNF t) (ps : NNF* ts) → NNF* (t ∷ ts)

-- renNNF* : ∀ {Γ Γ′ Δ} {ts : Γ ⊢* Δ} (e : Γ ⊆ Γ′) → NNF* ts → NNF* (ren* e ts)
-- renNNF* e []       = []
-- renNNF* e (p ∷ ps) = renNNF e p ∷ renNNF* e ps


-- ----------------------------------------------------------------------------------------------------

-- -- canonical model
-- 𝒞 : Model
-- 𝒞 = record
--       { World   = Ctx
-- --      ; Base    = λ Γ → Σ (Γ ⊢ `ℕ) NNF
--       ; _≤_     = _⊆_
--       ; refl≤   = refl⊆
--       ; trans≤  = trans⊆
-- --      ; ren⊩Base = λ { e (t , p) → ren e t , renNNF e p }
--       }

-- mutual
--   ↑ : ∀ {Γ A} {t : Γ ⊢ A} → NNF t → 𝒞 / Γ ⊩ A
--   ↑ {A = A `⊃ B}     p = λ e o → ↑ (renNNF e p `$ proj₂ (↓ o))
--   ↑ {A = `ℕ}     {t} p = {!t , `nnf p!}

--   ↓ : ∀ {Γ A} → 𝒞 / Γ ⊩ A → Σ (Γ ⊢ A) λ t → NF t
--   ↓ {A = A `⊃ B} f with ↓ (f wk⊆ (↑ (`v {i = zero})))
--   ... | t , p        = `λ t , `λ
--   ↓ {A = `ℕ}     o = {!o!}

-- ↑* : ∀ {Γ Δ} {ts : Γ ⊢* Δ} → NNF* ts → 𝒞 / Γ ⊩* Δ
-- ↑* []       = []
-- ↑* (p ∷ ps) = ↑ p ∷ ↑* ps

-- ↓* : ∀ {Γ Δ} → 𝒞 / Γ ⊩* Δ → Σ (Γ ⊢* Δ) λ ts → NF* ts
-- ↓* []       = [] , []
-- ↓* (o ∷ os) = let t , p = ↓ o
--                   ts , ps = ↓* os
--               in t ∷ ts , p ∷ ps

-- reflNNF* : ∀ {Γ} → NNF* (refl* {Γ})
-- reflNNF* {[]}    = []
-- reflNNF* {A ∷ Γ} = `v ∷ renNNF* wk⊆ reflNNF*

-- refl⊩* : ∀ {Γ} → 𝒞 / Γ ⊩* Γ
-- refl⊩* = ↑* reflNNF*

-- -- reification
-- ⟦_⟧⁻¹ : ∀ {Γ A} → Γ ⊨ A → Σ (Γ ⊢ A) λ t′ → NF t′
-- ⟦ o ⟧⁻¹ = ↓ (o refl⊩*)

-- nbe : ∀ {Γ A} → Γ ⊢ A → Σ (Γ ⊢ A) λ t′ → NF t′
-- nbe = ⟦_⟧⁻¹ ∘ ⟦_⟧


-- ----------------------------------------------------------------------------------------------------
