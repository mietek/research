module STLC-Naturals-Weak-NotEtaLong-NbE where

open import STLC-Naturals-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

record Model : Set₁ where
  infix 4 _≤_
  field
    World  : Set
    _≤_    : ∀ (W W′ : World) → Set
    refl≤  : ∀ {W} → W ≤ W
    trans≤ : ∀ {W W′ W″} (e : W ≤ W′) (e′ : W′ ≤ W″) → W ≤ W″

open Model public

module _ {ℳ : Model} where
  private
    module ℳ = Model ℳ

  infix 3 _⊩_
  _⊩_ : ∀ (W : ℳ.World) (A : Ty) → Set
  W ⊩ A `⊃ B = ∀ {W′} (e : W ℳ.≤ W′) (o : W′ ⊩ A) → W′ ⊩ B
  W ⊩ `ℕ     = ℕ

  mov : ∀ {W W′ A} (e : W ℳ.≤ W′) (v : W ⊩ A) → W′ ⊩ A
  mov {A = A `⊃ B} e f = λ e′ → f (ℳ.trans≤ e e′)
  mov {A = `ℕ}     e n = n

  infix 3 _⊩*_
  data _⊩*_ (W : ℳ.World) : ∀ (Δ : Ctx) → Set where
    []  : W ⊩* []
    _∷_ : ∀ {Δ A} (o : W ⊩ A) (os : W ⊩* Δ) → W ⊩* A ∷ Δ

  mov* : ∀ {W W′ Δ} (e : W ℳ.≤ W′) (vs : W ⊩* Δ) → W′ ⊩* Δ
  mov* e []                 = []
  mov* e (_∷_ {A = A} o os) = mov {A = A} e o ∷ mov* e os

infix 3 _∣_⊩_
_∣_⊩_ : ∀ (ℳ : Model) (W : World ℳ) (A : Ty) → Set
ℳ ∣ W ⊩ A = _⊩_ {ℳ} W A

infix 3 _∣_⊩*_
_∣_⊩*_ : ∀ (ℳ : Model) (W : World ℳ) (Δ : Ctx) → Set
ℳ ∣ W ⊩* Δ = _⊩*_ {ℳ} W Δ

infix 3 _⊨_
_⊨_ : ∀ (Γ : Ctx) (A : Ty) → Set₁
Γ ⊨ A = ∀ {ℳ : Model} {W : World ℳ} (os : ℳ ∣ W ⊩* Γ) → ℳ ∣ W ⊩ A

⟦_⟧∋ : ∀ {Γ A} (i : Γ ∋ A) → Γ ⊨ A
⟦ zero  ⟧∋ (o ∷ os) = o
⟦ suc i ⟧∋ (o ∷ os) = ⟦ i ⟧∋ os

⟦_⟧ : ∀ {Γ A} (d : Γ ⊢ A) → Γ ⊨ A
⟦ `v i          ⟧     os = ⟦ i ⟧∋ os
⟦ `λ d          ⟧     os = λ e o → ⟦ d ⟧ (o ∷ mov* e os)
⟦ d₁ `$ d₂      ⟧ {ℳ} os = ⟦ d₁ ⟧ os (refl≤ ℳ) $ ⟦ d₂ ⟧ os
⟦ `zero         ⟧     os = zero
⟦ `suc d        ⟧     os = suc (⟦ d ⟧ os)
⟦ `rec d₁ d₂ d₃ ⟧     os = recℕ (⟦ d₁ ⟧ os) (⟦ d₂ ⟧ os) λ n o → ⟦ d₃ ⟧ (o ∷ n ∷ os)

-- canonical model
𝒞 : Model
𝒞 = record
      { World  = Ctx
      ; _≤_    = _⊆_
      ; refl≤  = refl⊆
      ; trans≤ = trans⊆
      }

-- -- TODO: interpret `ℕ per Abel p.10 §2.3
-- mutual
--   ↓ : ∀ {Γ A} {d : Γ ⊢ A} (p : NNF d) → 𝒞 ∣ Γ ⊩ A
--   ↓ {A = A `⊃ B} p = λ e o → ↓ (renNNF e p `$ proj₂ (↑ o))
--   ↓ {A = `ℕ}     p = {!!}

--   ↑ : ∀ {Γ A} (v : 𝒞 ∣ Γ ⊩ A) → Σ (Γ ⊢ A) λ d → NF d
--   ↑ {A = A `⊃ B} f with ↑ (f wk⊆ (↓ (`v zero)))
--   ... | d , p        = `λ d , `λ d
--   ↑ {A = `ℕ}     n = {!!}

-- refl⊩* : ∀ {Γ} → 𝒞 ∣ Γ ⊩* Γ
-- refl⊩* {[]}    = []
-- refl⊩* {A ∷ Γ} = ↓ (`v zero) ∷ mov* wk⊆ refl⊩*

-- reify : ∀ {Γ A} (o : Γ ⊨ A) → Σ (Γ ⊢ A) λ d′ → NF d′
-- reify o = ↑ (o refl⊩*)

-- -- NOTE: we don't know whether d reduces to d′
-- nbe : ∀ {Γ A} (d : Γ ⊢ A) → Σ (Γ ⊢ A) λ d′ → NF d′
-- nbe = reify ∘ ⟦_⟧


-- ----------------------------------------------------------------------------------------------------
