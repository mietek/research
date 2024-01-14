module STLC-Base-Weak-NotEtaLong-NbE where

open import STLC-Base-Weak-NotEtaLong public


----------------------------------------------------------------------------------------------------

record Model : Set₁ where
  field
    World   : Set
    Base    : ∀ (W : World) → Set
    _≤_     : ∀ (W W′ : World) → Set
    refl≤   : ∀ {W} → W ≤ W
    trans≤  : ∀ {W W′ W″} (e : W ≤ W′) (e′ : W′ ≤ W″) → W ≤ W″
    movBase : ∀ {W W′} (e : W ≤ W′) (o : Base W) → Base W′

open Model public

module _ {ℳ : Model} where
  private module ℳ = Model ℳ

  infix 3 _⊩_
  _⊩_ : ∀ (W : ℳ.World) (A : Ty) → Set
  W ⊩ `∙     = ℳ.Base W
  W ⊩ A `⊃ B = ∀ {W′} (e : W ℳ.≤ W′) (o : W′ ⊩ A) → W′ ⊩ B

  mov : ∀ {W W′ A} (e : W ℳ.≤ W′) (o : W ⊩ A) → W′ ⊩ A
  mov {A = `∙}     e o = ℳ.movBase e o
  mov {A = A `⊃ B} e f = λ e′ → f (ℳ.trans≤ e e′)

  infix 3 _⊩*_
  data _⊩*_ (W : ℳ.World) : ∀ (Δ : Ctx) → Set where
    []  : W ⊩* []
    _∷_ : ∀ {Δ A} (o : W ⊩ A) (os : W ⊩* Δ) → W ⊩* A ∷ Δ

  mov* : ∀ {W W′ Δ} (e : W ℳ.≤ W′) (os : W ⊩* Δ) → W′ ⊩* Δ
  mov* e []                 = []
  mov* e (_∷_ {A = A} o os) = mov {A = A} e o ∷ mov* e os -- TODO: ugh

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
⟦ `v i     ⟧     os = ⟦ i ⟧∋ os
⟦ `λ d     ⟧     os = λ e o → ⟦ d ⟧ (o ∷ mov* e os)
⟦ d₁ `$ d₂ ⟧ {ℳ} os = ⟦ d₁ ⟧ os (refl≤ ℳ) $ ⟦ d₂ ⟧ os


----------------------------------------------------------------------------------------------------

-- canonical model
𝒞 : Model
𝒞 = record
      { World   = Ctx
      ; Base    = λ Γ → Σ (Γ ⊢ `∙) NNF
      ; _≤_     = _⊆_
      ; refl≤   = refl⊆
      ; trans≤  = trans⊆
      ; movBase = λ { e (d , p) → ren e d , renNNF e p }
      }

mutual
  ↓ : ∀ {Γ A} {d : Γ ⊢ A} (p : NNF d) → 𝒞 ∣ Γ ⊩ A
  ↓ {A = `∙}     p = _ , p
  ↓ {A = A `⊃ B} p = λ e o → ↓ (renNNF e p `$ proj₂ (↑ o))

  ↑ : ∀ {Γ A} (o : 𝒞 ∣ Γ ⊩ A) → Σ (Γ ⊢ A) λ d → NF d
  ↑ {A = `∙}     (d , p) = d , `nnf p
  ↑ {A = A `⊃ B} f       with ↑ (f wk⊆ (↓ {A = A} (`v zero))) -- TODO: ugh
  ... | d , p              = `λ d , `λ d

refl⊩* : ∀ {Γ} → 𝒞 ∣ Γ ⊩* Γ
refl⊩* {[]}    = []
refl⊩* {A ∷ Γ} = ↓ {A = A} (`v zero) ∷ mov* wk⊆ refl⊩* -- TODO: ugh

reify : ∀ {Γ A} (o : Γ ⊨ A) → Σ (Γ ⊢ A) λ d′ → NF d′
reify o = ↑ (o refl⊩*)

-- NOTE: we don't know whether d reduces to d′
nbe : ∀ {Γ A} (d : Γ ⊢ A) → Σ (Γ ⊢ A) λ d′ → NF d′
nbe = reify ∘ ⟦_⟧


----------------------------------------------------------------------------------------------------
