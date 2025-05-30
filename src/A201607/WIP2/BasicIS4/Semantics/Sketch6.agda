{-# OPTIONS --allow-unsolved-metas --sized-types #-}

module A201607.WIP2.BasicIS4.Semantics.Sketch6 where

open import A201607.Common.Semantics public
open import A201607.BasicIS4.Syntax.Common public


record Model : Set₁ where
  infix 3 _[⊢]_ _[⊢ⁿᶠ]_
  field
    World : Set

    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    _R_    : World → World → Set
    reflR  : ∀ {w} → w R w
    transR : ∀ {w w′ w″} → w R w′ → w′ R w″ → w R w″

    ⌊_⌋ : World → World

    ≤→R   : ∀ {w w′} → w ≤ w′ → w R w′
    ≤→⌊≤⌋ : ∀ {w w′} → w ≤ w′ → ⌊ w ⌋ ≤ ⌊ w′ ⌋
    R→⌊≤⌋ : ∀ {w w′} → w R w′ → ⌊ w ⌋ ≤ ⌊ w′ ⌋

    lem₁ : ∀ {w} → ⌊ w ⌋ ≤ w
    lem₂ : ∀ {w} → ⌊ w ⌋ ≤ ⌊ ⌊ w ⌋ ⌋

    _[⊢]_   : World → Ty → Set
    mono[⊢] : ∀ {A w w′} → w ≤ w′ → w [⊢] A → w′ [⊢] A

    _[⊢ⁿᶠ]_ : World → Ty → Set

    _⊪ᵅ_   : World → Atom → Set
    mono⊪ᵅ : ∀ {P w w′} → w ≤ w′ → w ⊪ᵅ P → w′ ⊪ᵅ P

  infix 3 _[⊢]⋆_
  _[⊢]⋆_ : World → Cx Ty → Set
  w [⊢]⋆ ∅     = 𝟙
  w [⊢]⋆ Ξ , A = w [⊢]⋆ Ξ × w [⊢] A

  mono[⊢]⋆ : ∀ {Ξ w w′} → w ≤ w′ → w [⊢]⋆ Ξ → w′ [⊢]⋆ Ξ
  mono[⊢]⋆ {∅}     ξ ∙        = ∙
  mono[⊢]⋆ {Ξ , A} ξ (ts , t) = mono[⊢]⋆ ξ ts , mono[⊢] ξ t

  cor₁ : ∀ {w w′} → ⌊ w ⌋ ≤ ⌊ w′ ⌋ → ⌊ w ⌋ ≤ ⌊ ⌊ w′ ⌋ ⌋
  cor₁ ξ = trans≤ ξ lem₂

open Model {{…}} public


module _ {{_ : Model}} where
  mutual
    infix 3 _⊪_
    _⊪_ : World → Ty → Set
    w ⊪ α P   = w ⊪ᵅ P
    w ⊪ A ▻ B = ∀ {w′ : World} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
    w ⊪ □ A   = ∀ {w′ : World} → w R w′ → ⌊ w′ ⌋ [⊢] A × ⌊ w′ ⌋ ⊩ A
    w ⊪ A ∧ B = w ⊩ A × w ⊩ B
    w ⊪ ⊤    = 𝟙

    infix 3 _⊩_
    _⊩_ : World → Ty → Set
    w ⊩ A = ∀ {C} {w′ : World} → w ≤ w′ → (∀ {w″ : World} → w′ ≤ w″ → w″ ⊪ A → w″ [⊢ⁿᶠ] C) → w′ [⊢ⁿᶠ] C

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ∅     = 𝟙
  w ⊩⋆ Ξ , A = w ⊩⋆ Ξ × w ⊩ A


module _ {{_ : Model}} where
  mutual
    mono⊪ : ∀ {A} {w w′ : World} → w ≤ w′ → w ⊪ A → w′ ⊪ A
    mono⊪ {α P}   ξ s = mono⊪ᵅ ξ s
    mono⊪ {A ▻ B} ξ s = λ ξ′ a → s (trans≤ ξ ξ′) a
    mono⊪ {□ A}   ξ s = λ ζ′ → s (transR (≤→R ξ) ζ′)
    mono⊪ {A ∧ B} ξ s = mono⊩ {A} ξ (π₁ s) , mono⊩ {B} ξ (π₂ s)
    mono⊪ {⊤}    ξ s = ∙

    mono⊩ : ∀ {A} {w w′ : World} → w ≤ w′ → w ⊩ A → w′ ⊩ A
    mono⊩ ξ a = λ ξ′ k′ → a (trans≤ ξ ξ′) k′

  mono⊩⋆ : ∀ {Ξ} {w w′ : World} → w ≤ w′ → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ {∅}     ξ ∙       = ∙
  mono⊩⋆ {Ξ , A} ξ (γ , a) = mono⊩⋆ {Ξ} ξ γ , mono⊩ {A} ξ a


module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B} {w : World} → w ⊪ A ▻ B → w ⊩ A → w ⊩ B
  s ⟪$⟫ a = s refl≤ a

  return : ∀ {A} {w : World} → w ⊪ A → w ⊩ A
  return {A} a = λ ξ k → k refl≤ (mono⊪ {A} ξ a)

  bind : ∀ {A B} {w : World} → w ⊩ A → (∀ {w′ : World} → w ≤ w′ → w′ ⊪ A → w′ ⊩ B) → w ⊩ B
  bind a k = λ ξ k′ → a ξ (λ ξ′ a′ → k (trans≤ ξ ξ′) a′ refl≤ (λ ξ″ a″ → k′ (trans≤ ξ′ ξ″) a″))


infix 3 _⊨_
_⊨_ : Cx² Ty Ty → Ty → Set₁
Γ ⁏ Δ ⊨ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → ⌊ w ⌋ [⊢]⋆ Δ → ⌊ w ⌋ ⊩⋆ Δ → w ⊩ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx² Ty Ty → Cx Ty → Set₁
Γ ⁏ Δ ⊨⋆ Ξ = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → ⌊ w ⌋ [⊢]⋆ Δ → ⌊ w ⌋ ⊩⋆ Δ → w ⊩⋆ Ξ


module _ {{_ : Model}} where
  lookup : ∀ {A Γ} {w : World} → A ∈ Γ → w ⊩⋆ Γ → w ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ


open import A201607.BasicIS4.Syntax.DyadicGentzenNormalForm public


eval : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)             γ ד δ = lookup i γ
eval (lam {A} {B} t)     γ ד δ = return {A ▻ B} λ ξ a →
                                   eval t (mono⊩⋆ ξ γ , a)
                                          (mono[⊢]⋆ (≤→⌊≤⌋ ξ) ד)
                                          (mono⊩⋆ (≤→⌊≤⌋ ξ) δ)
eval (app {A} {B} t u)   γ ד δ = bind {A ▻ B} {B} (eval t γ ד δ) λ ξ f →
                                   _⟪$⟫_ {A} {B} f (eval u (mono⊩⋆ ξ γ)
                                                           (mono[⊢]⋆ (≤→⌊≤⌋ ξ) ד)
                                                           (mono⊩⋆ (≤→⌊≤⌋ ξ) δ))
eval (mvar {A} i)        γ ד δ = mono⊩ {A} lem₁ (lookup i δ)
eval {Γ} {Δ} (box {A} t) γ ד δ = return {□ A} λ ζ → {!!}
--                                   let ד′ = mono[⊢]⋆ (R→⌊≤⌋ ζ) ד
--                                       t′ = ?
--                                   in  {!!} ⅋ -- ugh₁ ד′ t′ ⅋
--                                     eval t ∙
--                                            (mono[⊢]⋆ (cor₁ (R→⌊≤⌋ ζ)) ד)
--                                            (mono⊩⋆ (cor₁ (R→⌊≤⌋ ζ)) δ)
eval (unbox {A} {C} t u) γ ד δ = bind {□ A} {C} (eval t γ ד δ) λ ξ a →
                                   eval u (mono⊩⋆ ξ γ)
                                          (mono[⊢]⋆ (≤→⌊≤⌋ ξ) ד , {!!}) -- syn (a reflR))
                                          (mono⊩⋆ (≤→⌊≤⌋ ξ) δ , {!!}) -- sem (a reflR))
eval (pair {A} {B} t u)  γ ד δ = return {A ∧ B} (eval t γ ד δ , eval u γ ד δ)
eval (fst {A} {B} t)     γ ד δ = bind {A ∧ B} {A} (eval t γ ד δ) (K π₁)
eval (snd {A} {B} t)     γ ד δ = bind {A ∧ B} {B} (eval t γ ד δ) (K π₂)
eval unit                γ ד δ = return {⊤} ∙

eval⋆ : ∀ {Ξ Γ} → Γ ⊢⋆ Ξ → Γ ⊨⋆ Ξ
eval⋆ {∅}     ∙        γ ד δ = ∙
eval⋆ {Ξ , A} (ts , t) γ ד δ = eval⋆ ts γ ד δ , eval t γ ד δ
