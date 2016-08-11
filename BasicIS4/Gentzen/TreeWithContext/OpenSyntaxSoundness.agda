module BasicIS4.Gentzen.TreeWithContext.OpenSyntaxSoundness where

open import BasicIS4.Gentzen.TreeWithContext public
open import BasicIS4.OpenSyntaxSemantics public




-- Using satisfaction with a syntactic component, inspired by Gabbay and Nanevski.

module GabbayNanevskiSoundness where
  open GabbayNanevskiSemantics (λ Δ → □⋆ Δ ⊢_) public


  -- Soundness with respect to all models, or evaluation.

  -- FIXME: How to write this without translation?
  postulate
    oops₁ : ∀ {{_ : Model}} {A Δ} → Δ ⊨ A → ⌀ ⊨ A
    oops₂ : ∀ {A Δ Δ′} → □⋆ Δ ⊢ A → □⋆ Δ′ ⊢ A

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
    eval (var i)             γ = lookup i γ
    eval (lam {A} {B} t)     γ = λ _ a → mono⊨ {B} bot⊆ (eval t (γ , oops₁ {A} a))
    eval (app t u)           γ = (eval t γ) bot⊆ (eval u γ)
    eval (multibox {A} ts u) γ = λ _ → oops₂ u , mono⊨ {A} bot⊆ (eval u (eval⋆ ts γ))
    eval (down t)            γ = let s , a = (eval t γ) refl⊆
                                 in  a
    eval (pair t u)          γ = eval t γ , eval u γ
    eval (fst t)             γ = π₁ (eval t γ)
    eval (snd t)             γ = π₂ (eval t γ)
    eval tt                  γ = ∙

    eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊨⋆ Π
    eval⋆ {⌀}     ∙        γ = ∙
    eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ




-- Using satisfaction with a syntactic component, inspired by Coquand and Dybjer.

module CoquandDybjerSoundness where
  open CoquandDybjerSemantics (λ Δ → □⋆ Δ ⊢_)
                              (mono⊢ ∘ lift⊆) public


  -- Completeness with respect to a particular model.

  reify : ∀ {{_ : Model}} {A Δ} → Δ ⊨ A → □⋆ Δ ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} s       = let t , f = s refl⊆
                          in  t
  reify {□ A}   □a      = let t , a = □a refl⊆
                          in  cxdown (lift t)
  reify {A ∧ B} (a , b) = pair (reify {A} a) (reify {B} b)
  reify {⊤}    ∙       = tt


  -- Soundness with respect to all models, or evaluation.

  -- FIXME: How to write this without translation?
  postulate
    oops₀ : ∀ {A B Γ Δ′} → Γ , A ⊢ B → □⋆ Δ′ ⊢ A ▻ B
    oops₁ : ∀ {{_ : Model}} {A Δ} → Δ ⊨ A → ⌀ ⊨ A
    oops₂ : ∀ {A Δ Δ′} → □⋆ Δ ⊢ A → □⋆ Δ′ ⊢ A

  mutual
    eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
    eval (var i)             γ = lookup i γ
    eval (lam {A} {B} t)     γ = λ _ → oops₀ t , (λ a →
                                   mono⊨ {B} bot⊆ (eval t (γ , oops₁ {A} a)))
    eval (app t u)           γ = let t′ , f = (eval t γ) refl⊆
                                 in  f (eval u γ)
    eval (multibox {A} ts u) γ = λ _ → oops₂ u , mono⊨ {A} bot⊆ (eval u (eval⋆ ts γ))
    eval (down t)            γ = let s , a = (eval t γ) refl⊆
                                 in  a
    eval (pair t u)          γ = eval t γ , eval u γ
    eval (fst t)             γ = π₁ (eval t γ)
    eval (snd t)             γ = π₂ (eval t γ)
    eval tt                  γ = ∙

    eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊨⋆ Π
    eval⋆ {⌀}     ∙        γ = ∙
    eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ
