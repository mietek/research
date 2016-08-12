module BasicIS4.Gentzen.TreeWithContextPair.TarskiSoundness where

open import BasicIS4.Gentzen.TreeWithContextPair public
open import BasicIS4.TarskiSemantics public




-- Using satisfaction with a syntactic component, inspired by Gabbay and Nanevski.

module GabbayNanevskiSoundness where
  open GabbayNanevskiSemantics (⌀ ⁏ ⌀ ⊢_) (app) (box) public


  -- Completeness with respect to a particular model.

  -- FIXME: This formalisation seems to require a Coquand-Dybjer semantics.
  postulate
    oopsα : ∀ {P} → ⌀ ⁏ ⌀ ⊢ α P
    oops▻ : ∀ {A B} → ⌀ ⁏ ⌀ ⊢ A ▻ B

  reify : ∀ {{_ : Model}} {A} → ⊨ A → ⌀ ⁏ ⌀ ⊢ A
  reify {α P}   s        = oopsα
  reify {A ▻ B} s        = oops▻
  reify {□ A}   (t , □f) = box t
  reify {A ∧ B} (a , b)  = pair (reify {A} a) (reify {B} b)
  reify {⊤}    ∙        = tt

  reify⋆ : ∀ {{_ : Model}} {Π} → ⊨⋆ Π → ⌀ ⁏ ⌀ ⊢⋆ Π
  reify⋆ {⌀}     ∙        = ∙
  reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


  -- Soundness with respect to all models, or evaluation.

  -- FIXME: How to write this without translation?
  postulate
    oops : ∀ {A Δ} → ⌀ ⁏ Δ ⊢ A → ⌀ ⁏ ⌀ ⊢ A

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval (var i)     γ δ = lookup i γ
  eval (lam t)     γ δ = λ a → eval t (γ , a) δ
  eval (app t u)   γ δ = (eval t γ δ) (eval u γ δ)
  eval (mvar i)    γ δ = lookup i δ
  eval (box t)     γ δ = mmulticut (box⋆ (reify⋆ δ)) (down (box t)) ,
                         eval t ∙ δ
  eval (unbox t u) γ δ = eval u γ (δ , downˢ (eval t γ δ))
  eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
  eval (fst t)     γ δ = π₁ (eval t γ δ)
  eval (snd t)     γ δ = π₂ (eval t γ δ)
  eval tt          γ δ = ∙




-- Using satisfaction with a syntactic component, inspired by Coquand and Dybjer.

module CoquandDybjerSoundness where
  open CoquandDybjerSemantics (⌀ ⁏ ⌀ ⊢_) (app) (box) public


  -- Completeness with respect to a particular model.

  reify : ∀ {{_ : Model}} {A} → ⊨ A → ⌀ ⁏ ⌀ ⊢ A
  reify {α P}   (t , s)  = t
  reify {A ▻ B} (t , f)  = t
  reify {□ A}   (t , □f) = box t
  reify {A ∧ B} (a , b)  = pair (reify {A} a) (reify {B} b)
  reify {⊤}    ∙        = tt

  reify⋆ : ∀ {{_ : Model}} {Π} → ⊨⋆ Π → ⌀ ⁏ ⌀ ⊢⋆ Π
  reify⋆ {⌀}     ∙        = ∙
  reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval (var i)     γ δ = lookup i γ
  eval (lam t)     γ δ = multicut (reify⋆ γ) (mmulticut (box⋆ (reify⋆ δ)) (lam t)) , (λ a →
                           eval t (γ , a) δ)
  eval (app t u)   γ δ = (eval t γ δ) $ˢ (eval u γ δ)
  eval (mvar i)    γ δ = lookup i δ
  eval (box t)     γ δ = mmulticut (box⋆ (reify⋆ δ)) (down (box t)) ,
                         eval t ∙ δ
  eval (unbox t u) γ δ = eval u γ (δ , downˢ (eval t γ δ))
  eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
  eval (fst t)     γ δ = π₁ (eval t γ δ)
  eval (snd t)     γ δ = π₂ (eval t γ δ)
  eval tt          γ δ = ∙


  -- TODO: Correctness of evaluation with respect to conversion.
