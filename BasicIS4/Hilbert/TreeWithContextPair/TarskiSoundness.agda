module BasicIS4.Hilbert.TreeWithContextPair.TarskiSoundness where

open import BasicIS4.Hilbert.TreeWithContextPair public
open import BasicIS4.TarskiSemantics public




-- Using satisfaction with a syntactic component, inspired by Gabbay and Nanevski.

module GabbayNanevskiSoundness where
  open GabbayNanevskiSemantics (⌀ ⁏ ⌀ ⊢_) (app) (box) public


  -- Soundness with respect to all models, or evaluation.

  -- FIXME: This formalisation seems to require a Coquand-Dybjer semantics.
  postulate
    oopsα : ∀ {P} → ⌀ ⁏ ⌀ ⊢ α P
    oops▻ : ∀ {A B} → ⌀ ⁏ ⌀ ⊢ A ▻ B

  reify : ∀ {{_ : Model}} {A} → ⊨ A → ⌀ ⁏ ⌀ ⊢ A
  reify {α P}   s       = oopsα
  reify {A ▻ B} s       = oops▻
  reify {□ A}   (t , s) = box t
  reify {A ∧ B} (a , b) = pair (reify {A} a) (reify {B} b)
  reify {⊤}    ∙       = tt

  reify⋆ : ∀ {{_ : Model}} {Π} → ⊨⋆ Π → ⌀ ⁏ ⌀ ⊢⋆ Π
  reify⋆ {⌀}     ∙        = ∙
  reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t

  eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
  eval (var i)   γ δ = lookup i γ
  eval (app t u) γ δ = (eval t γ δ) (eval u γ δ)
  eval ci        γ δ = id
  eval ck        γ δ = const
  eval cs        γ δ = ap
  eval (mvar i)  γ δ = lookup i δ
  eval (box t)   γ δ = mmulticut (box⋆ (reify⋆ δ)) t ,
                       eval t ∙ δ
  eval cdist     γ δ = distˢ
  eval cup       γ δ = upˢ
  eval cdown     γ δ = downˢ
  eval cpair     γ δ = _,_
  eval cfst      γ δ = π₁
  eval csnd      γ δ = π₂
  eval tt        γ δ = ∙




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
  eval (var i)   γ δ = lookup i γ
  eval (app t u) γ δ = (eval t γ δ) $ˢ eval u γ δ
  eval ci        γ δ = ci , id
  eval ck        γ δ = ck , (λ a →
                         app ck (reify a) ,
                           const a)
  eval cs        γ δ = cs , (λ f →
                         app cs (reify f) , (λ g →
                           app (app cs (reify f)) (reify g) , (λ a →
                             apˢ f g a)))
  eval (mvar i)  γ δ = lookup i δ
  eval (box t)   γ δ = mmulticut (box⋆ (reify⋆ δ)) t ,
                       eval t ∙ δ
  eval cdist     γ δ = cdist , (λ □f →
                         app cdist (reify □f) , (λ □a →
                           distˢ′ □f □a))
  eval cup       γ δ = cup , upˢ
  eval cdown     γ δ = cdown , downˢ
  eval cpair     γ δ = cpair , (λ a →
                         app cpair (reify a) , (λ b →
                           a , b))
  eval cfst      γ δ = cfst , π₁
  eval csnd      γ δ = csnd , π₂
  eval tt        γ δ = ∙


  -- TODO: Correctness of evaluation with respect to conversion.
