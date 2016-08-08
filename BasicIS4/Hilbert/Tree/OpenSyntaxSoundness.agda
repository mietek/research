module BasicIS4.Hilbert.Tree.OpenSyntaxSoundness where

open import BasicIS4.Hilbert.Tree public
open import BasicIS4.Hilbert.Translation public
open import BasicIS4.OpenSyntaxSemantics public

import BasicIS4.Hilbert.TreeWithContext as TC


-- Translated equipment.

ᵀmono⊢ : ∀ {Π Π′ A} → Π ⊆ Π′ → ⊢ Π ▻⋯▻ A → ⊢ Π′ ▻⋯▻ A
ᵀmono⊢ θ t = tc→t (TC.mono⊢ θ (t→tc t))

ᵀapp : ∀ {Π A B} → ⊢ Π ▻⋯▻ A ▻ B → ⊢ Π ▻⋯▻ A → ⊢ Π ▻⋯▻ B
ᵀapp {Π} t u = tc→t (TC.app {Π} (t→tc t) (t→tc u))

ᵀpair : ∀ {Π A B} → ⊢ Π ▻⋯▻ A → ⊢ Π ▻⋯▻ B → ⊢ Π ▻⋯▻ A ∧ B
ᵀpair {Π} t u = tc→t (TC.pair {_} {_} {Π} (t→tc t) (t→tc u))

ᵀlift : ∀ {Π A} → ⊢ Π ▻⋯▻ A → ⊢ □⋆ Π ▻⋯▻ □ A
ᵀlift {Π} t = tc→t (TC.lift {Π} (t→tc t))

ᵀcxdown : ∀ {Π A} → ⊢ □⋆ □⋆ Π ▻⋯▻ A → ⊢ □⋆ Π ▻⋯▻ A
ᵀcxdown {Π} t = tc→t (TC.cxdown {Π} (t→tc t))




-- Using satisfaction with a syntactic component, inspired by Gabbay and Nanevski.

module GabbayNanevskiSoundness where
  open GabbayNanevskiSemantics (λ Δ A → ⊢ □⋆ Δ ▻⋯▻ A) public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A} → ⊢ A → ᴹ⊨ A
  eval (app t u)        = (eval t) refl⊆ (eval u)
  eval ci               = λ _ → id
  eval (ck {A})         = λ _ a θ b → mono⊨ {A} θ a
  eval (cs {A} {B} {C}) = λ _ f θ g θ′ a →
                          let h = ((mono⊨ {A ▻ B ▻ C} (trans⊆ θ θ′) f) refl⊆ a) refl⊆
                              b = (mono⊨ {A ▻ B} θ′ g) refl⊆ a
                          in  h b
  eval (box {A} t)      = λ θ₀ → ᵀmono⊢ (lift⊆ θ₀) t , mono⊨ {A} bot⊆ (eval t)
  eval cdist            = λ _ □f θ □a {Δ′} θ′ →
                          let t , f = □f (trans⊆ θ θ′)
                              u , a = □a θ′
                          in  ᵀapp {□⋆ Δ′} t u , f refl⊆ a
  eval (cup {A})        = λ _ □a {Δ′} θ →
                          let t , a = □a θ
                          in  ᵀcxdown {Δ′} (ᵀlift {□⋆ Δ′} t) , (λ θ′ →
                                ᵀmono⊢ (lift⊆ θ′) t , mono⊨ {A} θ′ a)
  eval cdown            = λ _ □a →
                          let t , a = □a refl⊆
                          in  a
  eval (cpair {A})      = λ _ a θ b → mono⊨ {A} θ a , b
  eval cfst             = λ _ → π₁
  eval csnd             = λ _ → π₂
  eval tt               = ∙




-- Using satisfaction with a syntactic component, inspired by Coquand and Dybjer.

module CoquandDybjerSoundness where
  open CoquandDybjerSemantics (λ Δ A → ⊢ □⋆ Δ ▻⋯▻ A)
                              (λ {Δ} {Δ′} → ᵀmono⊢ {□⋆ Δ} {□⋆ Δ′} ∘ lift⊆) public


  -- Completeness with respect to a particular model.

  reify : ∀ {{_ : Model}} {A Δ} → Δ ⊨ A → ⊢ □⋆ Δ ▻⋯▻ A
  reify {α P}   {Δ} (t , s) = t
  reify {A ▻ B} {Δ} s       = let t , f = s refl⊆
                              in  t
  reify {□ A}   {Δ} □a      = let t , a = □a refl⊆
                              in  ᵀcxdown {Δ} (ᵀlift {□⋆ Δ} t)
  reify {A ∧ B} {Δ} (a , b) = ᵀpair {□⋆ Δ} (reify {A} a) (reify {B} b)
  reify {⊤}    {Δ} ∙       = ᵀmono⊢ {⌀} {□⋆ Δ} bot⊆ tt


  -- Soundness with respect to all models, or evaluation.

  -- TODO: Finish this.
  postulate
    eval : ∀ {A} → ⊢ A → ᴹ⊨ A
  -- eval (app t u)   = let _ , f = (eval t) refl⊆
  --                    in  f (eval u)
  -- eval ci          = λ θ₀ → ᵀmono⊢ (lift⊆ θ₀) ci , id
  -- eval (ck {A})    = λ θ₀ → ᵀmono⊢ (lift⊆ θ₀) ck , (λ a θ →
  --                      {!!} , (λ b →
  --                        mono⊨ {A} θ a))
  -- eval cs          = λ θ₀ → ᵀmono⊢ (lift⊆ θ₀) cs , (λ f θ →
  --                    let t , f′ = f θ
  --                    in  {!!} , (λ g θ′ →
  --                        let _ , f″ = f (trans⊆ θ θ′)
  --                            u , g′ = g θ′
  --                        in  {!!} , (λ a →
  --                            let _ , h = (f″ a) refl⊆
  --                                b     = g′ a
  --                            in  h b)))
  -- eval (box {A} t) = λ θ₀ → ᵀmono⊢ (lift⊆ θ₀) t , mono⊨ {A} bot⊆ (eval t)
  -- eval cdist       = λ θ₀ → ᵀmono⊢ (lift⊆ θ₀) cdist , (λ □f θ →
  --                    let t , f = □f θ
  --                    in  {!!} , (λ □a θ′ →
  --                        let u  , a  = □a θ′
  --                            t′ , f′ = f θ′
  --                        in  {!!} , f′ a))
  -- eval (cup {A})   = λ θ₀ → ᵀmono⊢ (lift⊆ θ₀) cup , (λ □a θ →
  --                    let t , a = □a θ
  --                    in  {!!} , (λ θ′ →
  --                          {!!} , mono⊨ {A} θ′ a))
  -- eval cdown       = λ θ₀ → ᵀmono⊢ (lift⊆ θ₀) cdown , (λ □a →
  --                    let t , a = □a refl⊆
  --                    in  a)
  -- eval (cpair {A}) = λ θ₀ → ᵀmono⊢ (lift⊆ θ₀) cpair , (λ a θ →
  --                              {!!} , (λ b →
  --                                mono⊨ {A} θ a , b))
  -- eval cfst        = λ θ₀ → ᵀmono⊢ (lift⊆ θ₀) cfst , π₁
  -- eval csnd        = λ θ₀ → ᵀmono⊢ (lift⊆ θ₀) csnd , π₂
  -- eval tt          = ∙
