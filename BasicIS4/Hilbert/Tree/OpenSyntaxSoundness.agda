module BasicIS4.Hilbert.Tree.OpenSyntaxSoundness where

open import BasicIS4.Hilbert.Tree public
open import BasicIS4.Hilbert.Translation public
open import BasicIS4.OpenSyntaxSemantics public

import BasicIS4.Hilbert.TreeWithContext as TC


-- Translated equipment.

ᵀmono⊢ : ∀ {Π Π′ A} → Π ⊆ Π′ → ⊢ Π ▻⋯▻ A → ⊢ Π′ ▻⋯▻ A
ᵀmono⊢ θ t = tc→t (TC.mono⊢ θ (t→tc t))

ᵀml : ∀ {Π Π′ A} → Π ⊆ Π′ → ⊢ □⋆ Π ▻⋯▻ A → ⊢ □⋆ Π′ ▻⋯▻ A
ᵀml = ᵀmono⊢ ∘ lift⊆

ᵀapp : ∀ {Π A B} → ⊢ Π ▻⋯▻ A ▻ B → ⊢ Π ▻⋯▻ A → ⊢ Π ▻⋯▻ B
ᵀapp {Π} t u = tc→t (TC.app {Π} (t→tc t) (t→tc u))

ᵀk₁ : ∀ {Π A B} → ⊢ Π ▻⋯▻ A → ⊢ Π ▻⋯▻ B ▻ A
ᵀk₁ {Π} t = tc→t (TC.app {Π} TC.ck (t→tc t))

ᵀs₁ : ∀ {Π A B C} → ⊢ Π ▻⋯▻ A ▻ B ▻ C → ⊢ Π ▻⋯▻ (A ▻ B) ▻ A ▻ C
ᵀs₁ {Π} t = tc→t (TC.app {Π} TC.cs (t→tc t))

ᵀs₂ : ∀ {Π A B C} → ⊢ Π ▻⋯▻ A ▻ B ▻ C → ⊢ Π ▻⋯▻ A ▻ B → ⊢ Π ▻⋯▻ A ▻ C
ᵀs₂ {Π} t u = tc→t (TC.app {Π} (TC.app TC.cs (t→tc t)) (t→tc u))

ᵀdist₁ : ∀ {Π A B} → ⊢ Π ▻⋯▻ □ (A ▻ B) → ⊢ Π ▻⋯▻ □ A ▻ □ B
ᵀdist₁ {Π} t = tc→t (TC.app {Π} TC.cdist (t→tc t))

ᵀpair₁ : ∀ {Π A B} → ⊢ Π ▻⋯▻ A → ⊢ Π ▻⋯▻ B ▻ A ∧ B
ᵀpair₁ {Π} t = tc→t (TC.app {Π} TC.cpair (t→tc t))

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
  eval (box {A} t)      = λ θ₀ → ᵀml θ₀ t , mono⊨ {A} bot⊆ (eval t)
  eval cdist            = λ _ □f θ □a {Δ′} θ′ →
                          let t , f = □f (trans⊆ θ θ′)
                              u , a = □a θ′
                          in  ᵀapp {□⋆ Δ′} t u , f refl⊆ a
  eval (cup {A})        = λ _ □a {Δ′} θ →
                          let t , a = □a θ
                          in  ᵀcxdown {Δ′} (ᵀlift {□⋆ Δ′} t) , (λ θ′ →
                                ᵀml θ′ t , mono⊨ {A} θ′ a)
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

  eval : ∀ {A} → ⊢ A → ᴹ⊨ A
  eval (app t u)        = let _ , f = (eval t) refl⊆
                          in  f (eval u)
  eval ci               = λ θ₀ → ᵀml θ₀ ci , id
  eval (ck {A})         = λ θ₀ → ᵀml θ₀ ck , (λ a {Δ″} θ →
                            ᵀk₁ {□⋆ Δ″} (ᵀml θ (reify {A} a)) , (λ b →
                              mono⊨ {A} θ a))
  eval (cs {A} {B} {C}) = λ θ₀ → ᵀml θ₀ cs , (λ f {Δ″} θ →
                          let t , f′ = f θ
                          in  ᵀs₁ {□⋆ Δ″} (ᵀml θ (reify {A ▻ B ▻ C} f)) , (λ g {Δ‴} θ′ →
                              let _ , f″ = f (trans⊆ θ θ′)
                                  u , g′ = g θ′
                              in  ᵀs₂ {□⋆ Δ‴} (ᵀml (trans⊆ θ θ′) (reify {A ▻ B ▻ C} f))
                                              (ᵀml θ′ (reify {A ▻ B} g)) , (λ a →
                                  let _ , h = (f″ a) refl⊆
                                      b     = g′ a
                                  in  h b)))
  eval (box {A} t)      = λ θ₀ → ᵀml θ₀ t , mono⊨ {A} bot⊆ (eval t)
  eval (cdist {A} {B})  = λ θ₀ → ᵀml θ₀ cdist , (λ □f {Δ″} θ →
                          let t , f = □f θ
                          in  ᵀdist₁ {□⋆ Δ″} (ᵀml θ (reify {□ (A ▻ B)} □f)) , (λ □a {Δ‴} θ′ →
                              let u  , a  = □a θ′
                                  t′ , f′ = f θ′
                              in  ᵀapp {□⋆ Δ‴} (ᵀml θ′ t) u , f′ a))
  eval (cup {A})        = λ θ₀ → ᵀml θ₀ cup , (λ □a {Δ″} θ →
                          let t , a = □a θ
                          in  ᵀcxdown {Δ″} (ᵀlift {□⋆ Δ″} t) , (λ θ′ →
                                ᵀml θ′ t , mono⊨ {A} θ′ a))
  eval cdown            = λ θ₀ → ᵀml θ₀ cdown , (λ □a →
                          let t , a = □a refl⊆
                          in  a)
  eval (cpair {A})      = λ θ₀ → ᵀml θ₀ cpair , (λ a {Δ″} θ →
                                    ᵀpair₁ {□⋆ Δ″} (ᵀml θ (reify {A} a)) , (λ b →
                                      mono⊨ {A} θ a , b))
  eval cfst             = λ θ₀ → ᵀml θ₀ cfst , π₁
  eval csnd             = λ θ₀ → ᵀml θ₀ csnd , π₂
  eval tt               = ∙
