module New.BasicIS4.Metatheory.OpenDyadicHilbert-TarskiCoquandDybjerMk1 where

open import New.BasicIS4.Syntax.OpenDyadicHilbert public
open import New.BasicIS4.Semantics.TarskiCoquandDybjerMk1 public

open SyntacticComponent (λ Δ → ⌀ ⁏ Δ ⊢_)
                        (mmono⊢) public


-- Completeness with respect to a particular model.

reify : ∀ {{_ : Model}} {A Δ} → Δ ⊨ A → ⌀ ⁏ Δ ⊢ A
reify {α P}   (t , s) = t
reify {A ▻ B} s       = let t , f = s refl⊆
                        in  t
reify {□ A}   □a      = let t , a = □a refl⊆
                        in  lift t
reify {A ∧ B} (a , b) = pair (reify {A} a) (reify {B} b)
reify {⊤}    ∙       = tt


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ᴹ⊨ A
eval (var {A} i)  γ δ = mono⊨ {A} bot⊆ (lookup i γ)
eval (app t u)    γ δ = let _ , f = (eval t γ δ) refl⊆
                        in  f (eval u γ δ)
eval ci           γ δ = λ _ → ci , id
eval (ck {A})     γ δ = λ _ → ck , (λ a θ →
                          app ck (reify (mono⊨ {A} θ a)) , (λ b →
                            mono⊨ {A} θ a))
eval cs           γ δ = λ _ → cs , (λ f θ →
                        let t , f′ = f θ
                        in  app cs t , (λ g θ′ →
                            let _ , f″ = f (trans⊆ θ θ′)
                                u , g′ = g θ′
                            in  app (app cs (mmono⊢ θ′ t)) u , (λ a →
                                let _ , h = (f″ a) refl⊆
                                    b     = g′ a
                                in  h b)))
eval (mvar {A} i) γ δ = mono⊨ {A} bot⊆ (lookup i δ)
eval (box {A} t)  γ δ = λ θ → mmono⊢ θ t , mono⊨ {A} θ (eval t ∙ δ)
eval cdist        γ δ = λ _ → cdist , (λ □f θ →
                        let t , f = □f θ
                        in  app cdist (lift t) , (λ □a θ′ →
                            let u  , a  = □a θ′
                                t′ , f′ = f θ′
                            in  app t′ u , f′ a))
eval (cup {A})    γ δ = λ _ → cup , (λ □a θ →
                        let t , a = □a θ
                        in  lift t , (λ θ′ →
                            mmono⊢ θ′ t , mono⊨ {A} θ′ a))
eval cdown        γ δ = λ _ → cdown , (λ □a →
                        let t , a = □a refl⊆
                        in  a)
eval (cpair {A})  γ δ = λ _ → cpair , (λ a θ →
                          app cpair (reify (mono⊨ {A} θ a)) , (λ b →
                            mono⊨ {A} θ a , b))
eval cfst         γ δ = λ _ → cfst , π₁
eval csnd         γ δ = λ _ → csnd , π₂
eval tt           γ δ = ∙


-- The canonical model.

instance
  canon : Model
  canon = record
    { ⊨ᵅ_ = λ P → ⌀ ⁏ ⌀ ⊢ α P
    }


-- Completeness with respect to all models, or quotation.

-- FIXME: What is wrong here?
postulate
  quot : ∀ {A Γ Δ} → Γ ⁏ Δ ᴹ⊨ A → Γ ⁏ Δ ⊢ A


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
norm = quot ∘ eval
