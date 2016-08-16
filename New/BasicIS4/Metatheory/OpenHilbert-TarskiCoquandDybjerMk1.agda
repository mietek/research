module New.BasicIS4.Metatheory.OpenHilbert-TarskiCoquandDybjerMk1 where

open import New.BasicIS4.Syntax.OpenHilbert public
open import New.BasicIS4.Semantics.TarskiCoquandDybjerMk1 public

open SyntacticComponent (λ Δ → □⋆ Δ ⊢_)
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

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
eval (var i)     γ = lookup i γ
eval (app t u)   γ = let _ , f = (eval t γ) refl⊆
                     in  f (eval u γ)
eval ci          γ = λ _ → ci , id
eval (ck {A})    γ = λ _ → ck , (λ a θ →
                       app ck (reify (mono⊨ {A} θ a)) , (λ b →
                         mono⊨ {A} θ a))
eval cs          γ = λ _ → cs , (λ f θ →
                     let t , f′ = f θ
                     in  app cs t , (λ g θ′ →
                         let _ , f″ = f (trans⊆ θ θ′)
                             u , g′ = g θ′
                         in  app (app cs (mono⊢ (lift⊆ θ′) t)) u , (λ a →
                             let _ , h = (f″ a) refl⊆
                                 b     = g′ a
                             in  h b)))
eval (box {A} t) γ = λ θ₀ → mono⊢ (lift⊆ θ₀) t , mono⊨ {A} bot⊆ (eval t ∙)
eval cdist       γ = λ _ → cdist , (λ □f θ →
                     let t , f = □f θ
                     in  app cdist (cxdown (lift t)) , (λ □a θ′ →
                         let u  , a  = □a θ′
                             t′ , f′ = f θ′
                         in  app t′ u , f′ a))
eval (cup {A})   γ = λ _ → cup , (λ □a θ →
                     let t , a = □a θ
                     in  cxdown (lift t) , (λ θ′ →
                           mono⊢ (lift⊆ θ′) t , mono⊨ {A} θ′ a))
eval cdown       γ = λ _ → cdown , (λ □a →
                     let t , a = □a refl⊆
                     in  a)
eval (cpair {A}) γ = λ _ → cpair , (λ a θ →
                       app cpair (reify (mono⊨ {A} θ a)) , (λ b →
                         mono⊨ {A} θ a , b))
eval cfst        γ = λ _ → cfst , π₁
eval csnd        γ = λ _ → csnd , π₂
eval tt          γ = ∙


-- The canonical model.

instance
  canon : Model
  canon = record
    { ⊨ᵅ_ = λ P → ⌀ ⊢ α P
    }


-- Completeness with respect to all models, or quotation.

-- FIXME: What is wrong here?
postulate
  quot : ∀ {A Γ} → Γ ᴹ⊨ A → Γ ⊢ A


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
