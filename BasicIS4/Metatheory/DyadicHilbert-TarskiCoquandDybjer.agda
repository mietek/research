module BasicIS4.Metatheory.DyadicHilbert-TarskiCoquandDybjer where

open import BasicIS4.Syntax.DyadicHilbert public
open import BasicIS4.Semantics.TarskiCoquandDybjer public

open SyntacticComponent (⌀ ⁏ ⌀ ⊢_) (app) (box) public


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


-- The canonical model.

instance
  canon : Model
  canon = record
    { ⊨ᵅ_ = λ P → ⌀ ⁏ ⌀ ⊢ α P
    }


-- Completeness with respect to all models, or quotation.

-- TODO: Can we do better here?
quot₀ : ∀ {A} → ⌀ ⁏ ⌀ ᴹ⊨ A → ⌀ ⁏ ⌀ ⊢ A
quot₀ t = reify (t ∙ ∙)


-- Normalisation by evaluation.

-- TODO: Can we do better here?
norm₀ : ∀ {A} → ⌀ ⁏ ⌀ ⊢ A → ⌀ ⁏ ⌀ ⊢ A
norm₀ = quot₀ ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
