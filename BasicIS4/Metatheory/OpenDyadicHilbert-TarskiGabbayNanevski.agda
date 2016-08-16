module BasicIS4.Metatheory.OpenDyadicHilbert-TarskiGabbayNanevski where

open import BasicIS4.Syntax.OpenDyadicHilbert public
open import BasicIS4.Semantics.TarskiGabbayNanevski public

open SyntacticComponent (⌀ ⁏ ⌀ ⊢_) (app) (box) public


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
