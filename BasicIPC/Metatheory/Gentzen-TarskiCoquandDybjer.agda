module BasicIPC.Metatheory.Gentzen-TarskiCoquandDybjer where

open import BasicIPC.Syntax.Gentzen public
open import BasicIPC.Semantics.TarskiCoquandDybjer public

open SyntacticComponent (⌀ ⊢_) public


-- Completeness with respect to a particular model.

reify : ∀ {{_ : Model}} {A} → ⊨ A → ⌀ ⊢ A
reify {α P}   (t , s) = t
reify {A ▻ B} (t , f) = t
reify {A ∧ B} (a , b) = pair (reify {A} a) (reify {B} b)
reify {⊤}    ∙       = tt

reify⋆ : ∀ {{_ : Model}} {Π} → ⊨⋆ Π → ⌀ ⊢⋆ Π
reify⋆ {⌀}     ∙        = ∙
reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → ∀ᴹ⊨ Γ ⇒ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = multicut (reify⋆ γ) (lam t) , λ a →
                      eval t (γ , a)
eval (app t u)  γ = eval t γ ⟪$⟫ eval u γ
eval (pair t u) γ = eval t γ , eval u γ
eval (fst t)    γ = π₁ (eval t γ)
eval (snd t)    γ = π₂ (eval t γ)
eval tt         γ = ∙

-- Alternative version.
eval′ : ∀ {A Γ} → Γ ⊢ A → ∀ᴹ⊨ Γ ⇒ A
eval′ (var i)            γ = lookup i γ
eval′ (lam {A} {B} t)    γ = ⟦λ⟧ {A} {B} (multicut (reify⋆ γ) (lam t)) (eval t) γ
eval′ (app {A} {B} t u)  γ = _⟦$⟧_ {A} {B} (eval′ t) (eval′ u) γ
eval′ (pair {A} {B} t u) γ = _⟦,⟧_ {A} {B} (eval′ t) (eval′ u) γ
eval′ (fst {A} {B} t)    γ = ⟦π₁⟧ {A} {B} (eval′ t) γ
eval′ (snd {A} {B} t)    γ = ⟦π₂⟧ {A} {B} (eval′ t) γ
eval′ tt                 γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

instance
  canon : Model
  canon = record
    { ⊨ᵅ_ = λ P → ⌀ ⊢ α P
    }


-- Completeness with respect to all models, or quotation.

-- TODO: Can we do better here?
quot₀ : ∀ {A} → ∀ᴹ⊨ ⌀ ⇒ A → ⌀ ⊢ A
quot₀ t = reify (t ∙)


-- Normalisation by evaluation.

-- TODO: Can we do better here?
norm₀ : ∀ {A} → ⌀ ⊢ A → ⌀ ⊢ A
norm₀ = quot₀ ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
