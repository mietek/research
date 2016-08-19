module BasicIS4.Metatheory.Gentzen-TarskiGentzen where

open import BasicIS4.Syntax.Gentzen public
open import BasicIS4.Semantics.TarskiGentzen public


-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  mutual
    reflect[] : ∀ {A Γ} → Γ ⊢ A → [ Γ ⊢ A ]
    reflect[] (var i)         = [var] i
    reflect[] (lam t)         = [lam] (reflect[] t)
    reflect[] (app t u)       = [app] (reflect[] t) (reflect[] u)
    reflect[] (multibox ts u) = [multibox] ([⊢]⋆→[⊢⋆] (reflect[]⋆ ts)) (reflect[] u)
    reflect[] (down t)        = [down] (reflect[] t)
    reflect[] (pair t u)      = [pair] (reflect[] t) (reflect[] u)
    reflect[] (fst t)         = [fst] (reflect[] t)
    reflect[] (snd t)         = [snd] (reflect[] t)
    reflect[] tt              = [tt]

    reflect[]⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → [ Γ ⊢ Π ]⋆
    reflect[]⋆ {⌀}     ∙        = ∙
    reflect[]⋆ {Π , A} (ts , t) = reflect[]⋆ ts , reflect[] t


-- Additional useful equipment.

module _ {{_ : Model}} where
  [multicut] : ∀ {Π A Γ} → [ Γ ⊢ Π ]⋆ → [ Π ⊢ A ] → [ Γ ⊢ A ]
  [multicut] {⌀}     ∙        u = mono[⊢] bot⊆ u
  [multicut] {Π , B} (ts , t) u = [app] ([multicut] ts ([lam] u)) t


-- Soundness with respect to all models, or evaluation.

mutual
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
  eval (var i)         γ = lookup i γ
  eval (lam t)         γ = λ η →
                             let γ′ = mono⊩⋆ η γ
                             in  [multicut] (reify[]⋆ γ′) (reflect[] (lam t)) , λ a →
                                   eval t (γ′ , a)
  eval (app t u)       γ = eval t γ ⟪$⟫ eval u γ
  eval (multibox ts u) γ = λ η →
                             let γ′ = mono⊩⋆ η γ
                             in  [multicut] (reify[]⋆ γ′) (reflect[] (multibox ts u)) ,
                                   eval u (eval⋆ ts γ′)
  eval (down t)        γ = ⟪⇓⟫ (eval t γ)
  eval (pair t u)      γ = eval t γ , eval u γ
  eval (fst t)         γ = π₁ (eval t γ)
  eval (snd t)         γ = π₂ (eval t γ)
  eval tt              γ = ∙

  eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊨⋆ Π
  eval⋆ {⌀}     ∙        γ = ∙
  eval⋆ {Π , A} (ts , t) γ = eval⋆ ts γ , eval t γ


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

instance
  canon : Model
  canon = record
    { _⊩ᵅ_      = λ Γ P → Γ ⊢ α P
    ; mono⊩ᵅ    = mono⊢
    ; [_⊢_]     = _⊢_
    ; [_⊢⋆_]    = _⊢⋆_
    ; mono[⊢]   = mono⊢
    ; [var]      = var
    ; [lam]      = lam
    ; [app]      = app
    ; [multibox] = multibox
    ; [down]     = down
    ; [pair]     = pair
    ; [fst]      = fst
    ; [snd]      = snd
    ; [tt]       = tt
    ; top[⊢⋆]   = refl
    ; pop[⊢⋆]   = refl
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflect {α P}   t = t , t
  reflect {A ▻ B} t = λ η →
                        let t′ = mono⊢ η t
                        in  t′ , λ a → reflect (app t′ (reify a))
  reflect {□ A}   t = λ η →
                        let t′ = mono⊢ η t
                        in  t′ , reflect (down t′)
  reflect {A ∧ B} t = reflect (fst t) , reflect (snd t)
  reflect {⊤}    t = ∙

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} s       = let t , f = s refl⊆ in t
  reify {□ A}   s       = let t , a = s refl⊆ in t
  reify {A ∧ B} (a , b) = pair (reify a) (reify b)
  reify {⊤}    ∙       = tt

reflect⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊩⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t

reify⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ Π
reify⋆ {⌀}     ∙        = ∙
reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ = reflect⋆ refl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Γ″} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Γ″ → Γ ⊩⋆ Γ″
trans⊩⋆ ts us = reflect⋆ (trans⊢⋆ (reify⋆ ts) (reify⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
quot s = reify (s refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
