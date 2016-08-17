module BasicIS4.Metatheory.Hilbert-TarskiHilbert where

open import BasicIS4.Syntax.Hilbert public
open import BasicIS4.Semantics.TarskiHilbert public


-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  reflect[] : ∀ {A Γ} → Γ ⊢ A → [ Γ ⊢ A ]
  reflect[] (var i)   = [var] i
  reflect[] (app t u) = [app] (reflect[] t) (reflect[] u)
  reflect[] ci        = [ci]
  reflect[] ck        = [ck]
  reflect[] cs        = [cs]
  reflect[] (box t)   = [box] (reflect[] t)
  reflect[] cdist     = [cdist]
  reflect[] cup       = [cup]
  reflect[] cdown     = [cdown]
  reflect[] cpair     = [cpair]
  reflect[] cfst      = [cfst]
  reflect[] csnd      = [csnd]
  reflect[] tt        = [tt]


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → ∀ᴹ⊨ Γ ⇒ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ ⟪$⟫ eval u γ
eval ci        γ = const ([ci] , id)
eval ck        γ = const ([ck] , ⟪const⟫)
eval cs        γ = const ([cs] , ⟪ap⟫′)
eval (box t)   γ = reflect[] t , eval t ∙
eval cdist     γ = const ([cdist] , _⟪◎⟫′_)
eval cup       γ = const ([cup] , ⟪⇑⟫)
eval cdown     γ = const ([cdown] , ⟪⇓⟫)
eval cpair     γ = const ([cpair] , _⟪,⟫′_)
eval cfst      γ = const ([cfst] , π₁)
eval csnd      γ = const ([csnd] , π₂)
eval tt        γ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

instance
  canon : Model
  canon = record
    { _⊨ᵅ_    = λ Γ P → Γ ⊢ α P
    ; mono⊨ᵅ  = mono⊢
    ; [_⊢_]   = _⊢_
    ; mono[⊢] = mono⊢
    ; [var]    = var
    ; [app]    = app
    ; [ci]     = ci
    ; [ck]     = ck
    ; [cs]     = cs
    ; [box]    = box
    ; [cdist]  = cdist
    ; [cup]    = cup
    ; [cdown]  = cdown
    ; [cpair]  = cpair
    ; [cfst]   = cfst
    ; [csnd]   = csnd
    ; [tt]     = tt
    }


-- Soundness with respect to the canonical model.

-- FIXME: The semantics must be wrong...
postulate
  oops : ∀ {A Γ} → Γ ⊢ A → ⌀ ⊢ A

reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
reflect {α P}   t = t , t
reflect {A ▻ B} t = λ η → mono⊢ η t , λ a → reflect (app (mono⊢ η t) (reify[] a))
reflect {□ A}   t = oops (down t) , reflect (down t)
reflect {A ∧ B} t = reflect (fst t) , reflect (snd t)
reflect {⊤}    t = ∙

reflect⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊨⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t


-- Reflexivity and transitivity.

refl⊨⋆ : ∀ {Γ} → Γ ⊨⋆ Γ
refl⊨⋆ = reflect⋆ refl⊢⋆

-- TODO: Transitivity.


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → ∀ᴹ⊨ Γ ⇒ A → Γ ⊢ A
quot t = reify[] (t refl⊨⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
