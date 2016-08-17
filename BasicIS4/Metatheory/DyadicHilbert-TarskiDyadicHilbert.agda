module BasicIS4.Metatheory.DyadicHilbert-TarskiDyadicHilbert where

open import BasicIS4.Syntax.DyadicHilbert public
open import BasicIS4.Semantics.TarskiDyadicHilbert public


-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  reflect[] : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → [ Γ ⁏ Δ ⊢ A ]
  reflect[] (var i)   = [var] i
  reflect[] (app t u) = [app] (reflect[] t) (reflect[] u)
  reflect[] ci        = [ci]
  reflect[] ck        = [ck]
  reflect[] cs        = [cs]
  reflect[] (mvar i)  = [mvar] i
  reflect[] (box t)   = [box] (reflect[] t)
  reflect[] cdist     = [cdist]
  reflect[] cup       = [cup]
  reflect[] cdown     = [cdown]
  reflect[] cpair     = [cpair]
  reflect[] cfst      = [cfst]
  reflect[] csnd      = [csnd]
  reflect[] tt        = [tt]

  -- FIXME: Ugh, records.
  postulate
    [mmulticut] : ∀ {Π A Γ Δ} → [ Γ ⁏ Δ ⊢ □⋆ Π ]⋆ → [ Γ ⁏ Π ⊢ A ] → [ Γ ⁏ Δ ⊢ A ]


-- Soundness with respect to all models, or evaluation.

mutual
  eval : ∀ {Δ A Γ} → Γ ⁏ Δ ⊢ A → ∀ᴹ⊨ Γ ⁏ Δ ⇒ A
  eval (var i)      γ δ = lookup i γ
  eval (app t u)    γ δ = eval t γ δ ⟪$⟫ eval u γ δ
  eval ci           γ δ = const₂ ([ci] , id)
  eval ck           γ δ = const₂ ([ck] , ⟪const⟫)
  eval cs           γ δ = const₂ ([cs] , ⟪ap⟫′)
  eval (mvar {A} i) γ δ = mono⊨ {A} bot⊆ (mlookup i δ)
  eval {Δ} (box t)  γ δ = λ η θ → let δ′ = mmono[⊢]⋆ {□⋆ Δ} θ (reify[]⋆ δ)
                                   in  [mmulticut] δ′ (reflect[] t) , eval t ∙ (mmono⊨⋆ θ δ)
  eval cdist        γ δ = const₂ ([cdist] , _⟪◎⟫′_)
  eval cup          γ δ = const₂ ([cup] , ⟪⇑⟫)
  eval cdown        γ δ = const₂ ([cdown] , ⟪⇓⟫)
  eval cpair        γ δ = const₂ ([cpair] , _⟪,⟫′_)
  eval cfst         γ δ = const₂ ([cfst] , π₁)
  eval csnd         γ δ = const₂ ([csnd] , π₂)
  eval tt           γ δ = ∙

  eval⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊢⋆ Π → ∀ᴹ⊨ Γ ⁏ Δ ⇒⋆ Π
  eval⋆ {⌀}     ∙        γ δ = ∙
  eval⋆ {Π , A} (ts , t) γ δ = eval⋆ ts γ δ , eval t γ δ


-- -- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

instance
  canon : Model
  canon = record
    { _⁏_⊨ᵅ_   = λ Γ Δ P → Γ ⁏ Δ ⊢ α P
    ; mono⊨ᵅ   = mono⊢
    ; mmono⊨ᵅ  = mmono⊢
    ; [_⁏_⊢_]  = _⁏_⊢_
    ; mono[⊢]  = mono⊢
    ; mmono[⊢] = mmono⊢
    ; [var]     = var
    ; [app]     = app
    ; [ci]      = ci
    ; [ck]      = ck
    ; [cs]      = cs
    ; [mvar]    = mvar
    ; [box]     = box
    ; [cdist]   = cdist
    ; [cup]     = cup
    ; [cdown]   = cdown
    ; [cpair]   = cpair
    ; [cfst]    = cfst
    ; [csnd]    = csnd
    ; [tt]      = tt
    }


-- Soundness with respect to the canonical model.

-- FIXME: Is the semantics wrong?
postulate
  oops : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → ⌀ ⁏ Δ ⊢ A

reflect : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
reflect {α P}   t = t , t
reflect {A ▻ B} t = λ η θ → mono²⊢ (η , θ) t , λ a → reflect (app (mono²⊢ (η , θ) t) (reify[] a))
reflect {□ A}   t = λ η θ → oops (down (mmono⊢ θ t)) , reflect (mono²⊢ (η , θ) (down t))
reflect {A ∧ B} t = reflect (fst t) , reflect (snd t)
reflect {⊤}    t = ∙

reflect⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊢⋆ Π → Γ ⁏ Δ ⊨⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t


-- Reflexivity and transitivity.

lose : ∀ {Π′ Π Γ Δ} → Γ ⁏ Δ ⊢⋆ Π ⧺ Π′ → Γ ⁏ Δ ⊢⋆ Π
lose {⌀}      ts       = ts
lose {Π′ , A} (ts , t) = lose {Π′} ts

refl⊢⋆′ : ∀ {Δ Γ} → Γ ⁏ Δ ⊢⋆ Γ
refl⊢⋆′ {Δ} = lose {□⋆ Δ} refl⊢⋆

mrefl⊢⋆′ : ∀ {Δ} → ⌀ ⁏ Δ ⊢⋆ □⋆ Δ
mrefl⊢⋆′ {Δ} = subst (λ Π → ⌀ ⁏ Δ ⊢⋆ Π) (id⧺ᵣ {Γ = □⋆ Δ}) refl⊢⋆

refl⊨⋆ : ∀ {Δ Γ} → Γ ⁏ Δ ⊨⋆ Γ
refl⊨⋆ = reflect⋆ refl⊢⋆′

mrefl⊨⋆ : ∀ {Δ} → ⌀ ⁏ Δ ⊨⋆ □⋆ Δ
mrefl⊨⋆ = reflect⋆ mrefl⊢⋆′

-- TODO: Transitivity.


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ Δ} → ∀ᴹ⊨ Γ ⁏ Δ ⇒ A → Γ ⁏ Δ ⊢ A
quot t = reify[] (t refl⊨⋆ mrefl⊨⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
