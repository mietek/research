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


-- Additional useful equipment.

module _ {{_ : Model}} where
  [mmulticut] : ∀ {Π A Γ Δ} → [ Γ ⁏ Δ ⊢ □⋆ Π ]⋆ → [ Γ ⁏ Π ⊢ A ] → [ Γ ⁏ Δ ⊢ A ]
  [mmulticut] {⌀}     ∙        u = mmono[⊢] bot⊆ u
  [mmulticut] {Π , B} (ts , t) u = [app] ([mmulticut] ts ([mlam] u)) t


-- Soundness with respect to all models, or evaluation.

eval : ∀ {Δ A Γ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)   γ δ = lookup i γ
eval (app t u) γ δ = eval t γ δ ⟪$⟫ eval u γ δ
eval ci        γ δ = const₂ ([ci] , id)
eval ck        γ δ = const₂ ([ck] , ⟪const⟫)
eval cs        γ δ = const₂ ([cs] , ⟪ap⟫′)
eval (mvar i)  γ δ = mlookup i δ
eval (box t)   γ δ = λ η θ →
                       let δ′ = mono²⊩⋆ (η , θ) δ
                       in  [mmulticut] (reify[]⋆ δ′) (reflect[] (box t)) ,
                             eval t ∙ δ′
eval cdist     γ δ = const₂ ([cdist] , _⟪◎⟫′_)
eval cup       γ δ = const₂ ([cup] , ⟪⇑⟫)
eval cdown     γ δ = const₂ ([cdown] , ⟪⇓⟫)
eval cpair     γ δ = const₂ ([cpair] , _⟪,⟫′_)
eval cfst      γ δ = const₂ ([cfst] , π₁)
eval csnd      γ δ = const₂ ([csnd] , π₂)
eval tt        γ δ = ∙


-- TODO: Correctness of evaluation with respect to conversion.


-- The canonical model.

instance
  canon : Model
  canon = record
    { _⁏_⊩ᵅ_   = λ Γ Δ P → Γ ⁏ Δ ⊢ α P
    ; mono⊩ᵅ   = mono⊢
    ; mmono⊩ᵅ  = mmono⊢
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
    ; [mlam]    = mlam
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊩ A
  reflect {α P}   t = t , t
  reflect {A ▻ B} t = λ η θ →
                        let t′ = mono²⊢ (η , θ) t
                        in  t′ , λ a → reflect (app t′ (reify a))
  reflect {□ A}   t = λ η θ →
                        let t′ = mono²⊢ (η , θ) t
                        in  t′ , reflect (down t′)
  reflect {A ∧ B} t = reflect (fst t) , reflect (snd t)
  reflect {⊤}    t = ∙

  reify : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} s       = let t , f = s refl⊆ refl⊆ in t
  reify {□ A}   s       = let t , a = s refl⊆ refl⊆ in t
  reify {A ∧ B} (a , b) = pair (reify a) (reify b)
  reify {⊤}    ∙       = tt

reflect⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊢⋆ Π → Γ ⁏ Δ ⊩⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t

reify⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊩⋆ Π → Γ ⁏ Δ ⊢⋆ Π
reify⋆ {⌀}     ∙        = ∙
reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ Γ
refl⊩⋆ = reflect⋆ refl⊢⋆

mrefl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ □⋆ Δ
mrefl⊩⋆ = reflect⋆ mrefl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Δ Δ′ Π} → Γ ⁏ Δ ⊩⋆ Γ′ ⧺ (□⋆ Δ′) → Γ′ ⁏ Δ′ ⊩⋆ Π → Γ ⁏ Δ ⊩⋆ Π
trans⊩⋆ ts us = reflect⋆ (trans⊢⋆ (reify⋆ ts) (reify⋆ us))


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊢ A
quot s = reify (s refl⊩⋆ mrefl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
