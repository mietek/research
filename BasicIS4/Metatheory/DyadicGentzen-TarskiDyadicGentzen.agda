module BasicIS4.Metatheory.DyadicGentzen-TarskiDyadicGentzen where

open import BasicIS4.Syntax.DyadicGentzen public
open import BasicIS4.Semantics.TarskiDyadicGentzen public



-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  reflect[] : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → [ Γ ⁏ Δ ⊢ A ]
  reflect[] (var i)     = [var] i
  reflect[] (lam t)     = [lam] (reflect[] t)
  reflect[] (app t u)   = [app] (reflect[] t) (reflect[] u)
  reflect[] (mvar i)    = [mvar] i
  reflect[] (box t)     = [box] (reflect[] t)
  reflect[] (unbox t u) = [unbox] (reflect[] t) (reflect[] u)
  reflect[] (pair t u)  = [pair] (reflect[] t) (reflect[] u)
  reflect[] (fst t)     = [fst] (reflect[] t)
  reflect[] (snd t)     = [snd] (reflect[] t)
  reflect[] tt          = [tt]


-- Additional useful equipment.

module _ {{_ : Model}} where
  [mlam] : ∀ {A B Γ Δ} → [ Γ ⁏ Δ , A ⊢ B ] → [ Γ ⁏ Δ ⊢ □ A ▻ B ]
  [mlam] t = [lam] ([unbox] ([var] top) (mono[⊢] weak⊆ t))

  [multicut] : ∀ {Π A Γ Δ} → [ Γ ⁏ Δ ⊢ Π ]⋆ → [ Π ⁏ Δ ⊢ A ] → [ Γ ⁏ Δ ⊢ A ]
  [multicut] {⌀}     ∙        u = mono[⊢] bot⊆ u
  [multicut] {Π , B} (ts , t) u = [app] ([multicut] ts ([lam] u)) t

  [mmulticut] : ∀ {Π A Γ Δ} → [ Γ ⁏ Δ ⊢ □⋆ Π ]⋆ → [ Γ ⁏ Π ⊢ A ] → [ Γ ⁏ Δ ⊢ A ]
  [mmulticut] {⌀}     ∙        u = mmono[⊢] bot⊆ u
  [mmulticut] {Π , B} (ts , t) u = [app] ([mmulticut] ts ([mlam] u)) t

  [multicut²] : ∀ {Π Π′ A Γ Δ} → [ Γ ⁏ Δ ⊢ Π ]⋆ → [ Γ ⁏ Δ ⊢ □⋆ Π′ ]⋆ → [ Π ⁏ Π′ ⊢ A ] → [ Γ ⁏ Δ ⊢ A ]
  [multicut²] {⌀}     ∙        us v = [mmulticut] us (mono[⊢] bot⊆ v)
  [multicut²] {Π , B} (ts , t) us v = [app] ([multicut²] ts us ([lam] v)) t


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
eval (var i)     γ δ = lookup i γ
eval (lam t)     γ δ = λ η θ →
                         let γ′ = mono²⊩⋆ (η , θ) γ
                             δ′ = mono²⊩⋆ (η , θ) δ
                         in  [multicut²] (reify[]⋆ γ′) (reify[]⋆ δ′) (reflect[] (lam t)) , λ a →
                               eval t (γ′ , a) δ′
eval (app t u)   γ δ = eval t γ δ ⟪$⟫ eval u γ δ
eval (mvar i)    γ δ = mlookup i δ
eval (box t)     γ δ = λ η θ →
                         let γ′ = mono²⊩⋆ (η , θ) γ
                             δ′ = mono²⊩⋆ (η , θ) δ
                         in  [multicut²] (reify[]⋆ γ′) (reify[]⋆ δ′) (reflect[] (box t)) ,
                               eval t ∙ δ′
eval (unbox t u) γ δ = eval u γ (δ , eval t γ δ)
eval (pair t u)  γ δ = eval t γ δ , eval u γ δ
eval (fst t)     γ δ = π₁ (eval t γ δ)
eval (snd t)     γ δ = π₂ (eval t γ δ)
eval tt          γ δ = ∙


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
    ; [lam]     = lam
    ; [app]     = app
    ; [mvar]    = mvar
    ; [box]     = box
    ; [unbox]   = unbox
    ; [pair]    = pair
    ; [fst]     = fst
    ; [snd]     = snd
    ; [tt]      = tt
    }


-- Soundness with respect to the canonical model.

reflect : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊩ A
reflect {α P}   t = t , t
reflect {A ▻ B} t = λ η θ →
                      let t′ = mono²⊢ (η , θ) t
                      in  t′ , λ a → reflect (app t′ (reify[] a))
reflect {□ A}   t = λ η θ →
                      let t′ = mono²⊢ (η , θ) t
                      in  t′ , reflect (down t′)
reflect {A ∧ B} t = reflect (fst t) , reflect (snd t)
reflect {⊤}    t = ∙

reflect⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊢⋆ Π → Γ ⁏ Δ ⊩⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t


-- Completeness with respect to the canonical model.

reify : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ A
reify {α P}   (t , s) = t
reify {A ▻ B} s       = let t , f = s refl⊆ refl⊆ in t
reify {□ A}   s       = let t , a = s refl⊆ refl⊆ in t
reify {A ∧ B} (a , b) = pair (reify a) (reify b)
reify {⊤}    ∙       = tt

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
quot t = reify (t refl⊩⋆ mrefl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
norm = quot ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
