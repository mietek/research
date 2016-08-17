module BasicIPC.Metatheory.Hilbert-TarskiHilbert where

open import BasicIPC.Syntax.Hilbert public
open import BasicIPC.Semantics.TarskiHilbert public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → ∀ᴹ⊨ Γ ⇒ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ ⟪$⟫ eval u γ
eval ci        γ = const ([ci] , id)
eval ck        γ = const ([ck] , ⟪const⟫)
eval cs        γ = const ([cs] , ⟪ap⟫′)
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
    ; [cpair]  = cpair
    ; [cfst]   = cfst
    ; [csnd]   = csnd
    ; [tt]     = tt
    }


-- Soundness with respect to the canonical model.

reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
reflect {α P}   t = t , t
reflect {A ▻ B} t = λ η → mono⊢ η t , λ a → reflect (app (mono⊢ η t) (reify[] a))
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
