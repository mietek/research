module IPC.Gentzen.KripkeSemantics.BasicCompleteness where

open import IPC.Gentzen.KripkeSemantics.Core public


-- Canonical model.

instance
  canon : Model
  canon = record
    { World   = Cx Ty
    ; _≤_     = _⊆_
    ; refl≤   = refl⊆
    ; trans≤  = trans⊆
    ; _⊩ᴬ_   = λ Γ P → Γ ⊢ α P
    ; mono⊩ᴬ = mono⊢
    }


-- Soundness and completeness with respect to canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ᵀ A
  reflect {α P}   t = t
  reflect {A ⊃ B} t = λ ξ a → reflect {B} (app (mono⊢ ξ t) (reify {A} a))
  reflect {ι}     t = tt
  reflect {A ∧ B} t = reflect {A} (fst t) ∙ reflect {B} (snd t)

  reify : ∀ {A Γ} → Γ ⊩ᵀ A → Γ ⊢ A
  reify {α P}   s       = s
  reify {A ⊃ B} f       = lam (reify {B} (f weak⊆ (reflect {A} (var top))))
  reify {ι}     tt      = unit
  reify {A ∧ B} (a ∙ b) = pair (reify {A} a) (reify {B} b)

refl⊩ᴳ : ∀ {Γ} → Γ ⊩ᴳ Γ
refl⊩ᴳ {⌀}     = tt
refl⊩ᴳ {Γ , A} = mono⊩ᴳ {Γ} weak⊆ refl⊩ᴳ ∙ reflect {A} (var top)


-- Completeness with respect to all models, or quotation.

quot : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
quot t = reify (t refl⊩ᴳ)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
