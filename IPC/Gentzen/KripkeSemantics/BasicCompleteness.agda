module IPC.Gentzen.KripkeSemantics.BasicCompleteness where

open import IPC.Gentzen.KripkeSemantics.Core public


-- The canonical model.

instance
  canon : Model
  canon = record
    { World   = Cx Ty
    ; _≤_     = _⊆_
    ; refl≤   = refl⊆
    ; trans≤  = trans⊆
    ; _⊩ᴬ_   = λ Γ P → Γ ⊢ ᴬ P
    ; mono⊩ᴬ = mono⊢
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ᵀ A
  reflect {ᴬ P}   t = t
  reflect {A ▷ B} t = λ ξ a → reflect {B} (app (mono⊢ ξ t) (reify {A} a))
  reflect {⫪}    t = tt
  reflect {A ∧ B} t = reflect {A} (fst t) ∙ reflect {B} (snd t)

  reify : ∀ {A Γ} → Γ ⊩ᵀ A → Γ ⊢ A
  reify {ᴬ P}   s       = s
  reify {A ▷ B} f       = lam (reify {B} (f weak⊆ (reflect {A} (var top))))
  reify {⫪}    tt      = unit
  reify {A ∧ B} (a ∙ b) = pair (reify {A} a) (reify {B} b)

refl⊩ᴳ : ∀ {Γ} → Γ ⊩ᴳ Γ
refl⊩ᴳ {⌀}     = tt
refl⊩ᴳ {Γ , A} = mono⊩ᴳ {Γ} weak⊆ refl⊩ᴳ ∙ reflect {A} (var top)


-- Completeness, or quotation.

quot : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
quot t = reify (t refl⊩ᴳ)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
