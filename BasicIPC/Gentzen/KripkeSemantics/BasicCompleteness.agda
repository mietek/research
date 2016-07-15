module BasicIPC.Gentzen.KripkeSemantics.BasicCompleteness where

open import BasicIPC.Gentzen.KripkeSemantics.Core public


-- The canonical model.

instance
  canon : Model
  canon = record
    { World   = Cx Ty
    ; _≤_     = _⊆_
    ; refl≤   = refl⊆
    ; trans≤  = trans⊆
    ; _⊩ᵅ_   = λ Γ P → Γ ⊢ α P
    ; mono⊩ᵅ = mono⊢
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflect {α P}   t = t
  reflect {A ▷ B} t = λ ξ a → reflect {B} (app (mono⊢ ξ t) (reify {A} a))
  reflect {⊤}    t = ᴬtt
  reflect {A ∧ B} t = ᴬpair (reflect {A} (fst t)) (reflect {B} (snd t))

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   s = s
  reify {A ▷ B} s = lam (reify {B} (s weak⊆ (reflect {A} (var top))))
  reify {⊤}    s = tt
  reify {A ∧ B} s = pair (reify {A} (ᴬfst s)) (reify {B} (ᴬsnd s))

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ {⌀}     = ᴬtt
refl⊩⋆ {Γ , A} = ᴬpair (mono⊩⋆ {Γ} weak⊆ refl⊩⋆) (reflect {A} (var top))


-- Completeness, or quotation.

quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
quot t = reify (t refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
