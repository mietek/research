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
    ; _⊪ᴬ_   = λ Γ P → Γ ⊢ ᴬ P
    ; mono⊪ᴬ = mono⊢
    ; _⁂_    = λ Γ A → Γ ⊢ A
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflect {ᴬ P}   t = return {ᴬ P} t
  reflect {A ▷ B} t = return {A ▷ B} (λ ξ a → reflect {B} (app (mono⊢ ξ t) (reify {A} a)))
  reflect {⫪}    t = return {⫪} tt
  reflect {A ∧ B} t = return {A ∧ B} (reflect {A} (fst t) ∙ reflect {B} (snd t))
  reflect {A ∨ B} t = λ ξ k → case (mono⊢ ξ t)
                                 (k weak⊆ (inj₁ (reflect {A} (var top))))
                                 (k weak⊆ (inj₂ (reflect {B} (var top))))
  reflect {⫫}    t = λ ξ k → boom (mono⊢ ξ t)

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {ᴬ P}   k = k refl≤ (λ ξ s   → s)
  reify {A ▷ B} k = k refl≤ (λ ξ f   → lam (reify {B} (f weak⊆ (reflect {A} (var top)))))
  reify {⫪}    k = k refl≤ (λ ξ u   → unit)
  reify {A ∧ B} k = k refl≤ (λ ξ a&b → pair (reify {A} (proj₁ a&b)) (reify {B} (proj₂ a&b)))
  reify {A ∨ B} k = k refl≤ (λ ξ a∣b → [ (λ a → inl (reify {A} (λ ξ′ k → a ξ′ k)))
                                        ∙ (λ b → inr (reify {B} (λ ξ′ k → b ξ′ k)))
                                        ] a∣b)
  reify {⫫}    k = k refl≤ (λ ξ ())

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ {⌀}     = tt
refl⊩⋆ {Γ , A} = mono⊩⋆ {Γ} weak⊆ refl⊩⋆ ∙ reflect {A} (var top)


-- Completeness, or quotation.

quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
quot t = reify (t refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
