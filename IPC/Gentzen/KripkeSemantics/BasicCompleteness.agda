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
    ; _⊪ᵅ_   = λ Γ P → Γ ⊢ α P
    ; mono⊪ᵅ = mono⊢
    ; _‼_     = λ Γ A → Γ ⊢ A
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
  reflect {α P}   t = return {α P} t
  reflect {A ▷ B} t = return {A ▷ B} (λ ξ a → reflect {B} (app (mono⊢ ξ t) (reify {A} a)))
  reflect {⊤}    t = return {⊤} ᴬtt
  reflect {A ∧ B} t = return {A ∧ B} (ᴬpair (reflect {A} (fst t)) (reflect {B} (snd t)))
  reflect {A ∨ B} t = λ ξ k → case (mono⊢ ξ t)
                                 (k weak⊆ (ᴬinl (reflect {A} (var top))))
                                 (k weak⊆ (ᴬinr (reflect {B} (var top))))
  reflect {⊥}    t = λ ξ k → boom (mono⊢ ξ t)

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   k = k refl≤ (λ ξ s → s)
  reify {A ▷ B} k = k refl≤ (λ ξ s → lam (reify {B} (s weak⊆ (reflect {A} (var top)))))
  reify {⊤}    k = k refl≤ (λ ξ s → tt)
  reify {A ∧ B} k = k refl≤ (λ ξ s → pair (reify {A} (ᴬfst s)) (reify {B} (ᴬsnd s)))
  reify {A ∨ B} k = k refl≤ (λ ξ s → ᴬcase s
                                        (λ a → inl (reify {A} (λ ξ′ k → a ξ′ k)))
                                        (λ b → inr (reify {B} (λ ξ′ k → b ξ′ k))))
  reify {⊥}    k = k refl≤ (λ ξ ())

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ {⌀}     = ᴬtt
refl⊩⋆ {Γ , A} = ᴬpair (mono⊩⋆ {Γ} weak⊆ refl⊩⋆) (reflect {A} (var top))


-- Completeness, or quotation.

quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
quot t = reify (t refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
