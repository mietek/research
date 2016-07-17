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
  reflect {A ∧ B} t = return {A ∧ B} (ᴬᵍpair (reflect {A} (fst t)) (reflect {B} (snd t)))
  reflect {⊤}    t = return {⊤} ᴬᵍtt
  reflect {⊥}    t = λ ξ k → boom (mono⊢ ξ t)
  reflect {A ∨ B} t = λ ξ k → case (mono⊢ ξ t)
                                 (k weak⊆ (ᴬᵍinl (reflect {A} v₀)))
                                 (k weak⊆ (ᴬᵍinr (reflect {B} (v₀))))

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   k = k refl≤ (λ ξ s → s)
  reify {A ▷ B} k = k refl≤ (λ ξ s → lam (reify {B} (s weak⊆ (reflect {A} (v₀)))))
  reify {A ∧ B} k = k refl≤ (λ ξ s → pair (reify {A} (ᴬᵍfst s)) (reify {B} (ᴬᵍsnd s)))
  reify {⊤}    k = k refl≤ (λ ξ s → tt)
  reify {⊥}    k = k refl≤ (λ ξ ())
  reify {A ∨ B} k = k refl≤ (λ ξ s → ᴬᵍcase s
                                        (λ a → inl (reify {A} (λ ξ′ k → a ξ′ k)))
                                        (λ b → inr (reify {B} (λ ξ′ k → b ξ′ k))))

reflect⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊩⋆ Π
reflect⋆ {⌀}     ᴬᵍtt          = ᴬᵍtt
reflect⋆ {Π , A} (ᴬᵍpair ts t) = ᴬᵍpair (reflect⋆ ts) (reflect t)

reify⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ Π
reify⋆ {⌀}     ᴬᵍtt          = ᴬᵍtt
reify⋆ {Π , A} (ᴬᵍpair ts t) = ᴬᵍpair (reify⋆ ts) (reify t)


-- Additional useful properties.

multicut⊩ : ∀ {Π A Γ} → Γ ⊩⋆ Π → Π ⊩ A → Γ ⊩ A
multicut⊩ {⌀}     {A} ᴬᵍtt          u = mono⊩ {A} bot⊆ u
multicut⊩ {Π , B} {A} (ᴬᵍpair ts t) u = reflect {A} (app ts′ (reify {B} t))
  where ts′ = multicut⊢ (reify⋆ ts) (lam (reify {A} u))

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ {⌀}     = ᴬᵍtt
refl⊩⋆ {Γ , A} = ᴬᵍpair (mono⊩⋆ {Γ} weak⊆ refl⊩⋆) (reflect {A} v₀)

trans⊩⋆ : ∀ {Π Γ Γ′} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Π → Γ ⊩⋆ Π
trans⊩⋆ {⌀}     ts ᴬᵍtt          = ᴬᵍtt
trans⊩⋆ {Π , A} ts (ᴬᵍpair us u) = ᴬᵍpair (trans⊩⋆ ts us) (multicut⊩ {A = A} ts u)


-- Completeness, or quotation.

quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
quot t = reify (t refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
