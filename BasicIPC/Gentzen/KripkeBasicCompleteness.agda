module BasicIPC.Gentzen.KripkeBasicCompleteness where

open import BasicIPC.Gentzen.KripkeSoundness public


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
  reflect {A ∧ B} t = ᴬᵍpair (reflect {A} (fst t)) (reflect {B} (snd t))
  reflect {⊤}    t = ᴬᵍtt

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {α P}   s = s
  reify {A ▷ B} s = lam (reify {B} (s weak⊆ (reflect {A} v₀)))
  reify {A ∧ B} s = pair (reify {A} (ᴬᵍfst s)) (reify {B} (ᴬᵍsnd s))
  reify {⊤}    s = tt

reflect⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ⊩⋆ Π
reflect⋆ {⌀}     ᴬᵍtt          = ᴬᵍtt
reflect⋆ {Π , A} (ᴬᵍpair ts t) = ᴬᵍpair (reflect⋆ ts) (reflect t)

reify⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ Π
reify⋆ {⌀}     ᴬᵍtt          = ᴬᵍtt
reify⋆ {Π , A} (ᴬᵍpair ts t) = ᴬᵍpair (reify⋆ ts) (reify t)


-- Additional useful properties.

multicut⊩ : ∀ {A Γ Γ′} → Γ ⊩⋆ Γ′ → Γ′ ⊩ A → Γ ⊩ A
multicut⊩ {A} {Γ′ = ⌀}      ᴬᵍtt          u = mono⊩ {A} bot⊆ u
multicut⊩ {A} {Γ′ = Γ′ , B} (ᴬᵍpair ts t) u = reflect {A} (app ts′ (reify {B} t))
  where ts′ = multicut⊢ (reify⋆ ts) (lam (reify {A} u))

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ {⌀}     = ᴬᵍtt
refl⊩⋆ {Γ , A} = ᴬᵍpair (mono⊩⋆ {Γ} weak⊆ refl⊩⋆) (reflect {A} v₀)

trans⊩⋆ : ∀ {Π Γ Γ′} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Π → Γ ⊩⋆ Π
trans⊩⋆ {⌀}     ts ᴬᵍtt          = ᴬᵍtt
trans⊩⋆ {Π , A} ts (ᴬᵍpair us u) = ᴬᵍpair (trans⊩⋆ ts us) (multicut⊩ {A} ts u)


-- Completeness, or quotation.

quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
quot t = reify (t refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
