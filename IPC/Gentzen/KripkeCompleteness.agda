module IPC.Gentzen.KripkeCompleteness where

open import IPC.Gentzen.KripkeSoundness public


-- Derivations, as Gentzen-style natural deduction trees.

mutual
  -- Normal forms, or introductions.
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ (Γ : Cx Ty) : Ty → Set where
    neⁿᶠ   : ∀ {A}   → Γ ⊢ⁿᵉ A → Γ ⊢ⁿᶠ A
    lamⁿᶠ  : ∀ {A B} → Γ , A ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ▷ B
    pairⁿᶠ : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∧ B
    ttⁿᶠ   : Γ ⊢ⁿᶠ ⊤
    inlⁿᶠ  : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ A ∨ B
    inrⁿᶠ  : ∀ {A B} → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∨ B

  -- Neutrals, or eliminations.
  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ (Γ : Cx Ty) : Ty → Set where
    varⁿᵉ  : ∀ {A}     → A ∈ Γ → Γ ⊢ⁿᵉ A
    appⁿᵉ  : ∀ {A B}   → Γ ⊢ⁿᵉ A ▷ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᵉ B
    fstⁿᵉ  : ∀ {A B}   → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ A
    sndⁿᵉ  : ∀ {A B}   → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ B
    boomⁿᵉ : ∀ {C}     → Γ ⊢ⁿᵉ ⊥ → Γ ⊢ⁿᵉ C
    caseⁿᵉ : ∀ {A B C} → Γ ⊢ⁿᵉ A ∨ B → Γ , A ⊢ⁿᶠ C → Γ , B ⊢ⁿᶠ C → Γ ⊢ⁿᵉ C

infix 3 _⊢⋆ⁿᶠ_
_⊢⋆ⁿᶠ_ : Cx Ty → Cx Ty → Set
Γ ⊢⋆ⁿᶠ ⌀     = ᴬᵍ⊤
Γ ⊢⋆ⁿᶠ Π , A = Γ ⊢⋆ⁿᶠ Π ᴬᵍ∧ Γ ⊢ⁿᶠ A

infix 3 _⊢⋆ⁿᵉ_
_⊢⋆ⁿᵉ_ : Cx Ty → Cx Ty → Set
Γ ⊢⋆ⁿᵉ ⌀     = ᴬᵍ⊤
Γ ⊢⋆ⁿᵉ Π , A = Γ ⊢⋆ⁿᵉ Π ᴬᵍ∧ Γ ⊢ⁿᵉ A


-- Translation to simple terms.

mutual
  nf→tm : ∀ {A Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)
  nf→tm ttⁿᶠ         = tt
  nf→tm (inlⁿᶠ t)    = inl (nf→tm t)
  nf→tm (inrⁿᶠ t)    = inr (nf→tm t)

  ne→tm : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ A
  ne→tm (varⁿᵉ i)      = var i
  ne→tm (appⁿᵉ t u)    = app (ne→tm t) (nf→tm u)
  ne→tm (fstⁿᵉ t)      = fst (ne→tm t)
  ne→tm (sndⁿᵉ t)      = snd (ne→tm t)
  ne→tm (boomⁿᵉ t)     = boom (ne→tm t)
  ne→tm (caseⁿᵉ t u v) = case (ne→tm t) (nf→tm u) (nf→tm v)


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ⁿᶠ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᶠ A → Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ η (neⁿᶠ t)     = neⁿᶠ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᶠ η (lamⁿᶠ t)    = lamⁿᶠ (mono⊢ⁿᶠ (keep η) t)
  mono⊢ⁿᶠ η (pairⁿᶠ t u) = pairⁿᶠ (mono⊢ⁿᶠ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᶠ η ttⁿᶠ         = ttⁿᶠ
  mono⊢ⁿᶠ η (inlⁿᶠ t)    = inlⁿᶠ (mono⊢ⁿᶠ η t)
  mono⊢ⁿᶠ η (inrⁿᶠ t)    = inrⁿᶠ (mono⊢ⁿᶠ η t)

  mono⊢ⁿᵉ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᵉ A → Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ η (varⁿᵉ i)      = varⁿᵉ (mono∈ η i)
  mono⊢ⁿᵉ η (appⁿᵉ t u)    = appⁿᵉ (mono⊢ⁿᵉ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᵉ η (fstⁿᵉ t)      = fstⁿᵉ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᵉ η (sndⁿᵉ t)      = sndⁿᵉ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᵉ η (boomⁿᵉ t)     = boomⁿᵉ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᵉ η (caseⁿᵉ t u v) = caseⁿᵉ (mono⊢ⁿᵉ η t) (mono⊢ⁿᶠ (keep η) u) (mono⊢ⁿᶠ (keep η) v)


-- The canonical model.

instance
  canon : Model
  canon = record
    { World   = Cx Ty
    ; _≤_     = _⊆_
    ; refl≤   = refl⊆
    ; trans≤  = trans⊆
    ; _⊪ᵅ_   = λ Γ P → Γ ⊢ⁿᵉ α P
    ; mono⊪ᵅ = mono⊢ⁿᵉ
    ; _‼_     = λ Γ A → Γ ⊢ⁿᶠ A
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
  reflect {α P}   t = return {α P} t
  reflect {A ▷ B} t = return {A ▷ B} (λ ξ a → reflect {B} (appⁿᵉ (mono⊢ⁿᵉ ξ t) (reify {A} a)))
  reflect {A ∧ B} t = return {A ∧ B} (ᴬᵍpair (reflect {A} (fstⁿᵉ t)) (reflect {B} (sndⁿᵉ t)))
  reflect {⊤}    t = return {⊤} ᴬᵍtt
  reflect {⊥}    t = λ ξ k → neⁿᶠ (boomⁿᵉ (mono⊢ⁿᵉ ξ t))
  reflect {A ∨ B} t = λ ξ k → neⁿᶠ (caseⁿᵉ (mono⊢ⁿᵉ ξ t)
                                       (k weak⊆ (ᴬᵍinl (reflect {A} (varⁿᵉ top))))
                                       (k weak⊆ (ᴬᵍinr (reflect {B} (varⁿᵉ top)))))

  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
  reify {α P}   k = k refl≤ (λ ξ s → neⁿᶠ s)
  reify {A ▷ B} k = k refl≤ (λ ξ s → lamⁿᶠ (reify {B} (s weak⊆ (reflect {A} (varⁿᵉ top)))))
  reify {A ∧ B} k = k refl≤ (λ ξ s → pairⁿᶠ (reify {A} (ᴬᵍfst s)) (reify {B} (ᴬᵍsnd s)))
  reify {⊤}    k = k refl≤ (λ ξ s → ttⁿᶠ)
  reify {⊥}    k = k refl≤ (λ ξ ())
  reify {A ∨ B} k = k refl≤ (λ ξ s → ᴬᵍcase s
                                        (λ a → inlⁿᶠ (reify {A} (λ ξ′ k′ → a ξ′ k′)))
                                        (λ b → inrⁿᶠ (reify {B} (λ ξ′ k′ → b ξ′ k′))))

reflect⋆ : ∀ {Π Γ} → Γ ⊢⋆ⁿᵉ Π → Γ ⊩⋆ Π
reflect⋆ {⌀}     ᴬᵍtt          = ᴬᵍtt
reflect⋆ {Π , A} (ᴬᵍpair ts t) = ᴬᵍpair (reflect⋆ ts) (reflect t)

reify⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ ⊢⋆ⁿᶠ Π
reify⋆ {⌀}     ᴬᵍtt          = ᴬᵍtt
reify⋆ {Π , A} (ᴬᵍpair ts t) = ᴬᵍpair (reify⋆ ts) (reify t)


-- Additional useful properties.

-- TODO:
-- mutual
--   multicut⊢ⁿᶠ : ∀ {A Γ Γ′} → Γ ⊢⋆ⁿᶠ Γ′ → Γ′ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ A
--   multicut⊢ⁿᶠ {Γ′ = ⌀}      ᴬᵍtt          u = mono⊢ⁿᶠ bot⊆ u
--   multicut⊢ⁿᶠ {Γ′ = Γ′ , B} (ᴬᵍpair ts t) u = neⁿᶠ (appⁿᵉ (multicut⊢ⁿᵉ ts (lamⁿᶠ u)) t)
--
--   multicut⊢ⁿᵉ : ∀ {A Γ Γ′} → Γ ⊢⋆ⁿᶠ Γ′ → Γ′ ⊢ⁿᶠ A → Γ ⊢ⁿᵉ A
--   -- NOTE: No idea how to fill this hole.
--   multicut⊢ⁿᵉ {A} {Γ′ = ⌀}      ᴬᵍtt          u = {!!}
--   multicut⊢ⁿᵉ {A} {Γ′ = Γ′ , B} (ᴬᵍpair ts t) u = appⁿᵉ (multicut⊢ⁿᵉ ts (lamⁿᶠ u)) t
--
-- multicut⊩ : ∀ {A Γ Γ′} → Γ ⊩⋆ Γ′ → Γ′ ⊩ A → Γ ⊩ A
-- multicut⊩ {A} {Γ′ = ⌀}      ᴬᵍtt          u = mono⊩ {A} bot⊆ u
-- multicut⊩ {A} {Γ′ = Γ′ , B} (ᴬᵍpair ts t) u = reflect {A} (appⁿᵉ ts′ (reify {B} t))
--   where ts′ = multicut⊢ⁿᵉ (reify⋆ ts) (lamⁿᶠ (reify {A} u))

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ {⌀}     = ᴬᵍtt
refl⊩⋆ {Γ , A} = ᴬᵍpair (mono⊩⋆ {Γ} weak⊆ refl⊩⋆) (reflect {A} (varⁿᵉ top))

-- trans⊩⋆ : ∀ {Π Γ Γ′} → Γ ⊩⋆ Γ′ → Γ′ ⊩⋆ Π → Γ ⊩⋆ Π
-- trans⊩⋆ {⌀}     ts ᴬᵍtt          = ᴬᵍtt
-- trans⊩⋆ {Π , A} ts (ᴬᵍpair us u) = ᴬᵍpair (trans⊩⋆ ts us) (multicut⊩ {A} ts u)


-- Completeness, or quotation.

quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
quot t = nf→tm (reify (t refl⊩⋆))


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ eval
