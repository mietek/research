-- Tarski-style semantics with context pairs as concrete worlds, and glueing for α, ▻, and □.
-- Gentzen-style syntax.

module BasicIS4.Semantics.TarskiOvergluedDyadicGentzen where

open import BasicIS4.Syntax.Common public
open import Common.ContextPair public
open import Common.Semantics public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_ _[⊢]_
  field
    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_    : Cx² Ty → Atom → Set
    mono²⊩ᵅ : ∀ {P Π Π′} → Π ⊆² Π′ → Π ⊩ᵅ P → Π′ ⊩ᵅ P

    -- Gentzen-style syntax representation; monotonic.
    _[⊢]_    : Cx² Ty → Ty → Set
    mono²[⊢] : ∀ {A Π Π′}  → Π ⊆² Π′ → Π [⊢] A → Π′ [⊢] A
    [var]     : ∀ {A Γ Δ}   → A ∈ Γ → Γ ⁏ Δ [⊢] A
    [lam]     : ∀ {A B Γ Δ} → Γ , A ⁏ Δ [⊢] B → Γ ⁏ Δ [⊢] A ▻ B
    [app]     : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] A ▻ B → Γ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] B
    [mvar]    : ∀ {A Γ Δ}   → A ∈ Δ → Γ ⁏ Δ [⊢] A
    [box]     : ∀ {A Γ Δ}   → ∅ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] □ A
    [unbox]   : ∀ {A C Γ Δ} → Γ ⁏ Δ [⊢] □ A → Γ ⁏ Δ , A [⊢] C → Γ ⁏ Δ [⊢] C
    [pair]    : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] B → Γ ⁏ Δ [⊢] A ∧ B
    [fst]     : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] A ∧ B → Γ ⁏ Δ [⊢] A
    [snd]     : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] A ∧ B → Γ ⁏ Δ [⊢] B
    [tt]      : ∀ {Γ Δ}     → Γ ⁏ Δ [⊢] ⊤

  infix 3 _[⊢]⋆_
  _[⊢]⋆_ : Cx² Ty → Cx Ty → Set
  Π [⊢]⋆ ∅     = 𝟙
  Π [⊢]⋆ Ξ , A = Π [⊢]⋆ Ξ × Π [⊢] A

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : Cx² Ty → Ty → Set
  Π ⊩ α P   = Glue (Π [⊢] α P) (Π ⊩ᵅ P)
  Π ⊩ A ▻ B = ∀ {Π′} → Π ⊆² Π′ → Glue (Π′ [⊢] A ▻ B) (Π′ ⊩ A → Π′ ⊩ B)
  Π ⊩ □ A   = ∀ {Π′} → Π ⊆² Π′ → Glue (Π′ [⊢] □ A) (Π′ ⊩ A)
  Π ⊩ A ∧ B = Π ⊩ A × Π ⊩ B
  Π ⊩ ⊤    = 𝟙

  infix 3 _⊩⋆_
  _⊩⋆_ : Cx² Ty → Cx Ty → Set
  Π ⊩⋆ ∅     = 𝟙
  Π ⊩⋆ Ξ , A = Π ⊩⋆ Ξ × Π ⊩ A


-- Monotonicity with respect to context inclusion.

module _ {{_ : Model}} where
  mono²⊩ : ∀ {A Π Π′} → Π ⊆² Π′ → Π ⊩ A → Π′ ⊩ A
  mono²⊩ {α P}   ψ s = mono²[⊢] ψ (syn s) ⅋ mono²⊩ᵅ ψ (sem s)
  mono²⊩ {A ▻ B} ψ s = λ ψ′ → s (trans⊆² ψ ψ′)
  mono²⊩ {□ A}   ψ s = λ ψ′ → s (trans⊆² ψ ψ′)
  mono²⊩ {A ∧ B} ψ s = mono²⊩ {A} ψ (π₁ s) , mono²⊩ {B} ψ (π₂ s)
  mono²⊩ {⊤}    ψ s = ∙

  mono²⊩⋆ : ∀ {Ξ Π Π′} → Π ⊆² Π′ → Π ⊩⋆ Ξ → Π′ ⊩⋆ Ξ
  mono²⊩⋆ {∅}     ψ ∙        = ∙
  mono²⊩⋆ {Ξ , A} ψ (ts , t) = mono²⊩⋆ ψ ts , mono²⊩ {A} ψ t


-- Extraction of syntax representation in a particular model.

module _ {{_ : Model}} where
  reifyʳ : ∀ {A Π} → Π ⊩ A → Π [⊢] A
  reifyʳ {α P}   s = syn s
  reifyʳ {A ▻ B} s = syn (s refl⊆²)
  reifyʳ {□ A}   s = syn (s refl⊆²)
  reifyʳ {A ∧ B} s = [pair] (reifyʳ {A} (π₁ s)) (reifyʳ {B} (π₂ s))
  reifyʳ {⊤}    s = [tt]

  reifyʳ⋆ : ∀ {Ξ Π} → Π ⊩⋆ Ξ → Π [⊢]⋆ Ξ
  reifyʳ⋆ {∅}     ∙        = ∙
  reifyʳ⋆ {Ξ , A} (ts , t) = reifyʳ⋆ ts , reifyʳ t


-- Shorthand for variables.

module _ {{_ : Model}} where
  [v₀] : ∀ {A Γ Δ} → Γ , A ⁏ Δ [⊢] A
  [v₀] = [var] i₀

  [v₁] : ∀ {A B Γ Δ} → Γ , A , B ⁏ Δ [⊢] A
  [v₁] = [var] i₁

  [v₂] : ∀ {A B C Γ Δ} → Γ , A , B , C ⁏ Δ [⊢] A
  [v₂] = [var] i₂

  [mv₀] : ∀ {A Γ Δ} → Γ ⁏ Δ , A [⊢] A
  [mv₀] = [mvar] i₀

  [mv₁] : ∀ {A B Γ Δ} → Γ ⁏ Δ , A , B [⊢] A
  [mv₁] = [mvar] i₁

  [mv₂] : ∀ {A B C Γ Δ} → Γ ⁏ Δ , A , B , C [⊢] A
  [mv₂] = [mvar] i₂


-- Useful theorems in functional form.

module _ {{_ : Model}} where
  [mlam] : ∀ {A B Γ Δ} → Γ ⁏ Δ , A [⊢] B → Γ ⁏ Δ [⊢] □ A ▻ B
  [mlam] t = [lam] ([unbox] [v₀] (mono²[⊢] (weak⊆ , refl⊆) t))

  [multicut] : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ [⊢]⋆ Ξ → Ξ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] A
  [multicut] {∅}     ∙        u = mono²[⊢] (bot⊆ , refl⊆) u
  [multicut] {Ξ , B} (ts , t) u = [app] ([multicut] ts ([lam] u)) t

  [mmulticut] : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ [⊢]⋆ □⋆ Ξ → Γ ⁏ Ξ [⊢] A → Γ ⁏ Δ [⊢] A
  [mmulticut] {∅}     ∙        u = mono²[⊢] (refl⊆ , bot⊆) u
  [mmulticut] {Ξ , B} (ts , t) u = [app] ([mmulticut] ts ([mlam] u)) t

  [multicut²] : ∀ {Ξ Ξ′ A Γ Δ} → Γ ⁏ Δ [⊢]⋆ Ξ → Γ ⁏ Δ [⊢]⋆ □⋆ Ξ′ → Ξ ⁏ Ξ′ [⊢] A → Γ ⁏ Δ [⊢] A
  [multicut²] {∅}     ∙        us v = [mmulticut] us (mono²[⊢] (bot⊆ , refl⊆) v)
  [multicut²] {Ξ , B} (ts , t) us v = [app] ([multicut²] ts us ([lam] v)) t

  [dist] : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] □ (A ▻ B) → Γ ⁏ Δ [⊢] □ A → Γ ⁏ Δ [⊢] □ B
  [dist] t u = [unbox] t ([unbox] (mono²[⊢] (refl⊆ , weak⊆) u) ([box] ([app] [mv₁] [mv₀])))

  [up] : ∀ {A Γ Δ} → Γ ⁏ Δ [⊢] □ A → Γ ⁏ Δ [⊢] □ □ A
  [up] t = [unbox] t ([box] ([box] [mv₀]))

  [down] : ∀ {A Γ Δ} → Γ ⁏ Δ [⊢] □ A → Γ ⁏ Δ [⊢] A
  [down] t = [unbox] t [mv₀]


-- Useful theorems in combinatory form.

module _ {{_ : Model}} where
  [ci] : ∀ {A Γ Δ} → Γ ⁏ Δ [⊢] A ▻ A
  [ci] = [lam] [v₀]

  [ck] : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] A ▻ B ▻ A
  [ck] = [lam] ([lam] [v₁])

  [cs] : ∀ {A B C Γ Δ} → Γ ⁏ Δ [⊢] (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
  [cs] = [lam] ([lam] ([lam] ([app] ([app] [v₂] [v₀]) ([app] [v₁] [v₀]))))

  [cdist] : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] □ (A ▻ B) ▻ □ A ▻ □ B
  [cdist] = [lam] ([lam] ([dist] [v₁] [v₀]))

  [cup] : ∀ {A Γ Δ} → Γ ⁏ Δ [⊢] □ A ▻ □ □ A
  [cup] = [lam] ([up] [v₀])

  [cdown] : ∀ {A Γ Δ} → Γ ⁏ Δ [⊢] □ A ▻ A
  [cdown] = [lam] ([down] [v₀])

  [cpair] : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] A ▻ B ▻ A ∧ B
  [cpair] = [lam] ([lam] ([pair] [v₁] [v₀]))

  [cfst] : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] A ∧ B ▻ A
  [cfst] = [lam] ([fst] [v₀])

  [csnd] : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] A ∧ B ▻ B
  [csnd] = [lam] ([snd] [v₀])


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B Π} → Π ⊩ A ▻ B → Π ⊩ A → Π ⊩ B
  s ⟪$⟫ a = sem (s refl⊆²) a

  ⟪K⟫ : ∀ {A B Π} → Π ⊩ A → Π ⊩ B ▻ A
  ⟪K⟫ {A} a ψ = let a′ = mono²⊩ {A} ψ a
                in  [app] [ck] (reifyʳ a′) ⅋ K a′

  ⟪S⟫ : ∀ {A B C Π} → Π ⊩ A ▻ B ▻ C → Π ⊩ A ▻ B → Π ⊩ A → Π ⊩ C
  ⟪S⟫ s₁ s₂ a = (s₁ ⟪$⟫ a) ⟪$⟫ (s₂ ⟪$⟫ a)

  ⟪S⟫′ : ∀ {A B C Π} → Π ⊩ A ▻ B ▻ C → Π ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} s₁ ψ = let s₁′ = mono²⊩ {A ▻ B ▻ C} ψ s₁
                              t   = syn (s₁′ refl⊆²)
                          in  [app] [cs] t ⅋ λ s₂ ψ′ →
                              let s₁″ = mono²⊩ {A ▻ B ▻ C} (trans⊆² ψ ψ′) s₁
                                  s₂′ = mono²⊩ {A ▻ B} ψ′ s₂
                                  t′  = syn (s₁″ refl⊆²)
                                  u   = syn (s₂′ refl⊆²)
                              in  [app] ([app] [cs] t′) u ⅋ ⟪S⟫ s₁″ s₂′

  _⟪D⟫_ : ∀ {A B Π} → Π ⊩ □ (A ▻ B) → Π ⊩ □ A → Π ⊩ □ B
  (s₁ ⟪D⟫ s₂) ψ = let t ⅋ s₁′ = s₁ ψ
                      u ⅋ a   = s₂ ψ
                  in  [app] ([app] [cdist] t) u ⅋ s₁′ ⟪$⟫ a

  -- TODO: Report bug.
  _⟪D⟫′_ : ∀ {A B Π} → Π ⊩ □ (A ▻ B) → Π ⊩ □ A ▻ □ B
  _⟪D⟫′_ {A} {B} s₁ ψ = let s₁′ = mono²⊩ {□ (A ▻ B)} ψ s₁
                        in  [app] [cdist] (reifyʳ (λ {Π″} ψ′ → s₁′ ψ′)) ⅋ _⟪D⟫_ s₁′

  ⟪↑⟫ : ∀ {A Π} → Π ⊩ □ A → Π ⊩ □ □ A
  ⟪↑⟫ {A} s ψ = [app] [cup] (syn (s ψ)) ⅋ λ ψ′ → s (trans⊆² ψ ψ′)

  ⟪↓⟫ : ∀ {A Π} → Π ⊩ □ A → Π ⊩ A
  ⟪↓⟫ s = sem (s refl⊆²)

  _⟪,⟫′_ : ∀ {A B Π} → Π ⊩ A → Π ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} a ψ = let a′ = mono²⊩ {A} ψ a
                   in  [app] [cpair] (reifyʳ a′) ⅋ _,_ a′


-- Forcing in a particular world of a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⊩_⇒_
  _⊩_⇒_ : Cx² Ty → Cx² Ty → Ty → Set
  Π ⊩ Γ ⁏ Δ ⇒ A = Π ⊩⋆ Γ → Π ⊩⋆ □⋆ Δ → Π ⊩ A

  infix 3 _⊩_⇒⋆_
  _⊩_⇒⋆_ : Cx² Ty → Cx² Ty → Cx Ty → Set
  Π ⊩ Γ ⁏ Δ ⇒⋆ Ξ = Π ⊩⋆ Γ → Π ⊩⋆ □⋆ Δ → Π ⊩⋆ Ξ


-- Entailment, or forcing in all worlds of all models, for sequents.

infix 3 _⊨_
_⊨_ : Cx² Ty → Ty → Set₁
Π ⊨ A = ∀ {{_ : Model}} {w : Cx² Ty} → w ⊩ Π ⇒ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx² Ty → Cx Ty → Set₁
Π ⊨⋆ Ξ = ∀ {{_ : Model}} {w : Cx² Ty} → w ⊩ Π ⇒⋆ Ξ


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩⋆ Γ → w ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  mlookup : ∀ {A Δ w} → A ∈ Δ → w ⊩⋆ □⋆ Δ → w ⊩ A
  mlookup top     (γ , s) = sem (s refl⊆²)
  mlookup (pop i) (γ , s) = mlookup i γ

  -- TODO: More equipment.
