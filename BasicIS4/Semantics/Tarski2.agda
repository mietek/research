-- Tarski-style semantics with contexts as concrete worlds, and glueing for □ only.
-- Gentzen-style syntax.

module BasicIS4.Semantics.Tarski2 where

open import BasicIS4.Syntax.Common public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_ _[⊢]_ _[⊢⋆]_
  field
    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_   : Cx Ty → Atom → Set
    mono⊩ᵅ : ∀ {P Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩ᵅ P → Γ′ ⊩ᵅ P

    -- Gentzen-style syntax representation; monotonic.
    _[⊢]_     : Cx Ty → Ty → Set
    _[⊢⋆]_    : Cx Ty → Cx Ty → Set
    mono[⊢]   : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ [⊢] A → Γ′ [⊢] A
    [var]      : ∀ {A Γ}    → A ∈ Γ → Γ [⊢] A
    [lam]      : ∀ {A B Γ}  → Γ , A [⊢] B → Γ [⊢] A ▻ B
    [app]      : ∀ {A B Γ}  → Γ [⊢] A ▻ B → Γ [⊢] A → Γ [⊢] B
    [multibox] : ∀ {A Δ Γ}  → Γ [⊢⋆] □⋆ Δ → □⋆ Δ [⊢] A → Γ [⊢] □ A
    [down]     : ∀ {A Γ}    → Γ [⊢] □ A → Γ [⊢] A
    [pair]     : ∀ {A B Γ}  → Γ [⊢] A → Γ [⊢] B → Γ [⊢] A ∧ B
    [fst]      : ∀ {A B Γ}  → Γ [⊢] A ∧ B → Γ [⊢] A
    [snd]      : ∀ {A B Γ}  → Γ [⊢] A ∧ B → Γ [⊢] B
    [tt]       : ∀ {Γ}      → Γ [⊢] ⊤

    -- TODO: Workarounds for Agda bug #2143.
    top[⊢⋆] : ∀ {Γ}     → (Γ [⊢⋆] ⌀) ≡ 𝟙
    pop[⊢⋆] : ∀ {Π A Γ} → (Γ [⊢⋆] Π , A) ≡ (Γ [⊢⋆] Π × Γ [⊢] A)

  infix 3 _[⊢]⋆_
  _[⊢]⋆_ : Cx Ty → Cx Ty → Set
  Γ [⊢]⋆ ⌀     = 𝟙
  Γ [⊢]⋆ Π , A = Γ [⊢]⋆ Π × Γ [⊢] A

  [⊢⋆]→[⊢]⋆ : ∀ {Π Γ} → Γ [⊢⋆] Π → Γ [⊢]⋆ Π
  [⊢⋆]→[⊢]⋆ {⌀}     {Γ} ts = ∙
  [⊢⋆]→[⊢]⋆ {Π , A} {Γ} ts rewrite pop[⊢⋆] {Π} {A} {Γ} = [⊢⋆]→[⊢]⋆ (π₁ ts) , π₂ ts

  [⊢]⋆→[⊢⋆] : ∀ {Π Γ} → Γ [⊢]⋆ Π → Γ [⊢⋆] Π
  [⊢]⋆→[⊢⋆] {⌀}     {Γ} ∙        rewrite top[⊢⋆] {Γ}         = ∙
  [⊢]⋆→[⊢⋆] {Π , A} {Γ} (ts , t) rewrite pop[⊢⋆] {Π} {A} {Γ} = [⊢]⋆→[⊢⋆] ts , t

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : Cx Ty → Ty → Set
  Γ ⊩ α P   = Γ ⊩ᵅ P
  Γ ⊩ A ▻ B = ∀ {Γ′} → Γ ⊆ Γ′ → Γ′ ⊩ A → Γ′ ⊩ B
  Γ ⊩ □ A   = ∀ {Γ′} → Γ ⊆ Γ′ → Γ′ [⊢] □ A × Γ′ ⊩ A
  Γ ⊩ A ∧ B = Γ ⊩ A × Γ ⊩ B
  Γ ⊩ ⊤    = 𝟙

  infix 3 _⊩⋆_
  _⊩⋆_ : Cx Ty → Cx Ty → Set
  Γ ⊩⋆ ⌀     = 𝟙
  Γ ⊩⋆ Π , A = Γ ⊩⋆ Π × Γ ⊩ A


-- Monotonicity with respect to context inclusion.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩ A → Γ′ ⊩ A
  mono⊩ {α P}   η s       = mono⊩ᵅ η s
  mono⊩ {A ▻ B} η s       = λ η′ → s (trans⊆ η η′)
  mono⊩ {□ A}   η s       = λ η′ → s (trans⊆ η η′)
  mono⊩ {A ∧ B} η (a , b) = mono⊩ {A} η a , mono⊩ {B} η b
  mono⊩ {⊤}    η ∙       = ∙

  mono⊩⋆ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩⋆ Π → Γ′ ⊩⋆ Π
  mono⊩⋆ {⌀}     η ∙        = ∙
  mono⊩⋆ {Π , A} η (ts , t) = mono⊩⋆ {Π} η ts , mono⊩ {A} η t


-- Shorthand for variables.

module _ {{_ : Model}} where
  [v₀] : ∀ {A Γ} → Γ , A [⊢] A
  [v₀] = [var] i₀

  [v₁] : ∀ {A B Γ} → (Γ , A) , B [⊢] A
  [v₁] = [var] i₁

  [v₂] : ∀ {A B C Γ} → ((Γ , A) , B) , C [⊢] A
  [v₂] = [var] i₂


-- Useful theorems in functional form.

module _ {{_ : Model}} where
  [multicut] : ∀ {Π A Γ} → Γ [⊢]⋆ Π → Π [⊢] A → Γ [⊢] A
  [multicut] {⌀}     ∙        u = mono[⊢] bot⊆ u
  [multicut] {Π , B} (ts , t) u = [app] ([multicut] ts ([lam] u)) t

  [dist] : ∀ {A B Γ} → Γ [⊢] □ (A ▻ B) → Γ [⊢] □ A → Γ [⊢] □ B
  [dist] t u = [multibox] ([⊢]⋆→[⊢⋆] ((∙ , t) , u)) ([app] ([down] [v₁]) ([down] [v₀]))

  [up] : ∀ {A Γ} → Γ [⊢] □ A → Γ [⊢] □ □ A
  [up] t = [multibox] ([⊢]⋆→[⊢⋆] ((∙ , t))) [v₀]


-- Additional useful equipment.

module _ {{_ : Model}} where

  _⟪$⟫_ : ∀ {A B Γ} → Γ ⊩ A ▻ B → Γ ⊩ A → Γ ⊩ B
  f ⟪$⟫ a = f refl⊆ a

  ⟪K⟫ : ∀ {A B Γ} → Γ ⊩ A → Γ ⊩ B ▻ A
  ⟪K⟫ {A} a η = K (mono⊩ {A} η a)

  ⟪S⟫′ : ∀ {A B C Γ} → Γ ⊩ A ▻ B ▻ C → Γ ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} f η g η′ a = let f′ = mono⊩ {A ▻ B ▻ C} (trans⊆ η η′) f
                                    g′ = mono⊩ {A ▻ B} η′ g
                                in  (f′ refl⊆ a) refl⊆ (g′ refl⊆ a)

  ⟪S⟫ : ∀ {A B C Γ} → Γ ⊩ A ▻ B ▻ C → Γ ⊩ A ▻ B → Γ ⊩ A → Γ ⊩ C
  ⟪S⟫ {A} {B} {C} f g a = ⟪S⟫′ {A} {B} {C} f refl⊆ g refl⊆ a

  _⟪D⟫_ : ∀ {A B Γ} → Γ ⊩ □ (A ▻ B) → Γ ⊩ □ A → Γ ⊩ □ B
  _⟪D⟫_ {A} {B} s₁ s₂ η = let t , f = s₁ η
                              u , a = s₂ η
                          in  [dist] t u , _⟪$⟫_ {A} {B} f a

  _⟪D⟫′_ : ∀ {A B Γ} → Γ ⊩ □ (A ▻ B) → Γ ⊩ □ A ▻ □ B
  _⟪D⟫′_ {A} {B} s η = let s′ = mono⊩ {□ (A ▻ B)} η s
                       in  _⟪D⟫_ s′

  ⟪↑⟫ : ∀ {A Γ} → Γ ⊩ □ A → Γ ⊩ □ □ A
  ⟪↑⟫ s η = let t , a = s η
            in  [up] t , λ η′ → s (trans⊆ η η′)

  ⟪↓⟫ : ∀ {A Γ} → Γ ⊩ □ A → Γ ⊩ A
  ⟪↓⟫ s = let p , a = s refl⊆
          in  a

  _⟪,⟫′_ : ∀ {A B Γ} → Γ ⊩ A → Γ ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} {B} a η b = let a′ = mono⊩ {A} η a
                         in  a′ , b

  _⟪,⟫_ : ∀ {A B Γ} → Γ ⊩ A → Γ ⊩ B → Γ ⊩ A ∧ B
  _⟪,⟫_ {A} {B} a b = _⟪,⟫′_ {A} {B} a refl⊆ b


-- Forcing in a particular world of a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⊩_⇒_
  _⊩_⇒_ : Cx Ty → Cx Ty → Ty → Set
  w ⊩ Γ ⇒ A = w ⊩⋆ Γ → w ⊩ A

  infix 3 _⊩_⇒⋆_
  _⊩_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
  w ⊩ Γ ⇒⋆ Π = w ⊩⋆ Γ → w ⊩⋆ Π


-- Entailment, or forcing in all models, for sequents.

infix 3 _⊨_
_⊨_ : Cx Ty → Ty → Set₁
Γ ⊨ A = ∀ {{_ : Model}} {w : Cx Ty} → w ⊩ Γ ⇒ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx Ty → Cx Ty → Set₁
Γ ⊨⋆ Π = ∀ {{_ : Model}} {w : Cx Ty} → w ⊩ Γ ⇒⋆ Π


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  -- TODO: ⟦λ⟧

  _⟦$⟧_ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B
  _⟦$⟧_ {A} {B} f g γ = _⟪$⟫_ {A} {B} (f γ) (g γ)

  ⟦K⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B ▻ A
  ⟦K⟧ {A} {B} a γ = ⟪K⟫ {A} {B} (a γ)

  ⟦S⟧ : ∀ {A B C Γ w} → w ⊩ Γ ⇒ A ▻ B ▻ C → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ C
  ⟦S⟧ {A} {B} {C} f g a γ = ⟪S⟫ {A} {B} {C} (f γ) (g γ) (a γ)

  _⟦D⟧_ : ∀ {A B Γ w} → w ⊩ Γ ⇒ □ (A ▻ B) → w ⊩ Γ ⇒ □ A → w ⊩ Γ ⇒ □ B
  (s₁ ⟦D⟧ s₂) γ = (s₁ γ) ⟪D⟫ (s₂ γ)

  ⟦↑⟧ : ∀ {A Γ w} → w ⊩ Γ ⇒ □ A → w ⊩ Γ ⇒ □ □ A
  ⟦↑⟧ s γ = ⟪↑⟫ (s γ)

  ⟦↓⟧ : ∀ {A Γ w} → w ⊩ Γ ⇒ □ A → w ⊩ Γ ⇒ A
  ⟦↓⟧ s γ = ⟪↓⟫ (s γ)

  _⟦,⟧_ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B → w ⊩ Γ ⇒ A ∧ B
  (a ⟦,⟧ b) γ = a γ , b γ

  ⟦π₁⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ∧ B → w ⊩ Γ ⇒ A
  ⟦π₁⟧ s γ = π₁ (s γ)

  ⟦π₂⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ∧ B → w ⊩ Γ ⇒ B
  ⟦π₂⟧ s γ = π₂ (s γ)
