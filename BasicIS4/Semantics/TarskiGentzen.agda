-- Tarski-style semantics with explicit Gentzen-style syntax representation.

module BasicIS4.Semantics.TarskiGentzen where

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
  Γ ⊩ α P   = Γ [⊢] α P × Γ ⊩ᵅ P
  Γ ⊩ A ▻ B = ∀ {Γ′} → Γ ⊆ Γ′ → Γ′ [⊢] A ▻ B × (Γ′ ⊩ A → Γ′ ⊩ B)
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
  mono⊩ {α P}   η (t , s) = mono[⊢] η t , mono⊩ᵅ η s
  mono⊩ {A ▻ B} η s       = λ η′ → s (trans⊆ η η′)
  mono⊩ {□ A}   η s       = λ η′ → s (trans⊆ η η′)
  mono⊩ {A ∧ B} η (a , b) = mono⊩ {A} η a , mono⊩ {B} η b
  mono⊩ {⊤}    η ∙       = ∙

  mono⊩⋆ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩⋆ Π → Γ′ ⊩⋆ Π
  mono⊩⋆ {⌀}     η ∙        = ∙
  mono⊩⋆ {Π , A} η (ts , t) = mono⊩⋆ {Π} η ts , mono⊩ {A} η t


-- Completeness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  reifyʳ : ∀ {A Γ} → Γ ⊩ A → Γ [⊢] A
  reifyʳ {α P}   (t , s) = t
  reifyʳ {A ▻ B} s       = let t , f = s refl⊆ in t
  reifyʳ {□ A}   s       = let t , f = s refl⊆ in t
  reifyʳ {A ∧ B} (a , b) = [pair] (reifyʳ {A} a) (reifyʳ {B} b)
  reifyʳ {⊤}    ∙       = [tt]

  reifyʳ⋆ : ∀ {Π Γ} → Γ ⊩⋆ Π → Γ [⊢]⋆ Π
  reifyʳ⋆ {⌀}     ∙        = ∙
  reifyʳ⋆ {Π , A} (ts , t) = reifyʳ⋆ ts , reifyʳ t


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
  [dist] : ∀ {A B Γ} → Γ [⊢] □ (A ▻ B) → Γ [⊢] □ A → Γ [⊢] □ B
  [dist] t u = [multibox] ([⊢]⋆→[⊢⋆] ((∙ , t) , u)) ([app] ([down] [v₁]) ([down] [v₀]))

  [up] : ∀ {A Γ} → Γ [⊢] □ A → Γ [⊢] □ □ A
  [up] t = [multibox] ([⊢]⋆→[⊢⋆] ((∙ , t))) [v₀]


-- Useful theorems in combinatory form.

module _ {{_ : Model}} where
  [ck] : ∀ {A B Γ} → Γ [⊢] A ▻ B ▻ A
  [ck] = [lam] ([lam] [v₁])

  [cs] : ∀ {A B C Γ} → Γ [⊢] (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
  [cs] = [lam] ([lam] ([lam] ([app] ([app] [v₂] [v₀]) ([app] [v₁] [v₀]))))

  [cdist] : ∀ {A B Γ} → Γ [⊢] □ (A ▻ B) ▻ □ A ▻ □ B
  [cdist] = [lam] ([lam] ([dist] [v₁] [v₀]))

  [cup] : ∀ {A Γ} → Γ [⊢] □ A ▻ □ □ A
  [cup] = [lam] ([up] [v₀])

  [cpair] : ∀ {A B Γ} → Γ [⊢] A ▻ B ▻ A ∧ B
  [cpair] = [lam] ([lam] ([pair] [v₁] [v₀]))


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B Γ} → Γ ⊩ A ▻ B → Γ ⊩ A → Γ ⊩ B
  s ⟪$⟫ a = let t , f = s refl⊆
            in  f a

  ⟪K⟫ : ∀ {A B Γ} → Γ ⊩ A → Γ ⊩ B ▻ A
  ⟪K⟫ {A} a η = let a′ = mono⊩ {A} η a
                in  [app] [ck] (reifyʳ a′) , K a′

  ⟪S⟫ : ∀ {A B C Γ} → Γ ⊩ A ▻ B ▻ C → Γ ⊩ A ▻ B → Γ ⊩ A → Γ ⊩ C
  ⟪S⟫ s₁ s₂ a = let t , f = s₁ refl⊆
                    u , g = s₂ refl⊆
                    _ , h = (f a) refl⊆
                in  h (g a)

  ⟪S⟫′ : ∀ {A B C Γ} → Γ ⊩ A ▻ B ▻ C → Γ ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} s₁ η = let s₁′   = mono⊩ {A ▻ B ▻ C} η s₁
                              t , _ = s₁′ refl⊆
                          in  [app] [cs] t , λ s₂ η′ →
                                let s₁″    = mono⊩ {A ▻ B ▻ C} (trans⊆ η η′) s₁
                                    t′ , _ = s₁″ refl⊆
                                    s₂′    = mono⊩ {A ▻ B} η′ s₂
                                    u  , g = s₂′ refl⊆
                                in  [app] ([app] [cs] t′) u , ⟪S⟫ s₁″ s₂′

  _⟪D⟫_ : ∀ {A B Γ} → Γ ⊩ □ (A ▻ B) → Γ ⊩ □ A → Γ ⊩ □ B
  (s₁ ⟪D⟫ s₂) η = let t , f = s₁ η
                      u , a = s₂ η
                  in  [app] ([app] [cdist] t) u , f ⟪$⟫ a

  -- TODO: Report bug.
  _⟪D⟫′_ : ∀ {A B Γ} → Γ ⊩ □ (A ▻ B) → Γ ⊩ □ A ▻ □ B
  _⟪D⟫′_ {A} {B} s η = let s′ = mono⊩ {□ (A ▻ B)} η s
                       in  [app] [cdist] (reifyʳ (λ {Γ′} η′ → s′ η′ )) , _⟪D⟫_ s′

  ⟪↑⟫ : ∀ {A Γ} → Γ ⊩ □ A → Γ ⊩ □ □ A
  ⟪↑⟫ s η = let t , a = s η
            in  [app] [cup] t , λ η′ → s (trans⊆ η η′)

  ⟪↓⟫ : ∀ {A Γ} → Γ ⊩ □ A → Γ ⊩ A
  ⟪↓⟫ s = let p , a = s refl⊆
          in  a

  _⟪,⟫′_ : ∀ {A B Γ} → Γ ⊩ A → Γ ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} a η = let a′ = mono⊩ {A} η a
                   in  [app] [cpair] (reifyʳ a′) , _,_ a′


-- Forcing in a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⊩_⇒_
  _⊩_⇒_ : Cx Ty → Cx Ty → Ty → Set
  Γ₀ ⊩ Γ ⇒ A = Γ₀ ⊩⋆ Γ → Γ₀ ⊩ A

  infix 3 _⊩_⇒⋆_
  _⊩_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
  Γ₀ ⊩ Γ ⇒⋆ Π = Γ₀ ⊩⋆ Γ → Γ₀ ⊩⋆ Π


-- Forcing in all models, for sequents.

infix 3 _⊨_
_⊨_ : Cx Ty → Ty → Set₁
Γ ⊨ A = ∀ {{_ : Model}} {Γ₀ : Cx Ty} → Γ₀ ⊩ Γ ⇒ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx Ty → Cx Ty → Set₁
Γ ⊨⋆ Π = ∀ {{_ : Model}} {Γ₀ : Cx Ty} → Γ₀ ⊩ Γ ⇒⋆ Π


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ Γ₀} → A ∈ Γ → Γ₀ ⊩ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  -- TODO: ⟦λ⟧

  _⟦$⟧_ : ∀ {A B Γ Γ₀} → Γ₀ ⊩ Γ ⇒ A ▻ B → Γ₀ ⊩ Γ ⇒ A → Γ₀ ⊩ Γ ⇒ B
  (f ⟦$⟧ g) γ = f γ ⟪$⟫ g γ

  ⟦S⟧ : ∀ {A B C Γ Γ₀} → Γ₀ ⊩ Γ ⇒ A ▻ B ▻ C → Γ₀ ⊩ Γ ⇒ A ▻ B → Γ₀ ⊩ Γ ⇒ A → Γ₀ ⊩ Γ ⇒ C
  ⟦S⟧ f g a γ = ⟪S⟫ (f γ) (g γ) (a γ)

  _⟦D⟧_ : ∀ {A B Γ Γ₀} → Γ₀ ⊩ Γ ⇒ □ (A ▻ B) → Γ₀ ⊩ Γ ⇒ □ A → Γ₀ ⊩ Γ ⇒ □ B
  (s₁ ⟦D⟧ s₂) γ = (s₁ γ) ⟪D⟫ (s₂ γ)

  ⟦↑⟧ : ∀ {A Γ Γ₀} → Γ₀ ⊩ Γ ⇒ □ A → Γ₀ ⊩ Γ ⇒ □ □ A
  ⟦↑⟧ s γ = ⟪↑⟫ (s γ)

  ⟦↓⟧ : ∀ {A Γ Γ₀} → Γ₀ ⊩ Γ ⇒ □ A → Γ₀ ⊩ Γ ⇒ A
  ⟦↓⟧ s γ = ⟪↓⟫ (s γ)

  _⟦,⟧_ : ∀ {A B Γ Γ₀} → Γ₀ ⊩ Γ ⇒ A → Γ₀ ⊩ Γ ⇒ B → Γ₀ ⊩ Γ ⇒ A ∧ B
  (a ⟦,⟧ b) γ = a γ , b γ

  ⟦π₁⟧ : ∀ {A B Γ Γ₀} → Γ₀ ⊩ Γ ⇒ A ∧ B → Γ₀ ⊩ Γ ⇒ A
  ⟦π₁⟧ s γ = π₁ (s γ)

  ⟦π₂⟧ : ∀ {A B Γ Γ₀} → Γ₀ ⊩ Γ ⇒ A ∧ B → Γ₀ ⊩ Γ ⇒ B
  ⟦π₂⟧ s γ = π₂ (s γ)
