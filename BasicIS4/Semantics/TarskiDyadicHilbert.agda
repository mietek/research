-- Tarski-style semantics with a Hilbert-style syntax representation, with separate modal context.

module BasicIS4.Semantics.TarskiDyadicHilbert where

open import Common.ContextPair public
open import BasicIS4.Syntax.Common public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⁏_⊨ᵅ_
  field
    -- Satisfaction for atomic propositions; monotonic.
    _⁏_⊨ᵅ_  : Cx Ty → Cx Ty → Atom → Set
    mono⊨ᵅ  : ∀ {P Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊨ᵅ P → Γ′ ⁏ Δ ⊨ᵅ P
    mmono⊨ᵅ : ∀ {P Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊨ᵅ P → Γ ⁏ Δ′ ⊨ᵅ P

    -- Hilbert-style syntax representation; monotonic.
    [_⁏_⊢_]  : Cx Ty → Cx Ty → Ty → Set
    mono[⊢]  : ∀ {A Γ Γ′ Δ}  → Γ ⊆ Γ′ → [ Γ ⁏ Δ ⊢ A ] → [ Γ′ ⁏ Δ ⊢ A ]
    mmono[⊢] : ∀ {A Γ Δ Δ′}  → Δ ⊆ Δ′ → [ Γ ⁏ Δ ⊢ A ] → [ Γ ⁏ Δ′ ⊢ A ]
    [var]     : ∀ {A Γ Δ}     → A ∈ Γ → [ Γ ⁏ Δ ⊢ A ]
    [app]     : ∀ {A B Γ Δ}   → [ Γ ⁏ Δ ⊢ A ▻ B ] → [ Γ ⁏ Δ ⊢ A ] → [ Γ ⁏ Δ ⊢ B ]
    [ci]      : ∀ {A Γ Δ}     → [ Γ ⁏ Δ ⊢ A ▻ A ]
    [ck]      : ∀ {A B Γ Δ}   → [ Γ ⁏ Δ ⊢ A ▻ B ▻ A ]
    [cs]      : ∀ {A B C Γ Δ} → [ Γ ⁏ Δ ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C ]
    [mvar]    : ∀ {A Γ Δ}     → A ∈ Δ → [ Γ ⁏ Δ ⊢ A ]
    [box]     : ∀ {A Γ Δ}     → [ ⌀ ⁏ Δ ⊢ A ] → [ Γ ⁏ Δ ⊢ □ A ]
    [cdist]   : ∀ {A B Γ Δ}   → [ Γ ⁏ Δ ⊢ □ (A ▻ B) ▻ □ A ▻ □ B ]
    [cup]     : ∀ {A Γ Δ}     → [ Γ ⁏ Δ ⊢ □ A ▻ □ □ A ]
    [cdown]   : ∀ {A Γ Δ}     → [ Γ ⁏ Δ ⊢ □ A ▻ A ]
    [cpair]   : ∀ {A B Γ Δ}   → [ Γ ⁏ Δ ⊢ A ▻ B ▻ A ∧ B ]
    [cfst]    : ∀ {A B Γ Δ}   → [ Γ ⁏ Δ ⊢ A ∧ B ▻ A ]
    [csnd]    : ∀ {A B Γ Δ}   → [ Γ ⁏ Δ ⊢ A ∧ B ▻ B ]
    [tt]      : ∀ {Γ Δ}       → [ Γ ⁏ Δ ⊢ ⊤ ]

  [_⁏_⊢_]⋆ : Cx Ty → Cx Ty → Cx Ty → Set
  [ Γ ⁏ Δ ⊢ ⌀ ]⋆     = 𝟙
  [ Γ ⁏ Δ ⊢ Π , A ]⋆ = [ Γ ⁏ Δ ⊢ Π ]⋆ × [ Γ ⁏ Δ ⊢ A ]

  mmono[⊢]⋆ : ∀ {Π Γ Δ Δ′} → Δ ⊆ Δ′ → [ Γ ⁏ Δ ⊢ Π ]⋆ → [ Γ ⁏ Δ′ ⊢ Π ]⋆
  mmono[⊢]⋆ {⌀}     θ ∙        = ∙
  mmono[⊢]⋆ {Π , A} θ (ts , t) = mmono[⊢]⋆ {Π} θ ts , mmono[⊢] θ t

open Model {{…}} public


-- Satisfaction in a particular model.

module _ {{_ : Model}} where
  infix 3 _⁏_⊨_
  _⁏_⊨_ : Cx Ty → Cx Ty → Ty → Set
  Γ ⁏ Δ ⊨ α P   = [ Γ ⁏ Δ ⊢ α P ] × Γ ⁏ Δ ⊨ᵅ P
  Γ ⁏ Δ ⊨ A ▻ B = ∀ {Γ′ Δ′} → Γ ⊆ Γ′ → Δ ⊆ Δ′ → [ Γ′ ⁏ Δ′ ⊢ A ▻ B ] × (Γ′ ⁏ Δ′ ⊨ A → Γ′ ⁏ Δ′ ⊨ B)
  Γ ⁏ Δ ⊨ □ A   = ∀ {Γ′ Δ′} → Γ ⊆ Γ′ → Δ ⊆ Δ′ → [ ⌀ ⁏ Δ′ ⊢ A ] × Γ′ ⁏ Δ′ ⊨ A
  Γ ⁏ Δ ⊨ A ∧ B = Γ ⁏ Δ ⊨ A × Γ ⁏ Δ ⊨ B
  Γ ⁏ Δ ⊨ ⊤    = 𝟙

  infix 3 _⁏_⊨⋆_
  _⁏_⊨⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
  Γ ⁏ Δ ⊨⋆ ⌀     = 𝟙
  Γ ⁏ Δ ⊨⋆ Π , A = Γ ⁏ Δ ⊨⋆ Π × Γ ⁏ Δ ⊨ A


-- Monotonicity with respect to context inclusion.

module _ {{_ : Model}} where
  mono⊨ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊨ A → Γ′ ⁏ Δ ⊨ A
  mono⊨ {α P}   η (t , s) = mono[⊢] η t , mono⊨ᵅ η s
  mono⊨ {A ▻ B} η s       = λ η′ θ → s (trans⊆ η η′) θ
  mono⊨ {□ A}   η s       = λ η′ θ → s (trans⊆ η η′) θ
  mono⊨ {A ∧ B} η (a , b) = mono⊨ {A} η a , mono⊨ {B} η b
  mono⊨ {⊤}    η ∙       = ∙

  mono⊨⋆ : ∀ {Π Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊨⋆ Π → Γ′ ⁏ Δ ⊨⋆ Π
  mono⊨⋆ {⌀}     η ∙        = ∙
  mono⊨⋆ {Π , A} η (ts , t) = mono⊨⋆ {Π} η ts , mono⊨ {A} η t


-- Monotonicity with respect to modal context inclusion.

module _ {{_ : Model}} where
  mmono⊨ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ′ ⊨ A
  mmono⊨ {α P}   θ (t , s) = mmono[⊢] θ t , mmono⊨ᵅ θ s
  mmono⊨ {A ▻ B} θ s       = λ η θ′ → s η (trans⊆ θ θ′)
  mmono⊨ {□ A}   θ s       = λ η θ′ → s η (trans⊆ θ θ′)
  mmono⊨ {A ∧ B} θ (a , b) = mmono⊨ {A} θ a , mmono⊨ {B} θ b
  mmono⊨ {⊤}    θ ∙       = ∙

  mmono⊨⋆ : ∀ {Π Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊨⋆ Π → Γ ⁏ Δ′ ⊨⋆ Π
  mmono⊨⋆ {⌀}     η ∙        = ∙
  mmono⊨⋆ {Π , A} η (ts , t) = mmono⊨⋆ {Π} η ts , mmono⊨ {A} η t


-- Combined monotonicity.

module _ {{_ : Model}} where
  mono²⊨ : ∀ {A Γ Γ′ Δ Δ′} → Γ ⊆ Γ′ × Δ ⊆ Δ′ → Γ ⁏ Δ ⊨ A → Γ′ ⁏ Δ′ ⊨ A
  mono²⊨ {A} (η , θ) = mono⊨ {A} η ∘ mmono⊨ {A} θ


-- Completeness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  reify[] : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ A → [ Γ ⁏ Δ ⊢ A ]
  reify[] {α P}   (t , s) = t
  reify[] {A ▻ B} s       = let t , f = s refl⊆ refl⊆ in t
  reify[] {□ A}   s       = let t , a = s refl⊆ refl⊆ in [box] t
  reify[] {A ∧ B} (a , b) = [app] ([app] [cpair] (reify[] {A} a)) (reify[] {B} b)
  reify[] {⊤}    ∙       = [tt]

  reify[]⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊨⋆ Π → [ Γ ⁏ Δ ⊢ Π ]⋆
  reify[]⋆ {⌀}     ∙        = ∙
  reify[]⋆ {Π , A} (ts , t) = reify[]⋆ ts , reify[] t


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊨ A ▻ B → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊨ B
  s ⟪$⟫ a = let t , f = s refl⊆ refl⊆ in f a

  ⟪const⟫ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊨ B ▻ A
  ⟪const⟫ {A} a η θ = let a′ = mono²⊨ {A} (η , θ) a
                      in  [app] [ck] (reify[] a′) , const a′

  ⟪ap⟫ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊨ A ▻ B ▻ C → Γ ⁏ Δ ⊨ A ▻ B → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊨ C
  ⟪ap⟫ s₁ s₂ a = let t , f = s₁ refl⊆ refl⊆
                     u , g = s₂ refl⊆ refl⊆
                     _ , h = (f a) refl⊆ refl⊆
                 in  h (g a)

  ⟪ap⟫′ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊨ A ▻ B ▻ C → Γ ⁏ Δ ⊨ (A ▻ B) ▻ A ▻ C
  ⟪ap⟫′ {A} {B} {C} s₁ η θ = let s₁′   = mono²⊨ {A ▻ B ▻ C} (η , θ) s₁
                                 t , _ = s₁′ refl⊆ refl⊆
                             in  [app] [cs] t , λ s₂ η′ θ′ →
                                   let s₁″    = mono²⊨ {A ▻ B ▻ C} (trans⊆ η η′ , trans⊆ θ θ′) s₁
                                       t′ , _ = s₁″ refl⊆ refl⊆
                                       s₂′    = mono²⊨ {A ▻ B} (η′ , θ′) s₂
                                       u  , g = s₂′ refl⊆ refl⊆
                                   in  [app] ([app] [cs] t′) u , ⟪ap⟫ s₁″ s₂′

  _⟪◎⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊨ □ (A ▻ B) → Γ ⁏ Δ ⊨ □ A → Γ ⁏ Δ ⊨ □ B
  (s₁ ⟪◎⟫ s₂) η θ = let t , f = s₁ η θ
                        u , a = s₂ η θ
                    in  [app] t u , f ⟪$⟫ a

  -- TODO: Report bug.
  _⟪◎⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊨ □ (A ▻ B) → Γ ⁏ Δ ⊨ □ A ▻ □ B
  _⟪◎⟫′_ {A} {B} s η θ = let s′ = mono²⊨ {□ (A ▻ B)} (η , θ) s
                         in  [app] [cdist] (reify[] (λ {Γ″} {Δ″} η′ θ′ → s′ η′ θ′)) , _⟪◎⟫_ s′

  ⟪⇑⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ □ A → Γ ⁏ Δ ⊨ □ □ A
  ⟪⇑⟫ {A} s η θ = let t , a = s η θ
                  in  [box] t , λ η′ θ′ → s (trans⊆ η η′) (trans⊆ θ θ′)

  ⟪⇓⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊨ □ A → Γ ⁏ Δ ⊨ A
  ⟪⇓⟫ s = let t , a = s refl⊆ refl⊆
          in  a

  _⟪,⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊨ B ▻ A ∧ B
  _⟪,⟫′_ {A} a η θ = let a′ = mono²⊨ {A} (η , θ) a
                     in  [app] [cpair] (reify[] a′) , _,_ a′


-- Satisfaction in a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⁏_⊨_⁏_⇒_
  _⁏_⊨_⁏_⇒_ : Cx Ty → Cx Ty → Cx Ty → Cx Ty → Ty → Set
  Γ₀ ⁏ Δ₀ ⊨ Γ ⁏ Δ ⇒ A = Γ₀ ⁏ Δ₀ ⊨⋆ Γ → ⌀ ⁏ Δ₀ ⊨⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊨ A

  infix 3 _⁏_⊨_⁏_⇒⋆_
  _⁏_⊨_⁏_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Cx Ty → Cx Ty → Set
  Γ₀ ⁏ Δ₀ ⊨ Γ ⁏ Δ ⇒⋆ Π = Γ₀ ⁏ Δ₀ ⊨⋆ Γ → ⌀ ⁏ Δ₀ ⊨⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊨⋆ Π


-- Satisfaction in all models, for sequents.

∀ᴹ⊨_⁏_⇒_ : Cx Ty → Cx Ty → Ty → Set₁
∀ᴹ⊨ Γ ⁏ Δ ⇒ A = ∀ {{_ : Model}} {Γ₀ Δ₀ : Cx Ty} → Γ₀ ⁏ Δ₀ ⊨ Γ ⁏ Δ ⇒ A

∀ᴹ⊨_⁏_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Set₁
∀ᴹ⊨ Γ ⁏ Δ ⇒⋆ Π = ∀ {{_ : Model}} {Γ₀ Δ₀ : Cx Ty} → Γ₀ ⁏ Δ₀ ⊨ Γ ⁏ Δ ⇒⋆ Π


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ Γ₀ Δ₀} → A ∈ Γ → Γ₀ ⁏ Δ₀ ⊨⋆ Γ → Γ₀ ⁏ Δ₀ ⊨ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  mlookup : ∀ {A Δ Γ₀ Δ₀} → A ∈ Δ → Γ₀ ⁏ Δ₀ ⊨⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊨ A
  mlookup top     (γ , s) = let t , a = s refl⊆ refl⊆ in a
  mlookup (pop i) (γ , s) = mlookup i γ
