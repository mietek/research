-- Tarski-style semantics with context pairs as concrete worlds, and glueing for α, ▻, and □.
-- Gentzen-style syntax.

module BasicIS4.Semantics.TarskiDyadicGentzen where

open import Common.ContextPair public
open import BasicIS4.Syntax.Common public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 _⁏_⊩ᵅ_ _⁏_[⊢]_
  field
    -- Forcing for atomic propositions; monotonic.
    _⁏_⊩ᵅ_  : Cx Ty → Cx Ty → Atom → Set
    mono⊩ᵅ  : ∀ {P Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩ᵅ P → Γ′ ⁏ Δ ⊩ᵅ P
    mmono⊩ᵅ : ∀ {P Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊩ᵅ P → Γ ⁏ Δ′ ⊩ᵅ P

    -- Gentzen-style syntax representation; monotonic.
    _⁏_[⊢]_  : Cx Ty → Cx Ty → Ty → Set
    mono[⊢]  : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ [⊢] A → Γ′ ⁏ Δ [⊢] A
    mmono[⊢] : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ [⊢] A → Γ ⁏ Δ′ [⊢] A
    [var]     : ∀ {A Γ Δ}    → A ∈ Γ → Γ ⁏ Δ [⊢] A
    [lam]     : ∀ {A B Γ Δ}  → Γ , A ⁏ Δ [⊢] B → Γ ⁏ Δ [⊢] A ▻ B
    [app]     : ∀ {A B Γ Δ}  → Γ ⁏ Δ [⊢] A ▻ B → Γ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] B
    [mvar]    : ∀ {A Γ Δ}    → A ∈ Δ → Γ ⁏ Δ [⊢] A
    [box]     : ∀ {A Γ Δ}    → ⌀ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] □ A
    [unbox]   : ∀ {A C Γ Δ}  → Γ ⁏ Δ [⊢] □ A → Γ ⁏ Δ , A [⊢] C → Γ ⁏ Δ [⊢] C
    [pair]    : ∀ {A B Γ Δ}  → Γ ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] B → Γ ⁏ Δ [⊢] A ∧ B
    [fst]     : ∀ {A B Γ Δ}  → Γ ⁏ Δ [⊢] A ∧ B → Γ ⁏ Δ [⊢] A
    [snd]     : ∀ {A B Γ Δ}  → Γ ⁏ Δ [⊢] A ∧ B → Γ ⁏ Δ [⊢] B
    [tt]      : ∀ {Γ Δ}      → Γ ⁏ Δ [⊢] ⊤

  infix 3 _⁏_[⊢]⋆_
  _⁏_[⊢]⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
  Γ ⁏ Δ [⊢]⋆ ⌀     = 𝟙
  Γ ⁏ Δ [⊢]⋆ Π , A = Γ ⁏ Δ [⊢]⋆ Π × Γ ⁏ Δ [⊢] A

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 _⁏_⊩_
  _⁏_⊩_ : Cx Ty → Cx Ty → Ty → Set
  Γ ⁏ Δ ⊩ α P   = Γ ⁏ Δ [⊢] α P × Γ ⁏ Δ ⊩ᵅ P
  Γ ⁏ Δ ⊩ A ▻ B = ∀ {Γ′ Δ′} → Γ ⊆ Γ′ → Δ ⊆ Δ′ → Γ′ ⁏ Δ′ [⊢] A ▻ B × (Γ′ ⁏ Δ′ ⊩ A → Γ′ ⁏ Δ′ ⊩ B)
  Γ ⁏ Δ ⊩ □ A   = ∀ {Γ′ Δ′} → Γ ⊆ Γ′ → Δ ⊆ Δ′ → Γ′ ⁏ Δ′ [⊢] □ A × Γ′ ⁏ Δ′ ⊩ A
  Γ ⁏ Δ ⊩ A ∧ B = Γ ⁏ Δ ⊩ A × Γ ⁏ Δ ⊩ B
  Γ ⁏ Δ ⊩ ⊤    = 𝟙

  infix 3 _⁏_⊩⋆_
  _⁏_⊩⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
  Γ ⁏ Δ ⊩⋆ ⌀     = 𝟙
  Γ ⁏ Δ ⊩⋆ Π , A = Γ ⁏ Δ ⊩⋆ Π × Γ ⁏ Δ ⊩ A


-- Monotonicity with respect to context inclusion.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩ A → Γ′ ⁏ Δ ⊩ A
  mono⊩ {α P}   η (t , s) = mono[⊢] η t , mono⊩ᵅ η s
  mono⊩ {A ▻ B} η s       = λ η′ θ → s (trans⊆ η η′) θ
  mono⊩ {□ A}   η s       = λ η′ θ → s (trans⊆ η η′) θ
  mono⊩ {A ∧ B} η (a , b) = mono⊩ {A} η a , mono⊩ {B} η b
  mono⊩ {⊤}    η ∙       = ∙

  mono⊩⋆ : ∀ {Π Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊩⋆ Π → Γ′ ⁏ Δ ⊩⋆ Π
  mono⊩⋆ {⌀}     η ∙        = ∙
  mono⊩⋆ {Π , A} η (ts , t) = mono⊩⋆ {Π} η ts , mono⊩ {A} η t


-- Monotonicity with respect to modal context inclusion.

module _ {{_ : Model}} where
  mmono⊩ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ′ ⊩ A
  mmono⊩ {α P}   θ (t , s) = mmono[⊢] θ t , mmono⊩ᵅ θ s
  mmono⊩ {A ▻ B} θ s       = λ η θ′ → s η (trans⊆ θ θ′)
  mmono⊩ {□ A}   θ s       = λ η θ′ → s η (trans⊆ θ θ′)
  mmono⊩ {A ∧ B} θ (a , b) = mmono⊩ {A} θ a , mmono⊩ {B} θ b
  mmono⊩ {⊤}    θ ∙       = ∙

  mmono⊩⋆ : ∀ {Π Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊩⋆ Π → Γ ⁏ Δ′ ⊩⋆ Π
  mmono⊩⋆ {⌀}     η ∙        = ∙
  mmono⊩⋆ {Π , A} η (ts , t) = mmono⊩⋆ {Π} η ts , mmono⊩ {A} η t


-- Combined monotonicity.

module _ {{_ : Model}} where
  mono²⊩ : ∀ {A Γ Γ′ Δ Δ′} → Γ ⊆ Γ′ × Δ ⊆ Δ′ → Γ ⁏ Δ ⊩ A → Γ′ ⁏ Δ′ ⊩ A
  mono²⊩ {A} (η , θ) = mono⊩ {A} η ∘ mmono⊩ {A} θ

  mono²⊩⋆ : ∀ {Π Γ Γ′ Δ Δ′} → Γ ⊆ Γ′ × Δ ⊆ Δ′ → Γ ⁏ Δ ⊩⋆ Π → Γ′ ⁏ Δ′ ⊩⋆ Π
  mono²⊩⋆ {Π} (η , θ) = mono⊩⋆ {Π} η ∘ mmono⊩⋆ {Π} θ


-- Completeness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  reifyʳ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ [⊢] A
  reifyʳ {α P}   (t , s) = t
  reifyʳ {A ▻ B} s       = let t , f = s refl⊆ refl⊆ in t
  reifyʳ {□ A}   s       = let t , f = s refl⊆ refl⊆ in t
  reifyʳ {A ∧ B} (a , b) = [pair] (reifyʳ {A} a) (reifyʳ {B} b)
  reifyʳ {⊤}    ∙       = [tt]

  reifyʳ⋆ : ∀ {Π Γ Δ} → Γ ⁏ Δ ⊩⋆ Π → Γ ⁏ Δ [⊢]⋆ Π
  reifyʳ⋆ {⌀}     ∙        = ∙
  reifyʳ⋆ {Π , A} (ts , t) = reifyʳ⋆ ts , reifyʳ t


-- Shorthand for variables.

module _ {{_ : Model}} where
  [v₀] : ∀ {A Γ Δ} → Γ , A ⁏ Δ [⊢] A
  [v₀] = [var] i₀

  [v₁] : ∀ {A B Γ Δ} → (Γ , A) , B ⁏ Δ [⊢] A
  [v₁] = [var] i₁

  [v₂] : ∀ {A B C Γ Δ} → ((Γ , A) , B) , C ⁏ Δ [⊢] A
  [v₂] = [var] i₂

  [mv₀] : ∀ {A Γ Δ} → Γ ⁏ Δ , A [⊢] A
  [mv₀] = [mvar] i₀

  [mv₁] : ∀ {A B Γ Δ} → Γ ⁏ (Δ , A) , B [⊢] A
  [mv₁] = [mvar] i₁

  [mv₂] : ∀ {A B C Γ Δ} → Γ ⁏ ((Δ , A) , B) , C [⊢] A
  [mv₂] = [mvar] i₂


-- Useful theorems in functional form.

module _ {{_ : Model}} where
  [mlam] : ∀ {A B Γ Δ} → Γ ⁏ Δ , A [⊢] B → Γ ⁏ Δ [⊢] □ A ▻ B
  [mlam] t = [lam] ([unbox] [v₀] (mono[⊢] weak⊆ t))

  [multicut] : ∀ {Π A Γ Δ} → Γ ⁏ Δ [⊢]⋆ Π → Π ⁏ Δ [⊢] A → Γ ⁏ Δ [⊢] A
  [multicut] {⌀}     ∙        u = mono[⊢] bot⊆ u
  [multicut] {Π , B} (ts , t) u = [app] ([multicut] ts ([lam] u)) t

  [mmulticut] : ∀ {Π A Γ Δ} → Γ ⁏ Δ [⊢]⋆ □⋆ Π → Γ ⁏ Π [⊢] A → Γ ⁏ Δ [⊢] A
  [mmulticut] {⌀}     ∙        u = mmono[⊢] bot⊆ u
  [mmulticut] {Π , B} (ts , t) u = [app] ([mmulticut] ts ([mlam] u)) t

  [multicut²] : ∀ {Π Π′ A Γ Δ} → Γ ⁏ Δ [⊢]⋆ Π → Γ ⁏ Δ [⊢]⋆ □⋆ Π′ → Π ⁏ Π′ [⊢] A → Γ ⁏ Δ [⊢] A
  [multicut²] {⌀}     ∙        us v = [mmulticut] us (mono[⊢] bot⊆ v)
  [multicut²] {Π , B} (ts , t) us v = [app] ([multicut²] ts us ([lam] v)) t

  [dist] : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] □ (A ▻ B) → Γ ⁏ Δ [⊢] □ A → Γ ⁏ Δ [⊢] □ B
  [dist] t u = [unbox] t ([unbox] (mmono[⊢] weak⊆ u) ([box] ([app] [mv₁] [mv₀])))

  [up] : ∀ {A Γ Δ} → Γ ⁏ Δ [⊢] □ A → Γ ⁏ Δ [⊢] □ □ A
  [up] t = [unbox] t ([box] ([box] [mv₀]))


-- Useful theorems in combinatory form.

module _ {{_ : Model}} where
  [ck] : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] A ▻ B ▻ A
  [ck] = [lam] ([lam] [v₁])

  [cs] : ∀ {A B C Γ Δ} → Γ ⁏ Δ [⊢] (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
  [cs] = [lam] ([lam] ([lam] ([app] ([app] [v₂] [v₀]) ([app] [v₁] [v₀]))))

  [cdist] : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] □ (A ▻ B) ▻ □ A ▻ □ B
  [cdist] = [lam] ([lam] ([dist] [v₁] [v₀]))

  [cup] : ∀ {A Γ Δ} → Γ ⁏ Δ [⊢] □ A ▻ □ □ A
  [cup] = [lam] ([up] [v₀])

  [cpair] : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] A ▻ B ▻ A ∧ B
  [cpair] = [lam] ([lam] ([pair] [v₁] [v₀]))


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B
  s ⟪$⟫ a = let t , f = s refl⊆ refl⊆
            in  f a

  ⟪K⟫ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B ▻ A
  ⟪K⟫ {A} a η θ = let a′ = mono²⊩ {A} (η , θ) a
                  in  [app] [ck] (reifyʳ a′) , K a′

  ⟪S⟫ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B ▻ C → Γ ⁏ Δ ⊩ A ▻ B → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ C
  ⟪S⟫ s₁ s₂ a = let t , f = s₁ refl⊆ refl⊆
                    u , g = s₂ refl⊆ refl⊆
                    _ , h = (f a) refl⊆ refl⊆
                in  h (g a)

  ⟪S⟫′ : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊩ A ▻ B ▻ C → Γ ⁏ Δ ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} s₁ η θ = let s₁′   = mono²⊩ {A ▻ B ▻ C} (η , θ) s₁
                                t , _ = s₁′ refl⊆ refl⊆
                            in  [app] [cs] t , λ s₂ η′ θ′ →
                                  let s₁″    = mono²⊩ {A ▻ B ▻ C} (trans⊆ η η′ , trans⊆ θ θ′) s₁
                                      t′ , _ = s₁″ refl⊆ refl⊆
                                      s₂′    = mono²⊩ {A ▻ B} (η′ , θ′) s₂
                                      u  , g = s₂′ refl⊆ refl⊆
                                  in  [app] ([app] [cs] t′) u , ⟪S⟫ s₁″ s₂′

  _⟪D⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ □ (A ▻ B) → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ □ B
  (s₁ ⟪D⟫ s₂) η θ = let t , f = s₁ η θ
                        u , a = s₂ η θ
                    in  [app] ([app] [cdist] t) u , f ⟪$⟫ a

  -- TODO: Report bug.
  _⟪D⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ □ (A ▻ B) → Γ ⁏ Δ ⊩ □ A ▻ □ B
  _⟪D⟫′_ {A} {B} s η θ = let s′ = mono²⊩ {□ (A ▻ B)} (η , θ) s
                         in  [app] [cdist] (reifyʳ (λ {Γ″} {Δ″} η′ θ′ → s′ η′ θ′)) , _⟪D⟫_ s′

  ⟪↑⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ □ □ A
  ⟪↑⟫ {A} s η θ = let t , a = s η θ
                  in  [app] [cup] t , λ η′ θ′ → s (trans⊆ η η′) (trans⊆ θ θ′)

  ⟪↓⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ A
  ⟪↓⟫ s = let p , a = s refl⊆ refl⊆
          in  a

  _⟪,⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} a η θ = let a′ = mono²⊩ {A} (η , θ) a
                     in  [app] [cpair] (reifyʳ a′) , _,_ a′


-- Forcing in a particular world of a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⁏_⊩_⁏_⇒_
  _⁏_⊩_⁏_⇒_ : Cx Ty → Cx Ty → Cx Ty → Cx Ty → Ty → Set
  Γ₀ ⁏ Δ₀ ⊩ Γ ⁏ Δ ⇒ A = Γ₀ ⁏ Δ₀ ⊩⋆ Γ → Γ₀ ⁏ Δ₀ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊩ A

  infix 3 _⁏_⊩_⁏_⇒⋆_
  _⁏_⊩_⁏_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Cx Ty → Cx Ty → Set
  Γ₀ ⁏ Δ₀ ⊩ Γ ⁏ Δ ⇒⋆ Π = Γ₀ ⁏ Δ₀ ⊩⋆ Γ → Γ₀ ⁏ Δ₀ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊩⋆ Π


-- Entailment, or forcing in all worlds of all models, for sequents.

infix 3 _⁏_⊨_
_⁏_⊨_ : Cx Ty → Cx Ty → Ty → Set₁
Γ ⁏ Δ ⊨ A = ∀ {{_ : Model}} {Γ₀ Δ₀ : Cx Ty} → Γ₀ ⁏ Δ₀ ⊩ Γ ⁏ Δ ⇒ A

infix 3 _⁏_⊨⋆_
_⁏_⊨⋆_ : Cx Ty → Cx Ty → Cx Ty → Set₁
Γ ⁏ Δ ⊨⋆ Π = ∀ {{_ : Model}} {Γ₀ Δ₀ : Cx Ty} → Γ₀ ⁏ Δ₀ ⊩ Γ ⁏ Δ ⇒⋆ Π


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ Γ₀ Δ₀} → A ∈ Γ → Γ₀ ⁏ Δ₀ ⊩⋆ Γ → Γ₀ ⁏ Δ₀ ⊩ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  mlookup : ∀ {A Δ Γ₀ Δ₀} → A ∈ Δ → Γ₀ ⁏ Δ₀ ⊩⋆ □⋆ Δ → Γ₀ ⁏ Δ₀ ⊩ A
  mlookup top     (γ , s) = let t , a = s refl⊆ refl⊆ in a
  mlookup (pop i) (γ , s) = mlookup i γ

  -- TODO: More equipment.
