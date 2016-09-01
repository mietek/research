-- Tarski-style semantics with contexts as concrete worlds, and glueing for □ only.
-- Gentzen-style syntax.

module BasicIS4.Semantics.TarskiGluedGentzen where

open import BasicIS4.Syntax.Common public
open import Common.Semantics public


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
    top[⊢⋆] : ∀ {Γ}     → (Γ [⊢⋆] ∅) ≡ 𝟙
    pop[⊢⋆] : ∀ {Ξ A Γ} → (Γ [⊢⋆] Ξ , A) ≡ (Γ [⊢⋆] Ξ × Γ [⊢] A)

  infix 3 _[⊢]⋆_
  _[⊢]⋆_ : Cx Ty → Cx Ty → Set
  Γ [⊢]⋆ ∅     = 𝟙
  Γ [⊢]⋆ Ξ , A = Γ [⊢]⋆ Ξ × Γ [⊢] A

  [⊢⋆]→[⊢]⋆ : ∀ {Ξ Γ} → Γ [⊢⋆] Ξ → Γ [⊢]⋆ Ξ
  [⊢⋆]→[⊢]⋆ {∅}     {Γ} ts = ∙
  [⊢⋆]→[⊢]⋆ {Ξ , A} {Γ} ts rewrite pop[⊢⋆] {Ξ} {A} {Γ} = [⊢⋆]→[⊢]⋆ (π₁ ts) , π₂ ts

  [⊢]⋆→[⊢⋆] : ∀ {Ξ Γ} → Γ [⊢]⋆ Ξ → Γ [⊢⋆] Ξ
  [⊢]⋆→[⊢⋆] {∅}     {Γ} ∙        rewrite top[⊢⋆] {Γ}         = ∙
  [⊢]⋆→[⊢⋆] {Ξ , A} {Γ} (ts , t) rewrite pop[⊢⋆] {Ξ} {A} {Γ} = [⊢]⋆→[⊢⋆] ts , t

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : Cx Ty → Ty → Set
  Γ ⊩ α P   = Γ ⊩ᵅ P
  Γ ⊩ A ▻ B = ∀ {Γ′} → Γ ⊆ Γ′ → Γ′ ⊩ A → Γ′ ⊩ B
  Γ ⊩ □ A   = ∀ {Γ′} → Γ ⊆ Γ′ → Glue (Γ′ [⊢] □ A) (Γ′ ⊩ A)
  Γ ⊩ A ∧ B = Γ ⊩ A × Γ ⊩ B
  Γ ⊩ ⊤    = 𝟙

  infix 3 _⊩⋆_
  _⊩⋆_ : Cx Ty → Cx Ty → Set
  Γ ⊩⋆ ∅     = 𝟙
  Γ ⊩⋆ Ξ , A = Γ ⊩⋆ Ξ × Γ ⊩ A


-- Monotonicity with respect to context inclusion.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩ A → Γ′ ⊩ A
  mono⊩ {α P}   η s = mono⊩ᵅ η s
  mono⊩ {A ▻ B} η s = λ η′ → s (trans⊆ η η′)
  mono⊩ {□ A}   η s = λ η′ → s (trans⊆ η η′)
  mono⊩ {A ∧ B} η s = mono⊩ {A} η (π₁ s) , mono⊩ {B} η (π₂ s)
  mono⊩ {⊤}    η s = ∙

  mono⊩⋆ : ∀ {Ξ Γ Γ′} → Γ ⊆ Γ′ → Γ ⊩⋆ Ξ → Γ′ ⊩⋆ Ξ
  mono⊩⋆ {∅}     η ∙        = ∙
  mono⊩⋆ {Ξ , A} η (ts , t) = mono⊩⋆ {Ξ} η ts , mono⊩ {A} η t


-- Shorthand for variables.

module _ {{_ : Model}} where
  [v₀] : ∀ {A Γ} → Γ , A [⊢] A
  [v₀] = [var] i₀

  [v₁] : ∀ {A B Γ} → Γ , A , B [⊢] A
  [v₁] = [var] i₁

  [v₂] : ∀ {A B C Γ} → Γ , A , B , C [⊢] A
  [v₂] = [var] i₂


-- Useful theorems in functional form.

module _ {{_ : Model}} where
  [multicut] : ∀ {Ξ A Γ} → Γ [⊢]⋆ Ξ → Ξ [⊢] A → Γ [⊢] A
  [multicut] {∅}     ∙        u = mono[⊢] bot⊆ u
  [multicut] {Ξ , B} (ts , t) u = [app] ([multicut] ts ([lam] u)) t

  [dist] : ∀ {A B Γ} → Γ [⊢] □ (A ▻ B) → Γ [⊢] □ A → Γ [⊢] □ B
  [dist] t u = [multibox] ([⊢]⋆→[⊢⋆] ((∙ , t) , u)) ([app] ([down] [v₁]) ([down] [v₀]))

  [up] : ∀ {A Γ} → Γ [⊢] □ A → Γ [⊢] □ □ A
  [up] t = [multibox] ([⊢]⋆→[⊢⋆] ((∙ , t))) [v₀]


-- Additional useful equipment.

module _ {{_ : Model}} where

  _⟪$⟫_ : ∀ {A B Γ} → Γ ⊩ A ▻ B → Γ ⊩ A → Γ ⊩ B
  s ⟪$⟫ a = s refl⊆ a

  ⟪K⟫ : ∀ {A B Γ} → Γ ⊩ A → Γ ⊩ B ▻ A
  ⟪K⟫ {A} a η = K (mono⊩ {A} η a)

  ⟪S⟫ : ∀ {A B C Γ} → Γ ⊩ A ▻ B ▻ C → Γ ⊩ A ▻ B → Γ ⊩ A → Γ ⊩ C
  ⟪S⟫ {A} {B} {C} s₁ s₂ a = _⟪$⟫_ {B} {C} (_⟪$⟫_ {A} {B ▻ C} s₁ a) (_⟪$⟫_ {A} {B} s₂ a)

  ⟪S⟫′ : ∀ {A B C Γ} → Γ ⊩ A ▻ B ▻ C → Γ ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} s₁ η s₂ η′ a = let s₁′ = mono⊩ {A ▻ B ▻ C} (trans⊆ η η′) s₁
                                      s₂′ = mono⊩ {A ▻ B} η′ s₂
                                  in  ⟪S⟫ {A} {B} {C} s₁′ s₂′ a

  _⟪D⟫_ : ∀ {A B Γ} → Γ ⊩ □ (A ▻ B) → Γ ⊩ □ A → Γ ⊩ □ B
  _⟪D⟫_ {A} {B} s₁ s₂ η = let t ⅋ s₁′ = s₁ η
                              u ⅋ a   = s₂ η
                          in  [dist] t u ⅋ _⟪$⟫_ {A} {B} s₁′ a

  _⟪D⟫′_ : ∀ {A B Γ} → Γ ⊩ □ (A ▻ B) → Γ ⊩ □ A ▻ □ B
  _⟪D⟫′_ {A} {B} s₁ η = _⟪D⟫_ (mono⊩ {□ (A ▻ B)} η s₁)

  ⟪↑⟫ : ∀ {A Γ} → Γ ⊩ □ A → Γ ⊩ □ □ A
  ⟪↑⟫ s η = [up] (syn (s η)) ⅋ λ η′ → s (trans⊆ η η′)

  ⟪↓⟫ : ∀ {A Γ} → Γ ⊩ □ A → Γ ⊩ A
  ⟪↓⟫ s = sem (s refl⊆)

  _⟪,⟫′_ : ∀ {A B Γ} → Γ ⊩ A → Γ ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} {B} a η = _,_ (mono⊩ {A} η a)


-- Forcing in a particular world of a particular model, for sequents.

module _ {{_ : Model}} where
  infix 3 _⊩_⇒_
  _⊩_⇒_ : Cx Ty → Cx Ty → Ty → Set
  w ⊩ Γ ⇒ A = w ⊩⋆ Γ → w ⊩ A

  infix 3 _⊩_⇒⋆_
  _⊩_⇒⋆_ : Cx Ty → Cx Ty → Cx Ty → Set
  w ⊩ Γ ⇒⋆ Ξ = w ⊩⋆ Γ → w ⊩⋆ Ξ


-- Entailment, or forcing in all models, for sequents.

infix 3 _⊨_
_⊨_ : Cx Ty → Ty → Set₁
Γ ⊨ A = ∀ {{_ : Model}} {w : Cx Ty} → w ⊩ Γ ⇒ A

infix 3 _⊨⋆_
_⊨⋆_ : Cx Ty → Cx Ty → Set₁
Γ ⊨⋆ Ξ = ∀ {{_ : Model}} {w : Cx Ty} → w ⊩ Γ ⇒⋆ Ξ


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  lookup : ∀ {A Γ w} → A ∈ Γ → w ⊩ Γ ⇒ A
  lookup top     (γ , a) = a
  lookup (pop i) (γ , b) = lookup i γ

  _⟦$⟧_ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B
  _⟦$⟧_ {A} {B} s₁ s₂ γ = _⟪$⟫_ {A} {B} (s₁ γ) (s₂ γ)

  ⟦K⟧ : ∀ {A B Γ w} → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ B ▻ A
  ⟦K⟧ {A} {B} a γ = ⟪K⟫ {A} {B} (a γ)

  ⟦S⟧ : ∀ {A B C Γ w} → w ⊩ Γ ⇒ A ▻ B ▻ C → w ⊩ Γ ⇒ A ▻ B → w ⊩ Γ ⇒ A → w ⊩ Γ ⇒ C
  ⟦S⟧ {A} {B} {C} s₁ s₂ a γ = ⟪S⟫ {A} {B} {C} (s₁ γ) (s₂ γ) (a γ)

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
