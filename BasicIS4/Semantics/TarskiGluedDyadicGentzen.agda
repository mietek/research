-- Tarski-style semantics with context pairs as concrete worlds, and glueing for □ only.
-- Gentzen-style syntax.

module BasicIS4.Semantics.TarskiGluedDyadicGentzen where

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
    mono²[⊢] : ∀ {A Π Π′} → Π ⊆² Π′ → Π [⊢] A → Π′ [⊢] A
    [var]     : ∀ {A Π}    → A ∈ int Π → Π [⊢] A
    [lam]     : ∀ {A B Π}  → int Π , A ⁏ mod Π [⊢] B → Π [⊢] A ▻ B
    [app]     : ∀ {A B Π}  → Π [⊢] A ▻ B → Π [⊢] A → Π [⊢] B
    [mvar]    : ∀ {A Π}    → A ∈ mod Π → Π [⊢] A
    [box]     : ∀ {A Π}    → ⌀ ⁏ mod Π [⊢] A → Π [⊢] □ A
    [unbox]   : ∀ {A C Π}  → Π [⊢] □ A → int Π ⁏ mod Π , A [⊢] C → Π [⊢] C
    [pair]    : ∀ {A B Π}  → Π [⊢] A → Π [⊢] B → Π [⊢] A ∧ B
    [fst]     : ∀ {A B Π}  → Π [⊢] A ∧ B → Π [⊢] A
    [snd]     : ∀ {A B Π}  → Π [⊢] A ∧ B → Π [⊢] B
    [tt]      : ∀ {Π}      → Π [⊢] ⊤

  infix 3 _[⊢]⋆_
  _[⊢]⋆_ : Cx² Ty → Cx Ty → Set
  Π [⊢]⋆ ⌀     = 𝟙
  Π [⊢]⋆ Ξ , A = Π [⊢]⋆ Ξ × Π [⊢] A

open Model {{…}} public


-- Forcing in a particular model.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : Cx² Ty → Ty → Set
  Π ⊩ α P   = Π ⊩ᵅ P
  Π ⊩ A ▻ B = ∀ {Π′} → Π ⊆² Π′ → Π′ ⊩ A → Π′ ⊩ B
  Π ⊩ □ A   = ∀ {Π′} → Π ⊆² Π′ → Glue (Π′ [⊢] □ A) (Π′ ⊩ A)
  Π ⊩ A ∧ B = Π ⊩ A × Π ⊩ B
  Π ⊩ ⊤    = 𝟙

  infix 3 _⊩⋆_
  _⊩⋆_ : Cx² Ty → Cx Ty → Set
  Π ⊩⋆ ⌀     = 𝟙
  Π ⊩⋆ Ξ , A = Π ⊩⋆ Ξ × Π ⊩ A


-- Monotonicity with respect to context inclusion.

module _ {{_ : Model}} where
  mono²⊩ : ∀ {A Π Π′} → Π ⊆² Π′ → Π ⊩ A → Π′ ⊩ A
  mono²⊩ {α P}   ψ s = mono²⊩ᵅ ψ s
  mono²⊩ {A ▻ B} ψ s = λ ψ′ → s (trans⊆² ψ ψ′)
  mono²⊩ {□ A}   ψ s = λ ψ′ → s (trans⊆² ψ ψ′)
  mono²⊩ {A ∧ B} ψ s = mono²⊩ {A} ψ (π₁ s) , mono²⊩ {B} ψ (π₂ s)
  mono²⊩ {⊤}    ψ s = ∙

  mono²⊩⋆ : ∀ {Ξ Π Π′} → Π ⊆² Π′ → Π ⊩⋆ Ξ → Π′ ⊩⋆ Ξ
  mono²⊩⋆ {⌀}     ψ ∙        = ∙
  mono²⊩⋆ {Ξ , A} ψ (ts , t) = mono²⊩⋆ ψ ts , mono²⊩ {A} ψ t


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
  [multicut] {⌀}     ∙        u = mono²[⊢] (bot⊆ , refl⊆) u
  [multicut] {Ξ , B} (ts , t) u = [app] ([multicut] ts ([lam] u)) t

  [mmulticut] : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ [⊢]⋆ □⋆ Ξ → Γ ⁏ Ξ [⊢] A → Γ ⁏ Δ [⊢] A
  [mmulticut] {⌀}     ∙        u = mono²[⊢] (refl⊆ , bot⊆) u
  [mmulticut] {Ξ , B} (ts , t) u = [app] ([mmulticut] ts ([mlam] u)) t

  [multicut²] : ∀ {Ξ Ξ′ A Γ Δ} → Γ ⁏ Δ [⊢]⋆ Ξ → Γ ⁏ Δ [⊢]⋆ □⋆ Ξ′ → Ξ ⁏ Ξ′ [⊢] A → Γ ⁏ Δ [⊢] A
  [multicut²] {⌀}     ∙        us v = [mmulticut] us (mono²[⊢] (bot⊆ , refl⊆) v)
  [multicut²] {Ξ , B} (ts , t) us v = [app] ([multicut²] ts us ([lam] v)) t

  [dist] : ∀ {A B Γ Δ} → Γ ⁏ Δ [⊢] □ (A ▻ B) → Γ ⁏ Δ [⊢] □ A → Γ ⁏ Δ [⊢] □ B
  [dist] t u = [unbox] t ([unbox] (mono²[⊢] (refl⊆ , weak⊆) u) ([box] ([app] [mv₁] [mv₀])))

  [up] : ∀ {A Γ Δ} → Γ ⁏ Δ [⊢] □ A → Γ ⁏ Δ [⊢] □ □ A
  [up] t = [unbox] t ([box] ([box] [mv₀]))


-- Additional useful equipment.

module _ {{_ : Model}} where
  _⟪$⟫_ : ∀ {A B Π} → Π ⊩ A ▻ B → Π ⊩ A → Π ⊩ B
  s ⟪$⟫ a = s refl⊆² a

  ⟪K⟫ : ∀ {A B Π} → Π ⊩ A → Π ⊩ B ▻ A
  ⟪K⟫ {A} a ψ = K (mono²⊩ {A} ψ a)

  ⟪S⟫ : ∀ {A B C Π} → Π ⊩ A ▻ B ▻ C → Π ⊩ A ▻ B → Π ⊩ A → Π ⊩ C
  ⟪S⟫ {A} {B} {C} s₁ s₂ a = _⟪$⟫_ {B} {C} (_⟪$⟫_ {A} {B ▻ C} s₁ a) (_⟪$⟫_ {A} {B} s₂ a)

  ⟪S⟫′ : ∀ {A B C Π} → Π ⊩ A ▻ B ▻ C → Π ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ {A} {B} {C} s₁ ψ s₂ ψ′ a = let s₁′ = mono²⊩ {A ▻ B ▻ C} (trans⊆² ψ ψ′) s₁
                                      s₂′ = mono²⊩ {A ▻ B} ψ′ s₂
                                  in  ⟪S⟫ {A} {B} {C} s₁′ s₂′ a

  _⟪D⟫_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ □ (A ▻ B) → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ □ B
  _⟪D⟫_ {A} {B} s₁ s₂ ψ = let t ⅋ s₁′ = s₁ ψ
                              u ⅋ a   = s₂ ψ
                          in  [dist] t u ⅋ (_⟪$⟫_ {A} {B} s₁′ a)

  _⟪D⟫′_ : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊩ □ (A ▻ B) → Γ ⁏ Δ ⊩ □ A ▻ □ B
  _⟪D⟫′_ {A} {B} s₁ ψ = _⟪D⟫_ (mono²⊩ {□ (A ▻ B)} ψ s₁)

  ⟪↑⟫ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ □ A → Γ ⁏ Δ ⊩ □ □ A
  ⟪↑⟫ s ψ = [up] (syn (s ψ)) ⅋ λ ψ′ → s (trans⊆² ψ ψ′)

  ⟪↓⟫ : ∀ {A Π} → Π ⊩ □ A → Π ⊩ A
  ⟪↓⟫ s = sem (s refl⊆²)

  _⟪,⟫′_ : ∀ {A B Π} → Π ⊩ A → Π ⊩ B ▻ A ∧ B
  _⟪,⟫′_ {A} {B} a ψ = _,_ (mono²⊩ {A} ψ a)


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
