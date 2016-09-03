module Common.PredicateBasedContext where

open import Common.Predicate public


-- Predicate-based context membership.

module _ {U : Set} where
  infix 3 _∈_
  _∈_ : U → Pred (Cx U)
  A ∈ Γ = Any (_≡ A) Γ

  infix 3 _∉_
  _∉_ : U → Pred (Cx U)
  A ∉ Γ = Not (A ∈ Γ)

  lookup : ∀ {Γ P} → All P Γ → (∀ {A} → A ∈ Γ → P A)
  -- Alternatively:
  -- lookup : ∀ {Γ P} → All P Γ → (_∈ Γ) ⊆ᴾ P
  lookup ∅       ()
  lookup (γ , a) (top refl) = a
  lookup (γ , a) (pop i)    = lookup γ i

  tabulate : ∀ {Γ P} → (∀ {A} → A ∈ Γ → P A) → All P Γ
  -- Alternatively:
  -- tabulate : ∀ {Γ P} → (_∈ Γ) ⊆ᴾ P → All P Γ
  tabulate {∅}     f = ∅
  tabulate {Γ , A} f = tabulate (f ∘ pop) , f (top refl)

  bot∈ : ∀ {A} → A ∉ ∅
  bot∈ ()

  [_]ᴵˣ : ∀ {A Γ} → A ∈ Γ → ℕ
  [ top refl ]ᴵˣ = zero
  [ pop i ]ᴵˣ    = suc [ i ]ᴵˣ

  i₀ : ∀ {A Γ} → A ∈ Γ , A
  i₀ = top refl

  i₁ : ∀ {A B Γ} → A ∈ Γ , A , B
  i₁ = pop i₀

  i₂ : ∀ {A B C Γ} → A ∈ Γ , A , B , C
  i₂ = pop i₁


-- Predicate-based context inclusion.

module _ {U : Set} where
  -- NOTE: This is similar to Ren from Conor’s fish-and-chips development.
  infix 3 _⊆_
  _⊆_ : Cx U → Pred (Cx U)
  Γ ⊆ Γ′ = ∀ {A} → A ∈ Γ → A ∈ Γ′
  -- Alternatively:
  -- Γ ⊆ Γ′ = (_∈ Γ) ⊆ᴾ (_∈ Γ′)

  infix 3 _⊈_
  _⊈_ : Cx U → Pred (Cx U)
  Γ ⊈ Γ′ = Not (Γ ⊆ Γ′)

  skip⊆ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊆ Γ′ , A
  skip⊆ η = pop ∘ η

  -- NOTE: This is similar to wkr from Conor’s fish-and-chips development.
  keep⊆ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ , A ⊆ Γ′ , A
  keep⊆ η (top refl) = top refl
  keep⊆ η (pop i)    = pop (η i)

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ {Γ} = refl⊆ᴾ {P = _∈ Γ}

  trans⊆ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  trans⊆ {Γ} η η′ = trans⊆ᴾ {P = _∈ Γ} η η′

  unskip⊆ : ∀ {A Γ Γ′} → Γ , A ⊆ Γ′ → Γ ⊆ Γ′
  unskip⊆ η = η ∘ pop

  -- NOTE: This doesn’t seem possible.
  -- unkeep⊆ : ∀ {A Γ Γ′} → Γ , A ⊆ Γ′ , A → Γ ⊆ Γ′

  weak⊆ : ∀ {A Γ} → Γ ⊆ Γ , A
  weak⊆ = pop

  bot⊆ : ∀ {Γ} → ∅  ⊆ Γ
  bot⊆ ()


-- Predicate-based context equality.

module _ {U : Set} where
  infix 3 _⫗_
  _⫗_ : Cx U → Pred (Cx U)
  Γ ⫗ Γ′ = (Γ ⊆ Γ′) × (Γ′ ⊆ Γ)

  infix 3 _⫘_
  _⫘_ : Cx U → Pred (Cx U)
  Γ ⫘ Γ′ = Not (Γ ⫗ Γ′)

  refl⫗ : ∀ {Γ} → Γ ⫗ Γ
  refl⫗ {Γ} = refl⫗ᴾ {P = _∈ Γ}

  trans⫗ : ∀ {Γ Γ′ Γ″} → Γ ⫗ Γ′ → Γ′ ⫗ Γ″ → Γ ⫗ Γ″
  trans⫗ {Γ} σ σ′ = trans⫗ᴾ {P = _∈ Γ} σ σ′

  sym⫗ : ∀ {Γ Γ′} → Γ ⫗ Γ′ → Γ′ ⫗ Γ
  sym⫗ {Γ} σ = sym⫗ᴾ {P = _∈ Γ} σ

  antisym⊆ : ∀ {Γ Γ′} → ((Γ ⊆ Γ′) × (Γ′ ⊆ Γ)) ≡ (Γ ⫗ Γ′)
  antisym⊆ {Γ} = antisym⊆ᴾ {P = _∈ Γ}


-- Monotonicity with respect to predicate-based context inclusion.

module _ {U : Set} where
  mono∈ : ∀ {A : U} {Γ Γ′} → Γ ⊆ Γ′ → A ∈ Γ → A ∈ Γ′
  mono∈ η i = η i

  reflmono∈ : ∀ {A Γ} → (i : A ∈ Γ) → i ≡ mono∈ refl⊆ i
  reflmono∈ i = refl

  transmono∈ : ∀ {A Γ Γ′ Γ″} → (η : Γ ⊆ Γ′) (η′ : Γ′ ⊆ Γ″) (i : A ∈ Γ)
               → mono∈ η′ (mono∈ η i) ≡ mono∈ (trans⊆ η η′) i
  transmono∈ η η′ i = refl


-- Predicate-based context concatenation.

module _ {U : Set} where
  _⧺_ : Cx U → Cx U → Cx U
  Γ ⧺ ∅        = Γ
  Γ ⧺ (Γ′ , A) = (Γ ⧺ Γ′) , A

  id⧺₁ : ∀ {Γ} → Γ ⧺ ∅ ≡ Γ
  id⧺₁ = refl

  id⧺₂ : ∀ {Γ} → ∅  ⧺ Γ ≡ Γ
  id⧺₂ {∅}     = refl
  id⧺₂ {Γ , A} = cong² _,_ id⧺₂ refl

  weak⊆⧺₁ : ∀ {Γ} Γ′ → Γ ⊆ Γ ⧺ Γ′
  weak⊆⧺₁ ∅        = refl⊆
  weak⊆⧺₁ (Γ′ , A) = skip⊆ (weak⊆⧺₁ Γ′)

  weak⊆⧺₂ : ∀ {Γ Γ′} → Γ′ ⊆ Γ ⧺ Γ′
  weak⊆⧺₂ {Γ} {∅}      = bot⊆
  weak⊆⧺₂ {Γ} {Γ′ , A} = keep⊆ weak⊆⧺₂


-- Predicate-based context thinning.

module _ {U : Set} where
  _-_ : ∀ {A} → (Γ : Cx U) → A ∈ Γ → Cx U
  ∅       - ()
  (Γ , A) - top refl = Γ
  (Γ , B) - pop i    = (Γ - i) , B

  thin⊆ : ∀ {A Γ} → (i : A ∈ Γ) → Γ - i ⊆ Γ
  thin⊆ (top refl) = pop
  thin⊆ (pop i)    = keep⊆ (thin⊆ i)


-- Decidable predicate-based context membership equality.

module _ {U : Set} where
  data _=∈_ {A : U} {Γ} (i : A ∈ Γ) : ∀ {C} → Pred (C ∈ Γ) where
    same : i =∈ i
    diff : ∀ {C} → (j : C ∈ Γ - i) → i =∈ mono∈ (thin⊆ i) j

  _≟∈_ : ∀ {A C Γ} → (i : A ∈ Γ) (j : C ∈ Γ) → i =∈ j
  top refl ≟∈ top refl = same
  top refl ≟∈ pop j    = diff j
  pop i    ≟∈ top refl = diff (top refl)
  pop i    ≟∈ pop j    with i ≟∈ j
  pop i ≟∈ pop .i      | same = same
  pop i ≟∈ pop ._      | diff j = diff (pop j)
