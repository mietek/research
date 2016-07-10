module Common.Context where

open import Common.Core public


-- Contexts.

infixl 2 _,_
data Cx (U : Set) : Set where
  ⌀   : Cx U
  _,_ : Cx U → U → Cx U


-- Context membership, as nameless typed de Bruijn indices.

module _ {U : Set} where
  infix 1 _∈_
  data _∈_ (A : U) : Cx U → Set where
    top : ∀ {Γ} → A ∈ Γ , A
    pop : ∀ {C Γ} → A ∈ Γ → A ∈ Γ , C

  i₀ : ∀ {A Γ} → A ∈ Γ , A
  i₀ = top

  i₁ : ∀ {A B Γ} → A ∈ Γ , A , B
  i₁ = pop i₀

  i₂ : ∀ {A B C Γ} → A ∈ Γ , A , B , C
  i₂ = pop i₁


  -- Context inclusion, or order-preserving embedding.

  infix 1 _⊆_
  data _⊆_ : Cx U → Cx U → Set where
    done : ⌀ ⊆ ⌀
    skip : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊆ Γ′ , A
    keep : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ , A ⊆ Γ′ , A

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ {⌀}     = done
  refl⊆ {Γ , A} = keep refl⊆

  trans⊆ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  trans⊆ η        done      = η
  trans⊆ η        (skip η′) = skip (trans⊆ η η′)
  trans⊆ (skip η) (keep η′) = skip (trans⊆ η η′)
  trans⊆ (keep η) (keep η′) = keep (trans⊆ η η′)

  unskip⊆ : ∀ {A Γ Γ′} → Γ , A ⊆ Γ′ → Γ ⊆ Γ′
  unskip⊆ (skip η) = skip (unskip⊆ η)
  unskip⊆ (keep η) = skip η

  unkeep⊆ : ∀ {A Γ Γ′} → Γ , A ⊆ Γ′ , A → Γ ⊆ Γ′
  unkeep⊆ (skip η) = unskip⊆ η
  unkeep⊆ (keep η) = η

  weak⊆ : ∀ {A Γ} → Γ ⊆ Γ , A
  weak⊆ = skip refl⊆

  bot⊆ : ∀ {Γ} → ⌀ ⊆ Γ
  bot⊆ {⌀}     = done
  bot⊆ {Γ , A} = skip bot⊆


  -- Monotonicity of context membership with respect to context inclusion.

  mono∈ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → A ∈ Γ → A ∈ Γ′
  mono∈ done     ()
  mono∈ (skip η) i       = pop (mono∈ η i)
  mono∈ (keep η) top     = top
  mono∈ (keep η) (pop i) = pop (mono∈ η i)

  reflmono∈ : ∀ {A Γ} → (i : A ∈ Γ) → i ≡ mono∈ refl⊆ i
  reflmono∈ top     = refl
  reflmono∈ (pop i) = cong pop (reflmono∈ i)

  transmono∈ : ∀ {A Γ Γ′ Γ″} → (η : Γ ⊆ Γ′) (η′ : Γ′ ⊆ Γ″) (i : A ∈ Γ)
               → mono∈ η′ (mono∈ η i) ≡ mono∈ (trans⊆ η η′) i
  transmono∈ done     η′        ()
  transmono∈ η        (skip η′) i       = cong pop (transmono∈ η η′ i)
  transmono∈ (skip η) (keep η′) i       = cong pop (transmono∈ η η′ i)
  transmono∈ (keep η) (keep η′) top     = refl
  transmono∈ (keep η) (keep η′) (pop i) = cong pop (transmono∈ η η′ i)


  -- Context concatenation.

  _⧺_ : Cx U → Cx U → Cx U
  Γ ⧺ ⌀        = Γ
  Γ ⧺ (Γ′ , A) = (Γ ⧺ Γ′) , A

  id⧺ₗ : ∀ {Γ} → Γ ⧺ ⌀ ≡ Γ
  id⧺ₗ = refl

  id⧺ᵣ : ∀ {Γ} → ⌀ ⧺ Γ ≡ Γ
  id⧺ᵣ {⌀}     = refl
  id⧺ᵣ {Γ , A} = cong₂ _,_ id⧺ᵣ refl

  weak⊆⧺ₗ : ∀ {Γ} Γ′ → Γ ⊆ Γ ⧺ Γ′
  weak⊆⧺ₗ ⌀        = refl⊆
  weak⊆⧺ₗ (Γ′ , A) = skip (weak⊆⧺ₗ Γ′)

  weak⊆⧺ᵣ : ∀ {Γ Γ′} → Γ′ ⊆ Γ ⧺ Γ′
  weak⊆⧺ᵣ {Γ} {⌀}      = bot⊆
  weak⊆⧺ᵣ {Γ} {Γ′ , A} = keep weak⊆⧺ᵣ


  -- Context thinning.

  _-_ : ∀ {A} → (Γ : Cx U) → A ∈ Γ → Cx U
  ⌀       - ()
  (Γ , A) - top   = Γ
  (Γ , B) - pop i = (Γ - i) , B

  thin⊆ : ∀ {A Γ} → (i : A ∈ Γ) → Γ - i ⊆ Γ
  thin⊆ top     = weak⊆
  thin⊆ (pop i) = keep (thin⊆ i)


  -- Decidable context membership equality.

  data _=∈_ {A Γ} (i : A ∈ Γ) : ∀ {C} → C ∈ Γ → Set where
    same : i =∈ i
    diff : ∀ {C} → (k : C ∈ Γ - i) → i =∈ mono∈ (thin⊆ i) k

  _≟∈_ : ∀ {A C Γ} → (i : A ∈ Γ) (k : C ∈ Γ) → i =∈ k
  top ≟∈ top      = same
  top ≟∈ pop k    rewrite reflmono∈ k = diff k
  pop i ≟∈ top    = diff top
  pop i ≟∈ pop k  with i ≟∈ k
  pop i ≟∈ pop .i | same = same
  pop i ≟∈ pop ._ | diff k = diff (pop k)
