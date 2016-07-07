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


  -- Context extension, or order-preserving embedding.

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

  zero⊆ : ∀ {Γ} → ⌀ ⊆ Γ
  zero⊆ {⌀}     = done
  zero⊆ {Γ , A} = skip zero⊆


  -- Monotonicity of context membership with respect to extension.

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

  id⧺ : ∀ {Γ} → ⌀ ⧺ Γ ≡ Γ
  id⧺ {⌀}     = refl
  id⧺ {Γ , A} = cong₂ _,_ id⧺ refl

  weak⊆⧺ : ∀ {Γ} Γ′ → Γ ⊆ Γ ⧺ Γ′
  weak⊆⧺ ⌀        = refl⊆
  weak⊆⧺ (Γ′ , A) = skip (weak⊆⧺ Γ′)

  weak⊆⧺′ : ∀ {Γ Γ′} → Γ′ ⊆ Γ ⧺ Γ′
  weak⊆⧺′ {Γ} {⌀}      = zero⊆
  weak⊆⧺′ {Γ} {Γ′ , A} = keep weak⊆⧺′


  -- Thinning, or context removal.

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
