module Common.Context where

open import Common.Core public


-- Contexts.

infixl 2 _,_
data Cx (U : Set) : Set where
  ∅   : Cx U
  _,_ : Cx U → U → Cx U


-- Context membership, as nameless typed de Bruijn indices.

module _ {U : Set} where
  infix 1 _∈_
  data _∈_ (A : U) : Cx U → Set where
    top : ∀ {Γ} → A ∈ Γ , A
    pop : ∀ {B Γ} → A ∈ Γ → A ∈ Γ , B


  -- Context extension, or order-preserving embedding.

  infix 1 _⊆_
  data _⊆_ : Cx U → Cx U → Set where
    done : ∅ ⊆ ∅
    skip : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊆ Γ′ , A
    keep : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ , A ⊆ Γ′ , A

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ {∅}     = done
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

  zero⊆ : ∀ {Γ} → ∅ ⊆ Γ
  zero⊆ {∅}     = done
  zero⊆ {Γ , A} = skip zero⊆


  -- Monotonicity of context membership with respect to extension.

  mono∈ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → A ∈ Γ → A ∈ Γ′
  mono∈ done     ()
  mono∈ (skip η) i       = pop (mono∈ η i)
  mono∈ (keep η) top     = top
  mono∈ (keep η) (pop i) = pop (mono∈ η i)


  -- Context concatenation.

  _±±_ : Cx U → Cx U → Cx U
  Γ ±± ∅        = Γ
  Γ ±± (Γ′ , A) = (Γ ±± Γ′) , A


  -- Monotonicity of context membership with respect to concatenation.

  mono∈ᴸ : ∀ {A Γ} Γ′ → A ∈ Γ → A ∈ Γ ±± Γ′
  mono∈ᴸ ∅        i = i
  mono∈ᴸ (Γ′ , A) i = pop (mono∈ᴸ Γ′ i)

  mono∈ᴿ : ∀ {A Γ Γ′} → A ∈ Γ′ → A ∈ Γ ±± Γ′
  mono∈ᴿ top     = top
  mono∈ᴿ (pop i) = pop (mono∈ᴿ i)
