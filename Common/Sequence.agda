module Common.Sequence where

open import Common.Core public


-- Sequences.

infixr 2 _∷_
data Seq (U : Set) : Set where
  []  : Seq U
  _∷_ : U → Seq U → Seq U


-- Sequence membership, as nameless typed de Bruijn indices.

module _ {U : Set} where
  infix 1 _∋_
  data _∋_ : Seq U → U → Set where
    top : ∀ {A Π} → A ∷ Π ∋ A
    pop : ∀ {A B Π} → Π ∋ A → B ∷ Π ∋ A


  -- Sequence concatenation.

  _⧺ₛ_ : Seq U → Seq U → Seq U
  []      ⧺ₛ Π′ = Π′
  (A ∷ Π) ⧺ₛ Π′ = A ∷ (Π ⧺ₛ Π′)


  -- Monotonicity of sequence membership with respect to concatenation.

  mono∋ : ∀ {A Π Π′} → Π ∋ A → Π ⧺ₛ Π′ ∋ A
  mono∋ top     = top
  mono∋ (pop i) = pop (mono∋ i)

  mono∋′ : ∀ {A} Π {Π′} → Π′ ∋ A → Π ⧺ₛ Π′ ∋ A
  mono∋′ []      i = i
  mono∋′ (A ∷ Π) i = pop (mono∋′ Π i)
