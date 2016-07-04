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

  _∓∓_ : Seq U → Seq U → Seq U
  []      ∓∓ Π′ = Π′
  (A ∷ Π) ∓∓ Π′ = A ∷ (Π ∓∓ Π′)


  -- Monotonicity of sequence membership with respect to concatenation.

  mono∋ᴸ : ∀ {A Π Π′} → Π ∋ A → Π ∓∓ Π′ ∋ A
  mono∋ᴸ top     = top
  mono∋ᴸ (pop i) = pop (mono∋ᴸ i)

  mono∋ᴿ : ∀ {A} Π {Π′} → Π′ ∋ A → Π ∓∓ Π′ ∋ A
  mono∋ᴿ []      i = i
  mono∋ᴿ (A ∷ Π) i = pop (mono∋ᴿ Π i)
