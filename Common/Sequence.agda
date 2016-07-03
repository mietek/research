module Common.Sequence (U : Set) where


-- Sequences.

infixr 2 _∷_
data Seq (U : Set) : Set where
  []  : Seq U
  _∷_ : U → Seq U → Seq U


-- Sequence membership, as nameless typed de Bruijn indices.

infix 1 _∋_
data _∋_ : Seq U → U → Set where
  top : ∀ {A Π} → A ∷ Π ∋ A
  pop : ∀ {A B Π} → Π ∋ A → B ∷ Π ∋ A


-- Concatenation of sequences.

_++_ : Seq U → Seq U → Seq U
[]      ++ Π′ = Π′
(A ∷ Π) ++ Π′ = A ∷ (Π ++ Π′)

mono∋⁺⁺ : ∀ {A Π Π′} → Π ∋ A → Π ++ Π′ ∋ A
mono∋⁺⁺ top     = top
mono∋⁺⁺ (pop i) = pop (mono∋⁺⁺ i)

mono⁺⁺∋ : ∀ {A} Π {Π′} → Π′ ∋ A → Π ++ Π′ ∋ A
mono⁺⁺∋ []      i = i
mono⁺⁺∋ (A ∷ Π) i = pop (mono⁺⁺∋ Π i)