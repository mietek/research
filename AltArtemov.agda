module AltArtemov where

open import Data.Nat using ( ℕ ; _+_ ; zero ; suc )

infixl 3 _∧_
infixr 2 _⊃_
infixl 1 _∋_

mutual
  data Ty : ℕ → Set where
    ⊥   : ∀{n} → Ty n
    _∧_ : ∀{n} → Ty n → Ty n → Ty n
    _∋_ : ∀{n} → (A : Ty n) → Tm n A → Ty (n + 1)
    _⊃_ : ∀{n} → Ty n → Ty n → Ty n

  data Tm : (n : ℕ) → Ty n → Set where
    fst  : ∀{n A B} → Tm n (A ∧ B) → Tm n A
    snd  : ∀{n A B} → Tm n (A ∧ B) → Tm n B
    pair : ∀{n A B} → Tm n A → Tm n B → Tm n (A ∧ B)

    reflect : ∀{n A M} → Tm (n + 1) (A ∋ M) → Tm n A
    reify   : ∀{n A} → (M : Tm n A) → Tm (n + 1) (A ∋ M)

    app : ∀{n A B} → Tm n (A ⊃ B) → Tm n A → Tm n B
    --fun : ∀{n A B} → ???

⊤ : ∀{n} → Ty n
⊤ = ⊥ ⊃ ⊥

¬_ : ∀{n} → Ty n → Ty n
¬ A = A ⊃ ⊥

_⊃⊂_ : ∀{n} → Ty n → Ty n → Ty n
A ⊃⊂ B = A ⊃ B ∧ B ⊃ A

{-
A is a type₀
M₁ is a term₀ of type₀ A

A ∋ M₁ is a type₁
M₂ is a term₁ of type₁ A ∋ M₁

A ∋ M₁ ∋ M₂ is a type₂
M₃ is a term₂ of type₂ A ∋ M₁ ∋ M₂
-}

module Example where
  A : Ty 0
  A = ⊤

  postulate
    M₁ : Tm 0 A

  M₂ : Tm 1 (A ∋ M₁)
  M₂ = reify M₁
  
  M₃ : Tm 2 (A ∋ M₁ ∋ M₂)
  M₃ = reify M₂

  M₂' : Tm 1 (A ∋ M₁)
  M₂' = reflect M₃

  M₁' : Tm 0 A
  M₁' = reflect M₂'

{-
fun₁ binds a term₀ of type₀ A
fun₂ binds a term₁ of type₁ A ∋ M₁
fun₃ binds a term₂ of type₂ A ∋ M₁ ∋ M₂

TODO
-}
