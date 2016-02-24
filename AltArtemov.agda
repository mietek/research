module AltArtemov where

open import Data.Nat using ( ℕ ; _+_ ; zero ; suc )

infixl 3 _∧_
infixr 2 _⊃_
infixl 1 _⊢_∋_

mutual
  data Ty : ℕ → Set where
    ⊥     : ∀{n} → Ty n
    _∧_   : ∀{n} → Ty n → Ty n → Ty n
    _⊃_   : ∀{n} → Ty n → Ty n → Ty n
    _⊢_∋_ : ∀{n} → (Γ : Cx) → (A : Ty n) → Tm Γ n A → Ty (n + 1)
  
  data Cx : Set where
    ∅   : Cx
    _,_ : ∀{n} → (Γ : Cx) → Ty n → Cx

  data _In_ {n} (A : Ty n) : Cx → Set where
    vz : ∀{Γ} → A In (Γ , A)
    vs : ∀{Γ m} {B : Ty m} → A In Γ → A In (Γ , B)

  data Tm (Γ : Cx) : (n : ℕ) → Ty n → Set where
    fst  : ∀{n A B} → Tm Γ n (A ∧ B) → Tm Γ n A
    snd  : ∀{n A B} → Tm Γ n (A ∧ B) → Tm Γ n B
    pair : ∀{n A B} → Tm Γ n A → Tm Γ n B → Tm Γ n (A ∧ B)
  
    app : ∀{n A B} → Tm Γ n (A ⊃ B) → Tm Γ n A → Tm Γ n B
    fun : ∀{n A B} → Tm (Γ , A) n B → Tm Γ n (A ⊃ B)
    var : ∀{n A} → A In Γ → Tm Γ n A
  
    reflect : ∀{n A M}
            → Tm Γ (n + 1) (Γ ⊢ A ∋ M)
            → Tm Γ n A
    reify   : ∀{n A}
            → (M : Tm Γ n A)
            → Tm Γ (n + 1) (Γ ⊢ A ∋ M)

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

module Dummy (Γ : Cx) where
  A : Ty 0
  A = ⊤

  M₁ : Tm Γ 0 ⊤
  M₁ = fun (var vz)

  M₂ : Tm Γ 1 (Γ ⊢ A ∋ M₁)
  M₂ = reify M₁
  
  M₃ : Tm Γ 2 (Γ ⊢ (Γ ⊢ A ∋ M₁) ∋ M₂)
  M₃ = reify M₂

  M₂' : Tm Γ 1 (Γ ⊢ A ∋ M₁)
  M₂' = reflect M₃

  M₁' : Tm Γ 0 A
  M₁' = reflect M₂'

module ForAugur where
  p : ∀{Γ n A B} {M : Tm Γ n A} {N : Tm Γ n B}
    → Tm Γ (n + 1) ((Γ ⊢ A ∋ M) ⊃ (Γ ⊢ B ∋ N) ⊃ (Γ ⊢ A ∧ B ∋ pair M N))
  p = fun (fun {!?!})
