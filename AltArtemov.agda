module AltArtemov where

open import Data.Nat using (ℕ ; _+_ ; zero ; suc)

infixl 3 _∧_
infixr 2 _⊃_
infixl 1 _∋_

mutual
  data Ty : ℕ → Set where
    ⊥   : ∀{n} → Ty n
    _∧_ : ∀{n} → Ty n → Ty n → Ty n
    _⊃_ : ∀{n} → Ty n → Ty n → Ty n
    _∋_ : ∀{Γ n} → (A : Ty n) → Tm Γ n A → Ty (n + 1)
  
  data Cx : Set where
    []  : Cx
    _,_ : ∀{n} → (Γ : Cx) → Ty n → Cx

  data _In_ {n} : Ty n → Cx → Set where
    vz  : ∀{Γ A} → A In (Γ , A)
    vs  : ∀{Γ A m} {B : Ty m} → A In Γ → A In (Γ , B)
    get : ∀{Γ Δ A M} → (_∋_ {Γ = Δ} A M) In Γ → A In Γ

  data Tm (Γ : Cx) : (n : ℕ) → Ty n → Set where
    fst  : ∀{n A B} → Tm Γ n (A ∧ B) → Tm Γ n A
    snd  : ∀{n A B} → Tm Γ n (A ∧ B) → Tm Γ n B
    pair : ∀{n A B} → Tm Γ n A → Tm Γ n B → Tm Γ n (A ∧ B)
  
    app  : ∀{n A B} → Tm Γ n (A ⊃ B) → Tm Γ n A → Tm Γ n B
    fun  : ∀{n A B} → Tm (Γ , A) n B → Tm Γ n (A ⊃ B)
    var  : ∀{n A} → A In Γ → Tm Γ n A
    
    reflect : ∀{Δ n A M}
            → Tm Γ (n + 1) (_∋_ {Γ = Δ} A M)
            → Tm Γ n A
    reify   : ∀{Δ n A}
            → (M : Tm Δ n A)
            → Tm Γ (n + 1) (A ∋ M)

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

  M₂ : Tm Γ 1 (A ∋ M₁)
  M₂ = reify M₁

  M₂'' : Tm (Γ , (A ∋ M₁)) 1 (A ∋ M₁)
  M₂'' = var vz
  
  M₂''' : Tm (Γ , (A ∋ M₁)) 0 A
  M₂''' = var (get vz)

  M₃ : Tm Γ 2 (A ∋ M₁ ∋ M₂)
  M₃ = reify M₂

  M₂' : Tm Γ 1 (A ∋ M₁)
  M₂' = reflect M₃

  M₁' : Tm Γ 0 A
  M₁' = reflect M₂'

module ForAugur where
  p : ∀{Γ n A B} {M : Tm Γ n A} {N : Tm Γ n B}
    → Tm Γ (n + 1) ((A ∋ M) ⊃ (B ∋ N) ⊃ (A ∧ B ∋ pair M N))
  p = fun (fun (reify (pair {!var ?!} {!var ?!})))
  -- Should be:
  --p = fun (fun (reify (pair (var (get (vs vz))) (var (get vz)))))

module Cheating where
  p : ∀{Γ n A B} {M : Tm Γ n A} {N : Tm Γ n B}
    → Tm Γ (n + 1) ((A ∋ M) ⊃ (B ∋ N) ⊃ (A ∧ B ∋ pair M N))
  p {M = M} {N = N} = fun (fun (reify (pair M N)))
  
  p2 : ∀{Γ n A B} {M : Tm Γ n A} {N : Tm Γ n B}
     → Tm Γ (n + 1) (A ∧ B ∋ pair M N)
  p2 {M = M} {N = N} = reify (pair M N)
