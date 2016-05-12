module Numbered where

open import Data.Nat using (ℕ ; zero ; suc ; pred ; _⊔_ )

module SucNoLub where
  data Tm : ℕ → Set where
    var : (x : ℕ) → Tm (suc x)
    lam : ∀{x} → Tm (suc x) → Tm x
    app : ∀{x} → Tm x → Tm x → Tm x

  -- ∅ ⊢ A ⊃ A
  I : Tm 0
  I = lam (var 0)

  -- A ⊢ A
  I′ : Tm 1
  I′ = var 0

  -- ∅ ⊢ A ⊃ B ⊃ A
  K : Tm 0
  K = lam (lam (var 1))

  -- A ⊢ B ⊃ A
  K′ : Tm 1
  K′ = lam (var 1)

  -- A , B ⊢ A
  K″ : Tm 2
  K″ = var 1

  -- ∅ ⊢ B ⊃ A ⊃ A
  err1 : Tm 0
  err1 = {!lam (lam (var 0))!}

  -- ∅ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  err2 : Tm 0
  err2 = {!lam (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0)))))!}


module PredLub where
  data Tm : ℕ → Set where
    var : (x : ℕ) → Tm (suc x)
    lam : ∀{x} → Tm x → Tm (pred x)
    app : ∀{x y} → Tm x → Tm y → Tm (x ⊔ y)

  -- ∅ ⊢ A ⊃ A
  I : Tm 0
  I = lam (var 0)

  -- A ⊢ A
  I′ : Tm 1
  I′ = var 0

  -- ∅ ⊢ A ⊃ B ⊃ A
  K : Tm 0
  K = lam (lam (var 1))

  -- A ⊢ B ⊃ A
  K′ : Tm 1
  K′ = lam (var 1)

  -- A , B ⊢ A
  K″ : Tm 2
  K″ = var 1

  -- ∅ ⊢ B ⊃ A ⊃ A
  err1 : Tm 0
  err1 = lam (lam (var 0))

  -- ∅ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  err2 : Tm 0
  err2 = lam (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0)))))
