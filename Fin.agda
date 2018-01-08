module Fin where

open import Prelude


--------------------------------------------------------------------------------


infix 4 _≥_
data _≥_ : Nat → Nat → Set
  where
    done : zero ≥ zero

    drop : ∀ {n n′} → n′ ≥ n
                    → suc n′ ≥ n

    keep : ∀ {n n′} → n′ ≥ n
                    → suc n′ ≥ suc n


id≥ : ∀ {n} → n ≥ n
id≥ {zero}  = done
id≥ {suc i} = keep id≥


_∘≥_ : ∀ {n n′ n″} → n′ ≥ n → n″ ≥ n′
                   → n″ ≥ n
e₁      ∘≥ done    = e₁
e₁      ∘≥ drop e₂ = drop (e₁ ∘≥ e₂)
drop e₁ ∘≥ keep e₂ = drop (e₁ ∘≥ e₂)
keep e₁ ∘≥ keep e₂ = keep (e₁ ∘≥ e₂)


--------------------------------------------------------------------------------


data Fin : Nat → Set
  where
    zero : ∀ {n} → Fin (suc n)

    suc : ∀ {n} → Fin n
                → Fin (suc n)


renF : ∀ {n n′} → n′ ≥ n → Fin n
                → Fin n′
renF done     i       = i
renF (drop e) i       = suc (renF e i)
renF (keep e) zero    = zero
renF (keep e) (suc i) = suc (renF e i)


--------------------------------------------------------------------------------
