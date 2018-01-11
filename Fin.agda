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
id≥ {suc I} = keep id≥


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


REN∋ : ∀ {n n′} → n′ ≥ n → Fin n
                → Fin n′
REN∋ done     I       = I
REN∋ (drop e) I       = suc (REN∋ e I)
REN∋ (keep e) zero    = zero
REN∋ (keep e) (suc I) = suc (REN∋ e I)


--------------------------------------------------------------------------------
