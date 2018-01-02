module Fin where

open import Prelude


infix 4 _≥_
data _≥_ : Nat → Nat → Set
  where
    done : zero ≥ zero

    drop : ∀ {n n′} → n′ ≥ n
                    → suc n′ ≥ n

    keep : ∀ {n n′} → n′ ≥ n
                    → suc n′ ≥ suc n


bot≥ : ∀ {n} → n ≥ zero
bot≥ {zero}  = done
bot≥ {suc n} = drop bot≥

id≥ : ∀ {n} → n ≥ n
id≥ {zero}  = done
id≥ {suc n} = keep id≥

_∘≥_ : ∀ {n n′ n″} → n′ ≥ n → n″ ≥ n′
                   → n″ ≥ n
e₁      ∘≥ done    = e₁
e₁      ∘≥ drop e₂ = drop (e₁ ∘≥ e₂)
drop e₁ ∘≥ keep e₂ = drop (e₁ ∘≥ e₂)
keep e₁ ∘≥ keep e₂ = keep (e₁ ∘≥ e₂)

rid∘≥ : ∀ {n n′} → (e : n′ ≥ n)
                 → e ∘≥ id≥ ≡ e
rid∘≥ done     = refl
rid∘≥ (drop e) = drop & rid∘≥ e
rid∘≥ (keep e) = keep & rid∘≥ e


data Fin : Nat → Set
  where
    zero : ∀ {n} → Fin (suc n)

    suc : ∀ {n} → Fin n
                → Fin (suc n)

renFin : ∀ {n n′} → n′ ≥ n → Fin n
                  → Fin n′
renFin done     i       = i
renFin (drop e) i       = suc (renFin e i)
renFin (keep e) zero    = zero
renFin (keep e) (suc i) = suc (renFin e i)

idrenFin : ∀ {n} → (i : Fin n)
                 → renFin id≥ i ≡ i
idrenFin zero    = refl
idrenFin (suc i) = suc & idrenFin i

assocrenFin : ∀ {n n′ n″} → (e₁ : n′ ≥ n) (e₂ : n″ ≥ n′) (i : Fin n)
                          → renFin e₂ (renFin e₁ i) ≡ renFin (e₁ ∘≥ e₂) i
assocrenFin e₁        done      i       = refl
assocrenFin e₁        (drop e₂) i       = suc & assocrenFin e₁ e₂ i
assocrenFin (drop e₁) (keep e₂) i       = suc & assocrenFin e₁ e₂ i
assocrenFin (keep e₁) (keep e₂) zero    = refl
assocrenFin (keep e₁) (keep e₂) (suc i) = suc & assocrenFin e₁ e₂ i
