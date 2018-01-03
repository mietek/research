{-# OPTIONS --rewriting #-}

module Fin where

open import Prelude


-- _∋⋆_ / _⊇_
infix 4 _≥_
data _≥_ : Nat → Nat → Set
  where
    done : zero ≥ zero

    -- wkᵣ
    drop : ∀ {n n′} → n′ ≥ n
                    → suc n′ ≥ n

    -- liftᵣ
    keep : ∀ {n n′} → n′ ≥ n
                    → suc n′ ≥ suc n


bot≥ : ∀ {n} → n ≥ zero
bot≥ {zero}  = done
bot≥ {suc n} = drop bot≥

-- idᵣ
id≥ : ∀ {n} → n ≥ n
id≥ {zero}  = done
id≥ {suc n} = keep id≥

-- _○_ / getᵣ⋆
_∘≥_ : ∀ {n n′ n″} → n′ ≥ n → n″ ≥ n′
                   → n″ ≥ n
e₁      ∘≥ done    = e₁
e₁      ∘≥ drop e₂ = drop (e₁ ∘≥ e₂)
drop e₁ ∘≥ keep e₂ = drop (e₁ ∘≥ e₂)
keep e₁ ∘≥ keep e₂ = keep (e₁ ∘≥ e₂)

undrop≥ : ∀ {n n′} → n′ ≥ suc n
                   → n′ ≥ n
undrop≥ (drop e) = drop (undrop≥ e)
undrop≥ (keep e) = drop e

unkeep≥ : ∀ {n n′} → suc n′ ≥ suc n
                   → n′ ≥ n
unkeep≥ (drop e) = undrop≥ e
unkeep≥ (keep e) = e


-- lid○
lid∘≥ : ∀ {n n′} → (e : n′ ≥ n)
                 → id≥ ∘≥ e ≡ e
lid∘≥ done     = refl
lid∘≥ (drop e) = drop & lid∘≥ e
lid∘≥ (keep e) = keep & lid∘≥ e
-- {-# REWRITE lid∘≥ #-}

-- rid○
rid∘≥ : ∀ {n n′} → (e : n′ ≥ n)
                 → e ∘≥ id≥ ≡ e
rid∘≥ done     = refl
rid∘≥ (drop e) = drop & rid∘≥ e
rid∘≥ (keep e) = keep & rid∘≥ e
-- {-# REWRITE rid∘≥ #-}

-- assoc○
assoc∘≥ : ∀ {n n′ n″ n‴} → (e₁ : n′ ≥ n) (e₂ : n″ ≥ n′) (e₃ : n‴ ≥ n″)
                         → e₁ ∘≥ (e₂ ∘≥ e₃) ≡ (e₁ ∘≥ e₂) ∘≥ e₃
assoc∘≥ e₁        e₂        done      = refl
assoc∘≥ e₁        e₂        (drop e₃) = drop & assoc∘≥ e₁ e₂ e₃
assoc∘≥ e₁        (drop e₂) (keep e₃) = drop & assoc∘≥ e₁ e₂ e₃
assoc∘≥ (drop e₁) (keep e₂) (keep e₃) = drop & assoc∘≥ e₁ e₂ e₃
assoc∘≥ (keep e₁) (keep e₂) (keep e₃) = keep & assoc∘≥ e₁ e₂ e₃
-- {-# REWRITE assoc∘≥ #-}


-- _∋_
data Fin : Nat → Set
  where
    zero : ∀ {n} → Fin (suc n)

    suc : ∀ {n} → Fin n
                → Fin (suc n)

-- getᵣ
renFin : ∀ {n n′} → n′ ≥ n → Fin n
                  → Fin n′
renFin done     i       = i
renFin (drop e) i       = suc (renFin e i)
renFin (keep e) zero    = zero
renFin (keep e) (suc i) = suc (renFin e i)


-- idgetᵣ
idrenFin : ∀ {n} → (i : Fin n)
                 → renFin id≥ i ≡ i
idrenFin zero    = refl
idrenFin (suc i) = suc & idrenFin i
-- {-# REWRITE idrenFin #-}

-- get○
assocrenFin : ∀ {n n′ n″} → (e₁ : n′ ≥ n) (e₂ : n″ ≥ n′) (i : Fin n)
                          → renFin e₂ (renFin e₁ i) ≡ renFin (e₁ ∘≥ e₂) i
assocrenFin e₁        done      i       = refl
assocrenFin e₁        (drop e₂) i       = suc & assocrenFin e₁ e₂ i
assocrenFin (drop e₁) (keep e₂) i       = suc & assocrenFin e₁ e₂ i
assocrenFin (keep e₁) (keep e₂) zero    = refl
assocrenFin (keep e₁) (keep e₂) (suc i) = suc & assocrenFin e₁ e₂ i
-- {-# REWRITE assocrenFin #-}
