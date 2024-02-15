----------------------------------------------------------------------------------------------------

-- abstract reduction systems

module ARS {𝓍} {X : Set 𝓍} where

open import Prelude public


----------------------------------------------------------------------------------------------------

-- reflexive and transitive closure
data _* (R : Rel X) : Rel X where
  done : ∀ {x} → (R *) x x
  step : ∀ {x x′ x″} (r : R x x′) (rs : (R *) x′ x″) → (R *) x x″

module _ {R : Rel X} where
  trans* : ∀ {x x′ x″} → (R *) x x′ → (R *) x′ x″ → (R *) x x″
  trans* done        rs′ = rs′
  trans* (step r rs) rs′ = step r (trans* rs rs′)


----------------------------------------------------------------------------------------------------

-- reflexive, transitive, and symmetric closure
data _≈ (R : Rel X) : Rel X where
  done : ∀ {x} → (R ≈) x x
  step : ∀ {x x′ x″} (r : R x x′) (rs : (R ≈) x′ x″) → (R ≈) x x″
  pets : ∀ {x x′ x″} (r : R x′ x) (rs : (R ≈) x′ x″) → (R ≈) x x″

module _ {R : Rel X} where
  trans≈ : ∀ {x x′ x″} → (R ≈) x x′ → (R ≈) x′ x″ → (R ≈) x x″
  trans≈ done        rs′ = rs′
  trans≈ (step r rs) rs′ = step r (trans≈ rs rs′)
  trans≈ (pets r rs) rs′ = pets r (trans≈ rs rs′)

  sym≈ : ∀ {x x′} → (R ≈) x x′ → (R ≈) x′ x
  sym≈ done        = done
  sym≈ (step r rs) = trans≈ (sym≈ rs) (pets r done)
  sym≈ (pets r rs) = trans≈ (sym≈ rs) (step r done)


----------------------------------------------------------------------------------------------------
