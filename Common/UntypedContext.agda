module A201606.Common.UntypedContext where

open import Data.Fin using (Fin ; zero ; suc) public
open import Data.Nat using (ℕ ; zero ; suc) public
open import Function using (flip) public

open import Data.Nat using (_≤_ ; z≤n ; s≤s)



-- Variables as de Bruijn indices.

`i₀ : ∀ {g} → Fin (suc g)
`i₀ = zero

`i₁ : ∀ {g} → Fin (suc (suc g))
`i₁ = suc `i₀

`i₂ : ∀ {g} → Fin (suc (suc (suc g)))
`i₂ = suc `i₁


-- Renaming and substitution.

`Renᵢ : ℕ → ℕ → Set
`Renᵢ g g′ = Fin g → Fin g′

`Ren : (ℕ → Set) → ℕ → ℕ → Set
`Ren Ξ g g′ = Ξ g → Ξ g′

`Subᵢ : (ℕ → Set) → ℕ → ℕ → Set
`Subᵢ Ξ g g′ = Fin g → Ξ g′

`Sub : (ℕ → Set) → ℕ → ℕ → Set
`Sub Ξ g g′ = Ξ g → Ξ g′

`wk-renᵢ : ∀ {g g′} → `Renᵢ g g′ → `Renᵢ (suc g) (suc g′)
`wk-renᵢ ρ zero    = zero
`wk-renᵢ ρ (suc i) = suc (ρ i)


-- Context removals and variable equality.

_`-ᵢ_ : (g : ℕ) → Fin g → ℕ
zero  `-ᵢ ()
suc g `-ᵢ zero   = g
suc g `-ᵢ suc i = suc (g `-ᵢ i)

`add-var : ∀ {g} → (i : Fin g) → `Renᵢ (g `-ᵢ i) g
`add-var zero    j        = suc j
`add-var (suc i) zero     = zero
`add-var (suc i) (suc j) = suc (`add-var i j)

data _`=ᵢ_ {g} (i : Fin g) : Fin g → Set where
  same : i `=ᵢ i
  diff : (j : Fin (g `-ᵢ i)) → i `=ᵢ `add-var i j

_`≟ᵢ_ : ∀ {g} → (i j : Fin g) → i `=ᵢ j
zero  `≟ᵢ zero   = same
zero  `≟ᵢ suc j  = diff j
suc i `≟ᵢ zero   = diff zero
suc i `≟ᵢ suc j  with i `≟ᵢ j
suc i `≟ᵢ suc .i | same   = same
suc i `≟ᵢ suc ._ | diff j = diff (suc j)


-- Ordering.

`ren-var : ∀ {g g′} → g ≤ g′ → `Renᵢ g g′
`ren-var z≤n     ()
`ren-var (s≤s η) zero    = zero
`ren-var (s≤s η) (suc i) = suc (`ren-var η i)
