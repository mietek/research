---------------------------------------------------------------------------------------------------------------

module A201901.Chapter6 where

open import Data.Fin
  using (Fin ; suc ; zero)

open import A201901.Prelude public

import A201901.Chapter3
import A201901.Chapter5
open A201901.Chapter5 using () renaming (module Functions to Named)
open Named using (fv)


---------------------------------------------------------------------------------------------------------------
--
-- 6. Nameless representations of terms


---------------------------------------------------------------------------------------------------------------
--
-- 6.1. Terms and contexts
--
--
-- 6.1.1. Exercise [⋆]
-- “For each of the following combinators … write down the corresponding nameless terms.”
-- (skipped)


---------------------------------------------------------------------------------------------------------------
--
-- 6.1.2. Definition [Terms]
-- “Let `T` be the smallest family of sets `{T₀, T₁, T₂, …}` such that …”

module Nameless
  where
    infixl 7 _$_
    data Term : Nat → Set₀ where
      ν   : ∀ {n} → (k : Fin n) → Term n
      ƛ_  : ∀ {n} → (t : Term (suc n)) → Term n
      _$_ : ∀ {n} → (t₁ t₂ : Term n) → Term n


---------------------------------------------------------------------------------------------------------------
--
-- 6.1.3. Definition
-- “Suppose `x₀` through `xₙ` are variable names from `V`.  The naming context `Γ = xₙ, xₙ₋₁, …, x₁, x₀`
-- assigns to each `xᵢ` the de Bruijn index `i`.  …  We write `dom(Γ)` for the set `{xₙ, …, x₀}` of variable
-- names mentioned in `Γ`.”

dom : UniqueList Name → UniqueList Name
dom Γ = Γ


---------------------------------------------------------------------------------------------------------------
--
-- 6.1.4. Exercise [⋆⋆⋆ ↛]
-- “Give an alternative construction of the sets of `n`-terms in the style of Definition 3.2.3, and show (as we
-- did in Proposition 3.2.6) that it is equivalent to the one above.”
-- (skipped)


---------------------------------------------------------------------------------------------------------------
--
-- 6.1.5. Exercise [Recommended, ⋆⋆⋆]
-- “1. Define a function `removeNames(Γ, t)` that takes a naming context `Γ` and an ordinary term `t` (with
-- `fv(t) ⊆ dom(Γ)`) and yields the corresponding nameless term.
-- 2. Define a function `restoreNames(Γ, t)` that takes a nameless term `t` and a naming context `Γ` and
-- produces an ordinary term. …”

module Exercise615
  where
    open Nameless
    open Named

    -- TODO: unfinished

    -- find : ∀ {a} {A : Set a} → UniqueList A → A → ...

    -- removeNames : ∀ (Γ : UniqueList Name) (t : Named.Term) → T (fv t ⊆ dom Γ) → Nameless.Term (length (fv t))
    -- removeNames Γ (ν x)     p = {!!}
    -- removeNames Γ (ƛ x ∙ t) p = {!!}
    -- removeNames Γ (t₁ $ t₂) p = {!!}
