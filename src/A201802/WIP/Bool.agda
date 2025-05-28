{-# OPTIONS --rewriting #-}

module A201802.WIP.Bool where

open import A201801.Prelude


--------------------------------------------------------------------------------


open import Agda.Builtin.Bool public
  using (Bool ; true ; false)


not : Bool → Bool
not true  = false
not false = true


and : Bool → Bool → Bool
and true  b = b
and false b = false


⌊_⌋ : ∀ {ℓ} → {X : Set ℓ}
            → Dec X
            → Bool
⌊ yes p ⌋ = true
⌊ no  p ⌋ = false


T : Bool → Set
T true  = ⊤
T false = ⊥


--------------------------------------------------------------------------------
