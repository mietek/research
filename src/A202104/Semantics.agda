module A202104.Semantics where

open import A202103.Prelude

------------------------------------------------------------------------------

record Model : Set₁ where
  field
    World          : Set
    _≤_            : World → World → Set
    refl≤          : ∀ {w} → w ≤ w
    trans≤         : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″
    _R_            : World → World → Set
    reflR          : ∀ {w} → w R w
    transR         : ∀ {w w′ w″} → w R w′ → w′ R w″ → w R w″
    _⊩_atomTrue   : World → Atom → Set
    mono≤-atomTrue : ∀ {w w′ P} → w ≤ w′ → w ⊩ P atomTrue → w′ ⊩ P atomTrue
    ≤→R           : ∀ {w w′} → w ≤ w′ → w R w′

open Model {{...}} public

{-# DISPLAY Model.World M = World #-}
{-# DISPLAY Model._≤_ M w w′ = w ≤ w′ #-}
{-# DISPLAY Model.refl≤ M = refl≤ #-}
{-# DISPLAY Model.trans≤ M η η′ = trans≤ η η′ #-}
{-# DISPLAY Model._R_ M w w′ = w R w′ #-}
{-# DISPLAY Model.reflR M = reflR #-}
{-# DISPLAY Model.transR M η η′ = transR η η′ #-}
{-# DISPLAY Model._⊩_atomTrue M w P = w ⊩ P atomTrue #-}
{-# DISPLAY Model.mono≤-atomTrue M η p = mono≤-atomTrue η p #-}
{-# DISPLAY Model.≤→R M η = ≤→R η #-}

------------------------------------------------------------------------------
