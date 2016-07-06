module Common.Core where

open import Data.Empty public
  using (⊥)

open import Data.Product public
  using (Σ ; _×_ ; proj₁ ; proj₂)
  renaming (_,_ to _∙_)

open import Data.Sum public
  using (_⊎_ ; inj₁ ; inj₂)

open import Data.Unit public
  using (⊤ ; tt)

open import Function public
  using (_∘_ ; _$_)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; refl ; sym ; cong ; cong₂)


-- Atoms, for propositional variables.

postulate
  Atom : Set
