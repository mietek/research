module Common.Core where

open import Data.Empty public
  using ()
  renaming (⊥ to Empty)

open import Data.Product public
  using (Σ ; _×_)
  renaming (_,_ to _∙_ ; proj₁ to π₁_ ; proj₂ to π₂_)

open import Data.Sum public
  using ()
  renaming (_⊎_ to _+_ ; inj₁ to ι₁_ ; inj₂ to ι₂_)

open import Data.Unit public
  using ()
  renaming (⊤ to Unit ; tt to τ)

open import Function public
  using (_∘_ ; _$_)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; refl ; sym ; cong ; cong₂)


-- Atoms, for propositional variables.

postulate
  Atom : Set
