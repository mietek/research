module Common.Core where

open import Data.Empty using () renaming (⊥ to Empty) public
open import Data.Product using (Σ ; _×_) renaming (_,_ to _∙_ ; proj₁ to π₁_ ; proj₂ to π₂_) public
open import Data.Sum using () renaming (_⊎_ to _+_ ; inj₁ to ι₁_ ; inj₂ to ι₂_) public
open import Data.Unit using () renaming (⊤ to Unit ; tt to τ) public
open import Function using (_∘_ ; _$_) public
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; cong₂) public


-- Atoms, for propositional variables.

postulate
  Atom : Set
