module Common.Core where

open import Data.Product using (Σ ; _×_) renaming (_,_ to _∙_) public
open import Function using (_∘_ ; _$_) public


-- Atoms, for propositional variables.

postulate
  Atom : Set
