{-

Possibly related to:

- Conor McBride (2011) “Ornamental algebras, algebraic ornaments”
  https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/Ornament.pdf

- Pierre-Evariste Dagand, Conor McBride (2012) “Transporting functions across ornaments”
  http://arxiv.org/abs/1201.4801

With thanks to Darryl McAdams.

-}

module Ornaments where

open import Data.Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
open import Data.Nat using (ℕ ; zero ; suc)


forget : ∀{n} → Fin n → ℕ
forget fzero    = zero
forget (fsuc n) = suc (forget n)


-- We index each Fin by its forgetful mapping:

data _≪_ : ℕ → ℕ → Set where
  ≪-zero : ∀{n} → forget (fzero {n}) ≪ suc n
  ≪-suc : ∀{m n} {i : Fin m} {j : Fin n} → m ≪ n → forget (fsuc i) ≪ forget (fsuc j)


-- Then, we simplify the mapping away:

data _<_ : ℕ → ℕ → Set where
  <-zero : ∀{n} → zero < suc n
  <-suc : ∀{m n} → m < n → suc m < suc n
