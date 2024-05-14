module A201602.Atom where

open import Data.Nat using (ℕ)
open import Relation.Nullary using (¬_ ; yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
import Data.Nat as Nat


data Atom : Set where
  α_ : ℕ → Atom

foo : ∀{n m} → n ≡ m → α n ≡ α m
foo refl = refl

bar : ∀{n m} → α n ≡ α m → n ≡ m
bar refl = refl

baz : ∀{n m} → ¬ n ≡ m → ¬ α n ≡ α m
baz n≢m = λ αn≡αm → contradiction (bar αn≡αm) n≢m

_≟_ : Decidable {A = Atom} _≡_
(α n) ≟ (α m) with n Nat.≟ m
...              | yes n≡m = yes (foo n≡m)
...              | no n≢m  = no (baz n≢m)
