module SystemT where


data Bool : Set where
  true : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

if_then_else_ : {X : Set} → Bool → X → X → X
if true then x else y = x
if false then x else y = y

natrec : {X : Set} → X → (Nat → X → X) → Nat → X
natrec p h zero = p
natrec p h (suc n) = h n (natrec p h n)

_+_ : Nat → Nat → Nat
_+_ n m = natrec m (λ x y → suc y) n

_*_ : Nat → Nat → Nat
_*_ n m = natrec zero (λ x y → y + m) n

pred : Nat → Nat
pred n = natrec n (λ x y → x) n

_-_ : Nat → Nat → Nat
_-_ n m = natrec n (λ x y → pred y) m

¬_ : Bool → Bool
¬ b = if b then false else true

_∧_ : Bool → Bool → Bool
a ∧ b = if a then b else false

_∨_ : Bool → Bool → Bool
a ∨ b = if a then true else b

_⊕_ : Bool → Bool → Bool
a ⊕ b = if a then ¬ b else b

booleq? : Bool → Bool → Bool
booleq? a b = if a then a ∧ b else ¬ (a ∧ b)

zero?
