module A201802.WIP.Name where

open import A201801.Prelude
open import A201801.Category

open import A201802.WIP.Bool


--------------------------------------------------------------------------------


data Name : Set
  where
    name : Nat → Name


inj-name : ∀ {n m} → name n ≡ name m
                   → n ≡ m
inj-name refl = refl


_≟_ : (x y : Name) → Dec (x ≡ y)
name n ≟ name m  with n ≟ₙ m
name n ≟ name .n | yes refl = yes refl
name n ≟ name m  | no n≢m   = no (n≢m ∘ inj-name)


_≠_ : Name → Name → Bool
x ≠ y = not ⌊ x ≟ y ⌋


--------------------------------------------------------------------------------


≢→≠ : ∀ {x y} → x ≢ y → T (x ≠ y)
≢→≠ {x} {y}  x≢y with x ≟ y
≢→≠ {x} {.x} x≢x | yes refl = refl ↯ x≢x
≢→≠ {x} {y}  x≢y | no _     = ∙


lem-and₁ : ∀ {b} → {{_ : T b}}
                 → T (and b true)
lem-and₁ {false} {{φ}} = φ
lem-and₁ {true}  {{φ}} = φ


lem-and₂ : ∀ {b} x y → {{_ : T (and (x ≠ y) b)}}
                     → T b
lem-and₂ x y  {{φ}} with x ≟ y
lem-and₂ x .x {{φ}} | yes refl = elim⊥ φ
lem-and₂ x y  {{φ}} | no x≢y   = φ


lem-and₃ : ∀ {b} x → ¬ (T (and (x ≠ x) b))
lem-and₃ x φ with x ≟ x
lem-and₃ x φ | yes refl = φ
lem-and₃ x φ | no x≢x   = refl ↯ x≢x


lem-and₄ : ∀ {b} x y → {{_ : T (and (x ≠ y) b)}}
                     → T (x ≠ y)
lem-and₄ x y  {{φ}} with x ≟ y
lem-and₄ x .x {{φ}} | yes refl = φ
lem-and₄ x y  {{φ}} | no x≢y   = ∙


lem-and₅ : ∀ {b} x y → {{_ : T (x ≠ y)}} {{_ : T b}}
                     → T (and (x ≠ y) b)
lem-and₅ x y {{φ₁}} {{φ₂}} with x ≟ y
lem-and₅ x y {{()}} {{φ₂}} | yes refl
lem-and₅ x y {{φ₁}} {{φ₂}} | no x≢y   = φ₂


--------------------------------------------------------------------------------
