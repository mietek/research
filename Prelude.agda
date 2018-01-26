{-# OPTIONS --rewriting #-}

module Prelude where

open import Agda.Primitive public
  using (Level ; lzero ; lsuc ; _⊔_)

open import Agda.Builtin.Equality public
  using (_≡_ ; refl)

open import Agda.Builtin.FromString public
  using (IsString ; fromString)

open import Agda.Builtin.Nat public
  using (Nat ; zero ; suc)

open import Agda.Builtin.String public
  using (String ; primStringEquality)

open import Agda.Builtin.Unit public
  using (⊤)
  renaming (tt to ∙)


--------------------------------------------------------------------------------


Π : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
Π X Y = X → Y


_∘′_ : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {P : X → Set ℓ′} {Q : ∀ {x} → P x → Set ℓ″}
                   → (f : ∀ {x} → (y : P x) → Q y) (g : ∀ x → P x) (x : X)
                   → Q (g x)
(f ∘′ g) x = f (g x)


flip : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″}
                   → (X → Y → Z) → Y → X
                   → Z
flip f y x = f x y


--------------------------------------------------------------------------------


data ⊥ : Set
  where


elim⊥ : ∀ {ℓ} → {X : Set ℓ} → ⊥ → X
elim⊥ ()


¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ X = X → ⊥


_↯_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} → X → ¬ X → Y
x ↯ f = elim⊥ (f x)


--------------------------------------------------------------------------------


{-# BUILTIN REWRITE _≡_ #-}


infix 4 _≢_
_≢_ : ∀ {ℓ} → {X : Set ℓ} → X → X → Set ℓ
x ≢ x′ = ¬ (x ≡ x′)


_⁻¹≡ : ∀ {ℓ} → {X : Set ℓ} {x y : X} → x ≡ y → y ≡ x
refl ⁻¹≡ = refl


_⋮≡_ : ∀ {ℓ} → {X : Set ℓ} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
refl ⋮≡ refl = refl


--------------------------------------------------------------------------------


record PER {ℓ} (X : Set ℓ) (_≈_ : X → X → Set ℓ) : Set ℓ
  where
    infix 9 _⁻¹
    infixr 4 _⋮_
    field
      _⁻¹ : ∀ {x y} → x ≈ y → y ≈ x
      _⋮_ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

open PER {{...}} public


instance
  per≡ : ∀ {ℓ} {X : Set ℓ} → PER X _≡_
  per≡ = record
           { _⁻¹ = _⁻¹≡
           ; _⋮_ = _⋮≡_
           }


--------------------------------------------------------------------------------


infixl 9 _&_
_&_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {x y : X}
               → (f : X → Y) → x ≡ y
               → f x ≡ f y
f & refl = refl


infixl 8 _⊗_
_⊗_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {f g : X → Y} {x y : X}
               → f ≡ g → x ≡ y
               → f x ≡ g y
refl ⊗ refl = refl


coerce : ∀ {ℓ} → {X Y : Set ℓ}
               → X → X ≡ Y
               → Y
coerce x refl = x


subst : ∀ {ℓ ℓ′} → {X : Set ℓ} {x y : X}
                 → (P : X → Set ℓ′) → x ≡ y → P x
                 → P y
subst P refl p = p


case_of_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
                    → X → (X → Y) → Y
case x of f = f x


postulate
  funext! : ∀ {ℓ ℓ′} → {X : Set ℓ} {P : X → Set ℓ′} {f g : ∀ x → P x}
                     → (∀ x → f x ≡ g x)
                     → f ≡ g

postulate
  funext!′ : ∀ {ℓ ℓ′} → {X : Set ℓ} {P : X → Set ℓ′} {f g : ∀ {x} → P x}
                      → (∀ x → f {x} ≡ g {x})
                      → (\ {x} → f {x}) ≡ (\ {x} → g {x})


--------------------------------------------------------------------------------


module ≡-Reasoning {ℓ} {X : Set ℓ}
  where
    infix 1 begin_
    begin_ : ∀ {x y : X} → x ≡ y → x ≡ y
    begin p = p

    infixr 2 _≡⟨⟩_
    _≡⟨⟩_ : ∀ (x {y} : X) → x ≡ y → x ≡ y
    x ≡⟨⟩ p = p

    infixr 2 _≡⟨_⟩_
    _≡⟨_⟩_ : ∀ (x {y z} : X) → x ≡ y → y ≡ z → x ≡ z
    x ≡⟨ p ⟩ q = p ⋮ q

    infix 3 _∎
    _∎ : ∀ (x : X) → x ≡ x
    x ∎ = refl


--------------------------------------------------------------------------------


module Inspect
  where
    record Reveal_$_is_ {ℓ ℓ′} {X : Set ℓ} {P : X → Set ℓ′}
                               (f : ∀ x → P x) (x : X) (y : P x)
                             : Set (ℓ ⊔ ℓ′)
      where
        constructor [_]
        field
          eq : f x ≡ y


    inspect : ∀ {ℓ ℓ′} → {X : Set ℓ} {P : X → Set ℓ′}
                       → (f : ∀ x → P x) (x : X)
                       → Reveal f $ x is f x
    inspect f x = [ refl ]


--------------------------------------------------------------------------------


data Dec {ℓ} (X : Set ℓ) : Set ℓ
  where
    instance
      yes : X → Dec X
      no  : ¬ X → Dec X


forD : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
                → Dec X → (X → Y) → (Y → X)
                → Dec Y
forD (yes x) f g = yes (f x)
forD (no ¬x) f g = no (\ y → g y ↯ ¬x)


mapD : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
                → (X → Y) → (Y → X) → Dec X
                → Dec Y
mapD f g x = forD x f g


--------------------------------------------------------------------------------


infixl 6 _,_
record Σ {ℓ ℓ′} (X : Set ℓ) (P : X → Set ℓ′) : Set (ℓ ⊔ ℓ′)
  where
    instance
      constructor _,_
    field
      proj₁ : X
      proj₂ : P proj₁

open Σ public


forΣ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} → {X : Set ℓ} {Y : Set ℓ′} {P : X → Set ℓ″} {Q : Y → Set ℓ‴}
                      → Σ X P → (f : X → Y) (g : ∀ {x} → P x → Q (f x))
                      → Σ Y Q
forΣ (x , y) f g = f x , g y


mapΣ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} → {X : Set ℓ} {Y : Set ℓ′} {P : X → Set ℓ″} {Q : Y → Set ℓ‴}
                      → (f : X → Y) (g : ∀ {x} → P x → Q (f x)) → Σ X P
                      → Σ Y Q
mapΣ f g p = forΣ p f g


infixl 2 _×_
_×_ : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
X × Y = Σ X (\ x → Y)


--------------------------------------------------------------------------------


infixl 1 _⊎_
data _⊎_ {ℓ ℓ′} (X : Set ℓ) (Y : Set ℓ′) : Set (ℓ ⊔ ℓ′)
  where
    inj₁ : (x : X) → X ⊎ Y
    inj₂ : (y : Y) → X ⊎ Y


elim⊎ : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″}
                    → X ⊎ Y → (X → Z) → (Y → Z)
                    → Z
elim⊎ (inj₁ x) f g = f x
elim⊎ (inj₂ y) f g = g y


for⊎ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} → {X : Set ℓ} {Y : Set ℓ′} {U : Set ℓ″} {V : Set ℓ‴}
                      → X ⊎ Y → (X → U) → (Y → V)
                      → U ⊎ V
for⊎ s f g = elim⊎ s (\ x → inj₁ (f x)) (\ y → inj₂ (g y))


map⊎ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} → {X : Set ℓ} {Y : Set ℓ′} {U : Set ℓ″} {V : Set ℓ‴}
                      → (X → U) → (Y → V) → X ⊎ Y
                      → U ⊎ V
map⊎ f g s = for⊎ s f g


--------------------------------------------------------------------------------


-- not : Bool → Bool
-- not true  = false
-- not false = true
--
--
-- ⊺ : Bool → Set
-- ⊺ true  = ⊤
-- ⊺ false = ⊥
--
--
-- ⌊_⌋ : ∀ {ℓ} → {X : Set ℓ}
--             → Dec X
--             → Bool
-- ⌊ yes _ ⌋ = true
-- ⌊ no  _ ⌋ = false
--
--
-- True : ∀ {ℓ} → {X : Set ℓ}
--              → Dec X
--              → Set
-- True p = ⊺ ⌊ p ⌋
--
--
-- False : ∀ {ℓ} → {X : Set ℓ}
--               → Dec X
--               → Set
-- False p = ⊺ (not ⌊ p ⌋)


--------------------------------------------------------------------------------


module _
  where
    open import Agda.Builtin.Bool
    open import Agda.Builtin.TrustMe

    _≟ₛ_ : (s₁ s₂ : String) → Dec (s₁ ≡ s₂)
    s₁ ≟ₛ s₂ with primStringEquality s₁ s₂
    ...    | true  = yes primTrustMe
    ...    | false = no s₁≢s₂
      where
        postulate
          s₁≢s₂ : s₁ ≢ s₂


instance
  stringIsString : IsString String
  stringIsString =
    record
      { Constraint = \ s → ⊤
      ; fromString = \ s → s
      }


--------------------------------------------------------------------------------


inj-suc : ∀ {n m} → suc n ≡ suc m
                  → n ≡ m
inj-suc refl = refl


_≟ₙ_ : (n₁ n₂ : Nat) → Dec (n₁ ≡ n₂)
zero   ≟ₙ zero   = yes refl
zero   ≟ₙ suc n₂ = no (\ ())
suc n₁ ≟ₙ zero   = no (\ ())
suc n₁ ≟ₙ suc n₂ with n₁ ≟ₙ n₂
...              | yes refl = yes refl
...              | no n₁≢n₂ = no (n₁≢n₂ ∘′ inj-suc)


--------------------------------------------------------------------------------
