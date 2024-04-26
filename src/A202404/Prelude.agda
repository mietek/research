module A202404.Prelude where

open import Agda.Builtin.Equality public
  using (_≡_ ; refl)

open import Agda.Builtin.List
  using (List ; [] ; _∷_)

open import Agda.Builtin.Nat public
  using (zero ; suc ; _+_)
  renaming (Nat to ℕ)

open import Agda.Builtin.Sigma public
  using (Σ ; _,_)

open import Agda.Builtin.String public
  using (String)

open import Agda.Primitive public
  using (_⊔_)


----------------------------------------------------------------------------------------------------

-- mini prelude

id : ∀ {𝓍} {X : Set 𝓍} → X → X
id x = x

subst : ∀ {𝓍 𝓎} {X : Set 𝓍} (Y : X → Set 𝓎) {x x′} → x ≡ x′ → Y x → Y x′
subst Y refl y = y

transport : ∀ {𝓍} {X Y : Set 𝓍} → X ≡ Y → X → Y
transport = subst id

infixl 9 _&_
cong _&_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (f : X → Y) {x x′} → x ≡ x′ → f x ≡ f x′
cong f refl = refl
_&_ = cong

infixr 1 _⊎_
data _⊎_ {𝓍 𝓎} (X : Set 𝓍) (Y : Set 𝓎) : Set (𝓍 ⊔ 𝓎) where
  left  : ∀ (x : X) → X ⊎ Y
  right : ∀ (y : Y) → X ⊎ Y

record Irrelevant {𝓍} (X : Set 𝓍) : Set 𝓍 where
  field .irrelevant : X

open Irrelevant public

private
  data Empty : Set where

𝟘 : Set
𝟘 = Irrelevant Empty

{-# DISPLAY Irrelevant Empty = 𝟘 #-}

abort : ∀ {𝓍} {X : Set 𝓍} → 𝟘 → X
abort ()

infix 3 ¬_
¬_ : ∀ {𝓍} → Set 𝓍 → Set 𝓍
¬ X = X → 𝟘

_↯_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → X → ¬ X → Y
x ↯ ¬x = abort (¬x x)

data Dec {𝓍} (X : Set 𝓍) : Set 𝓍 where
  yes : ∀ (x : X) → Dec X
  no  : ∀ (¬x : ¬ X) → Dec X

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} (i : Fin n) → Fin (suc n)

injsuc : ∀ {n} {k k′ : Fin n} → Fin.suc k ≡ suc k′ → k ≡ k′
injsuc refl = refl


----------------------------------------------------------------------------------------------------
