module Prelude where

open import Agda.Builtin.Equality public
  using (_≡_ ; refl)

open import Agda.Builtin.List public
  using (List ; [] ; _∷_)

open import Agda.Builtin.Nat public
  using (zero ; suc)
  renaming (Nat to ℕ)

open import Agda.Builtin.Sigma public
  using (Σ ; _,_ ; fst ; snd)

open import Agda.Builtin.Unit public
  using ()
  renaming (⊤ to 𝟙 ; tt to unit)

open import Agda.Primitive public
  using (Level ; _⊔_ ; lzero ; lsuc ; Setω)


----------------------------------------------------------------------------------------------------

id : ∀ {𝓍} {X : Set 𝓍} → X → X
id x = x

infixr -1 _$_
_$_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} → (∀ x → Y x) → (∀ x → Y x)
f $ x = f x

flip : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : X → Y → Set 𝓏} → (∀ x y → Z x y) →
       (∀ y x → Z x y)
(flip f) y x = f x y

infixr 9 _∘_
_∘_ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : X → Set 𝓎} {Z : ∀ {x} → Y x → Set 𝓏} →
        (∀ {x} (y : Y x) → Z y) → (g : ∀ x → Y x) →
      (∀ x → Z (g x))
(f ∘ g) x = f (g x)

infixr 9 _⨾_
_⨾_ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : X → Set 𝓎} {Z : ∀ {x} → Y x → Set 𝓏} (g : ∀ x → Y x) →
        (∀ {x} (y : Y x) → Z y) →
      (∀ x → Z (g x))
(g ⨾ f) x = f (g x)

infixr 2 _×_
_×_ : ∀ {𝓍 𝓎} (X : Set 𝓍) (Y : Set 𝓎) → Set (𝓍 ⊔ 𝓎)
X × Y = Σ X λ _ → Y

infixr 1 _⊎_
data _⊎_ {𝓍 𝓎} (X : Set 𝓍) (Y : Set 𝓎) : Set (𝓍 ⊔ 𝓎) where
  left  : ∀ (x : X) → X ⊎ Y
  right : ∀ (y : Y) → X ⊎ Y

recℕ : ∀ {𝓍} {X : Set 𝓍} → ℕ → X → (ℕ → X → X) → X
recℕ zero    z s = z
recℕ (suc n) z s = s n (recℕ n z s)

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
  yes : X → Dec X
  no  : ¬ X → Dec X


----------------------------------------------------------------------------------------------------

infix 4 ≡-syntax
≡-syntax : ∀ {𝓍} (X : Set 𝓍) (x x′ : X) → Set 𝓍
≡-syntax X = _≡_

syntax ≡-syntax X x x′ = x ≡ x′ :> X

sym : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} → x ≡ x′ → x′ ≡ x
sym refl = refl

infix 9 _⁻¹
_⁻¹ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} → x ≡ x′ → x′ ≡ x
_⁻¹ = sym

trans : ∀ {𝓍} {X : Set 𝓍} {x x′ x″ : X} → x ≡ x′ → x′ ≡ x″ → x ≡ x″
trans refl eq = eq

infixr 4 _⋮_
_⋮_ : ∀ {𝓍} {X : Set 𝓍} {x x′ x″ : X} → x ≡ x′ → x′ ≡ x″ → x ≡ x″
_⋮_ = trans

subst : ∀ {𝓍 𝓎} {X : Set 𝓍} (Y : X → Set 𝓎) {x x′} → x ≡ x′ → Y x → Y x′
subst Y refl y = y

coe : ∀ {𝓍} {X Y : Set 𝓍} → X ≡ Y → X → Y
coe = subst id

cong : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (f : X → Y) {x x′} → x ≡ x′ → f x ≡ f x′
cong f refl = refl

infixl 9 _&_
_&_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (f : X → Y) {x x′} → x ≡ x′ → f x ≡ f x′
_&_ = cong

cong₂ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : Set 𝓏} (f : X → Y → Z) {x x′ y y′} → x ≡ x′ →
          y ≡ y′ →
        f x y ≡ f x′ y′
cong₂ f refl refl = refl

infixl 8 _⊗_
_⊗_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {f g : X → Y} {x x′} → f ≡ g → x ≡ x′ → f x ≡ g x′
refl ⊗ refl = refl

congapp : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} {f g : ∀ x → Y x} → f ≡ g → (∀ x → f x ≡ g x)
congapp refl x = refl

congapp′ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} {f g : ∀ {x} → Y x} →
             f ≡ g :> (∀ {x} → Y x) →
           (∀ {x} → f {x} ≡ g {x})
congapp′ refl {x} = refl

FunExt : Setω
FunExt = ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} {f g : ∀ x → Y x} → (∀ x → f x ≡ g x) → f ≡ g

FunExt′ : Setω
FunExt′ = ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} {f g : ∀ {x} → Y x} →
            (∀ {x} → f {x} ≡ g {x}) →
          f ≡ g :> (∀ {x} → Y x)

uni≡ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} (eq eq′ : x ≡ x′) → eq ≡ eq′
uni≡ refl refl = refl

uni𝟘 : ∀ (z z′ : 𝟘) → z ≡ z′
uni𝟘 () ()

uni¬ : ∀ {𝓍} {X : Set 𝓍} (f g : ¬ X) → f ≡ g
uni¬ f g = refl

module _ (⚠ : FunExt) where
  implify : FunExt′
  implify eq = (λ f {x} → f x) & ⚠ (λ x → eq {x})

  uni→ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (uniY : ∀ y y′ → y ≡ y′) (f g : X → Y) → f ≡ g
  uni→ uniY f g = ⚠ λ x → uniY (f x) (g x)

module ≡-Reasoning {𝓍} {X : Set 𝓍} where
  infix 1 begin_
  begin_ : ∀ {x x′ : X} → x ≡ x′ → x ≡ x′
  begin_ eq = eq

  infixr 2 _≡⟨⟩_
  _≡⟨⟩_ : ∀ (x {x′} : X) → x ≡ x′ → x ≡ x′
  x ≡⟨⟩ eq = eq

  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ : ∀ (x {x′ x″} : X) → x ≡ x′ → x′ ≡ x″ → x ≡ x″
  x ≡⟨ eq ⟩ eq′ = trans eq eq′

  infixr 2 _≡˘⟨_⟩_
  _≡˘⟨_⟩_ : ∀ (x {x′ x″} : X) → x′ ≡ x → x′ ≡ x″ → x ≡ x″
  x ≡˘⟨ eq ⟩ eq′ = trans (sym eq) eq′

  infix  3 _∎
  _∎ : ∀ (x : X) → x ≡ x
  _∎ _ = refl


----------------------------------------------------------------------------------------------------

infix 4 _≅_
data _≅_ {𝓍} {X : Set 𝓍} (x : X) : ∀ {𝓎} {Y : Set 𝓎} → Y → Set 𝓍 where
   refl : x ≅ x

≅→≡ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} → x ≅ x′ → x ≡ x′
≅→≡ refl = refl

≡→≅ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} → x ≡ x′ → x ≅ x′
≡→≅ refl = refl

cong≅ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} (f : ∀ x → Y x) {x x′} → x ≅ x′ → f x ≅ f x′
cong≅ f refl = refl

cong₂≅ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : X → Set 𝓎} {Z : ∀ x → Y x → Set 𝓏}
           (f : ∀ x → (y : Y x) → Z x y) {x x′ y y′} → x ≅ x′ → y ≅ y′ →
         f x y ≅ f x′ y′
cong₂≅ f refl refl = refl


----------------------------------------------------------------------------------------------------
