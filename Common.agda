module Common where

import Axiom.Extensionality.Propositional as A

open import Data.List public
  using (List ; [] ; _∷_)

open import Data.Nat public
  using (ℕ ; zero ; suc)

open import Data.Product public
  using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)

open import Data.Sum public
  using (_⊎_ ; inj₁ ; inj₂)

open import Data.Unit public
  using ()
  renaming (⊤ to 𝟙 ; tt to unit)

open import Function public
  using (_∘_ ; _$_ ; flip ; id)

open import Level public
  using (Level ; _⊔_ ; Setω)
  renaming (zero to ℓzero ; suc to ℓsuc)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; refl ; cong ; cong₂ ; cong-app ; subst ; sym ; trans ; module ≡-Reasoning)

open import Relation.Binary.HeterogeneousEquality public
  using (_≅_)
  renaming (≡-to-≅ to ≡→≅ ; ≅-to-≡ to ≅→≡ ; cong to cong≅ ; cong₂ to cong₂≅)


----------------------------------------------------------------------------------------------------

Extensionality : Setω
Extensionality = ∀ {𝓍 𝓎} → A.Extensionality 𝓍 𝓎

Extensionality′ : Setω
Extensionality′ = ∀ {𝓍 𝓎} → A.ExtensionalityImplicit 𝓍 𝓎

implify : Extensionality → Extensionality′
implify ⚠ = A.implicit-extensionality ⚠


----------------------------------------------------------------------------------------------------

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

coe : ∀ {𝓍} {X Y : Set 𝓍} → X ≡ Y → X → Y
coe = subst id

infixl 9 _&_
_&_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (f : X → Y) {x x′ : X} → x ≡ x′ → f x ≡ f x′
_&_ = cong

infixl 8 _⊗_
_⊗_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {f g : X → Y} {x y : X} → f ≡ g → x ≡ y → f x ≡ g y
refl ⊗ refl = refl

infix 9 _⁻¹
_⁻¹ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} → x ≡ x′ → x′ ≡ x
_⁻¹ = sym

infixr 4 _⋮_
_⋮_ : ∀ {𝓍} {X : Set 𝓍} {x x′ x″ : X} → x ≡ x′ → x′ ≡ x″ → x ≡ x″
_⋮_ = trans

cong-app′ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} {f g : ∀ {x : X} → Y x} →
            (λ {x : X} → f {x}) ≡ (λ {x : X} → g {x}) → (∀ {x : X} → f {x} ≡ g {x})
cong-app′ refl {x} = refl


----------------------------------------------------------------------------------------------------

recℕ : ∀ {𝓍} {X : Set 𝓍} → ℕ → X → (ℕ → X → X) → X
recℕ zero    z s = z
recℕ (suc n) z s = s n (recℕ n z s)


----------------------------------------------------------------------------------------------------

uni≡ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} (eq eq′ : x ≡ x′) → eq ≡ eq′
uni≡ refl refl = refl

uni𝟘 : ∀ (z z′ : 𝟘) → z ≡ z′
uni𝟘 () ()

uni¬ : ∀ {𝓍} {X : Set 𝓍} → ∀ (f f′ : ¬ X) → f ≡ f′
uni¬ f f′ = refl

module _ (⚠ : Extensionality) where
  uni→ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → (∀ (y y′ : Y) → y ≡ y′) → ∀ (f f′ : X → Y) → f ≡ f′
  uni→ uniY f f′ = ⚠ λ x → uniY (f x) (f′ x)


----------------------------------------------------------------------------------------------------
