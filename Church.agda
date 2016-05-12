module Church where

open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂ ; _×_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)


module Rank₀ where
  List : Set → Set → Set
  List A B = (A → B → B) → B → B

  nil : ∀{A B} → List A B
  nil = λ f y₀ → y₀

  cons : ∀{A B} → A → List A B → List A B
  cons x xs = λ f y₀ → f x (xs f y₀)

  it : ∀{A B} → List A B → (A → B → B) → B → B
  it xs f y₀ = xs f y₀

  rec : ∀{A B C} → List A (List A C × B) → (A → List A C → B → B) → B → B
  rec xs f y₀ = proj₂ (it xs (λ xᵢ pᵢ → cons xᵢ (proj₁ pᵢ) , f xᵢ (proj₁ pᵢ) (proj₂ pᵢ)) (nil , y₀))

  tail : ∀{A B} → List A (List A B × List A B) → List A B
  tail xs = rec xs (λ xᵢ xsᵢ yᵢ → xsᵢ) nil

  data Empty : Set where
    empty : Empty

  head : ∀{A} → List A (A ⊎ Empty) → A ⊎ Empty
  head xs = it xs (λ xᵢ xsᵢ → inj₁ xᵢ) (inj₂ empty)


module Rank₁ where
  List : Set → Set₁
  List A = ∀{T} → (A → T → T) → T → T

  nil : ∀{A} → List A
  nil = λ f y₀ → y₀

  cons : ∀{A} → A → List A → List A
  cons x xs = λ f y₀ → f x (xs f y₀)

  it : ∀{A B} → List A → (A → B → B) → B → B
  it xs f y₀ = xs f y₀

--  rec : ∀{A B} → List A → (A → List A → B → B) → B → B
--  rec xs f y₀ = proj₂ (it xs (λ xᵢ pᵢ → cons xᵢ {!proj₁ pᵢ!} , f xᵢ {!proj₁ pᵢ!} (proj₂ pᵢ)) ((nil , y₀)))

  rec : ∀{A B} → List A → (A → List A → B → B) → B → B
  rec {A} {B} xs f y₀ = proj₂ (it {A} {{!List A!} × B} xs (λ xᵢ pᵢ → cons xᵢ {!proj₁ pᵢ!} , f xᵢ {!proj₁ pᵢ!} (proj₂ pᵢ)) ((nil , y₀)))


module WTF where
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A


module OMG where
  data Unit : Set where
    unit : Unit
⟨x ∈ X, a ∈ A x⟩ ∈ Σ X (X → A)
  data ListTag : Set where
    nil  : ListTag
    cons : ListTag

--  List : Set → Set
--  List A = Σ ListTag (λ { nil → Unit ; cons → A × List A })


{-module Foo where
  data Unit : Set where
    unit : Unit

  data ListTag : Set where
    nil  : ListTag
    cons : ListTag

  data Mu (F : Set → Set) : Set where
    roll : F (Mu F) → Mu F

  foo : Set → Set → ListTag → Set
  List : Set → Set
  foo A T nil = Unit
  foo A T cons = A × T
  List A = Mu (λ T → Σ ListTag (foo A T))-}


data mΣ {X : Set} (A : X → Set) : Set where
     _,_ : (x₀ : X) → A x₀ → mΣ A
