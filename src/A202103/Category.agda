module A202103.Category where

import A202103.Prelude
open A202103.Prelude hiding (id ; _∘_)

------------------------------------------------------------------------------

record Category {a r} (A : Set a) (_⇒_ : A → A → Set r)
              : Set (a ⊔ r) where
  field
    id   : ∀ {x : A} → x ⇒ x
    _∘_  : ∀ {x y z : A} → z ⇒ y → y ⇒ x → z ⇒ x
    lid∘ : ∀ {x y : A} (m : y ⇒ x) →
           id ∘ m ≡ m
    rid∘ : ∀ {x y : A} (m : y ⇒ x) →
           m ∘ id ≡ m
    ass∘ : ∀ {x y z α : A} (o : α ⇒ z) (n : z ⇒ y) (m : y ⇒ x) →
           (o ∘ n) ∘ m ≡ o ∘ (n ∘ m)

open Category

SET : (a : Level) → Category (Set a) Π
SET a = record
          { id   = λ x → x
          ; _∘_  = λ n m x → m (n x)
          ; lid∘ = λ m → refl
          ; rid∘ = λ m → refl
          ; ass∘ = λ o n m → refl
          }

SET₀ : Category Set₀ Π
SET₀ = SET lzero

------------------------------------------------------------------------------

record Functor {a b r s} {A : Set a} {B : Set b}
               {_⇒ᴬ_ : A → A → Set r} {_⇒ᴮ_ : B → B → Set s}
               (C : Category A _⇒ᴬ_) (D : Category B _⇒ᴮ_)
               (f : A → B)
             : Set (a ⊔ b ⊔ r ⊔ s) where
  field
    φ     : ∀ {x y : A} → y ⇒ᴬ x → f y ⇒ᴮ f x
    idφ   : ∀ {x : A} →
            φ (C .id {x = x}) ≡ D .id
    compφ : ∀ {x y z : A} (n : z ⇒ᴬ y) (m : y ⇒ᴬ x) →
            φ (C ._∘_ n m) ≡ D ._∘_ (φ n) (φ m)

open Functor

Opposite : ∀ {a r} {A : Set a} {_⇒ᴬ_ : A → A → Set r} →
           Category A _⇒ᴬ_ → Category A (flip _⇒ᴬ_)
Opposite C = record
               { id   = C .id
               ; _∘_  = flip (C ._∘_)
               ; lid∘ = C .rid∘
               ; rid∘ = C .lid∘
               ; ass∘ = λ o n m → C .ass∘ m n o ⁻¹
               }

Presheaf : ∀ {a r p} {A : Set a} {_⇒ᴬ_ : A → A → Set r} →
           Category A _⇒ᴬ_ → (A → Set p) → Set (a ⊔ r ⊔ lsuc p)
Presheaf {p = p} C = Functor (Opposite C) (SET p)

------------------------------------------------------------------------------

record NatTrans {a b r s} {A : Set a} {B : Set b}
                {_⇒ᴬ_ : A → A → Set r} {_⇒ᴮ_ : B → B → Set s}
                {C : Category A _⇒ᴬ_} {D : Category B _⇒ᴮ_}
                {f g : A → B}
                (F : Functor C D f) (G : Functor C D g)
              : Set (a ⊔ b ⊔ r ⊔ s) where
  field
    α    : ∀ {x : A} → f x ⇒ᴮ g x
    natα : ∀ {x y} (m : y ⇒ᴬ x) →
           D ._∘_ (F .φ m) α ≡ D ._∘_ α (G .φ m)

------------------------------------------------------------------------------
