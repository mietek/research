module A202103.List where

open import A202103.Prelude

------------------------------------------------------------------------------

data List {t} (T : Set t) : Set t where
  ·   : List T
  _,_ : List T → T → List T

infix 3 _∋_
data _∋_ {t} {T : Set t} : List T → T → Set where
  top : ∀ {Γ A} → Γ , A ∋ A
  pop : ∀ {Γ A C} → Γ ∋ A → Γ , C ∋ A

------------------------------------------------------------------------------
