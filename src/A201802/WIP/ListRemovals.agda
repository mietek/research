{-# OPTIONS --rewriting #-}

module A201802.WIP.ListRemovals where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas


--------------------------------------------------------------------------------


-- McBride's context removals

_-_ : ∀ {X A} → (Ξ : List X) → Ξ ∋ A → List X
∙       - ()
(Ξ , A) - zero  = Ξ
(Ξ , B) - suc i = (Ξ - i) , B

del⊇ : ∀ {X A} → {Ξ : List X}
               → (i : Ξ ∋ A)
               → Ξ ⊇ Ξ - i
del⊇ zero    = drop id
del⊇ (suc i) = keep (del⊇ i)


-- McBride's removal-based variable equality

data _≡∋_ {X} : ∀ {A B} → {Ξ : List X} → Ξ ∋ A → Ξ ∋ B → Set
  where
    same : ∀ {A} → {Ξ : List X}
                 → (i : Ξ ∋ A)
                 → i ≡∋ i

    diff : ∀ {A B} → {Ξ : List X}
                   → (i : Ξ ∋ A) (j : Ξ - i ∋ B)
                   → i ≡∋ ren∋ (del⊇ i) j

_≟∋_ : ∀ {X A B} → {Ξ : List X}
                 → (i : Ξ ∋ A) (j : Ξ ∋ B)
                 → i ≡∋ j
zero  ≟∋ zero   = same zero
zero  ≟∋ suc j  rewrite id-ren∋ j ⁻¹ = diff zero j
suc i ≟∋ zero   = diff (suc i) zero
suc i ≟∋ suc j  with i ≟∋ j
suc i ≟∋ suc .i | same .i = same (suc i)
suc i ≟∋ suc ._ | diff .i j = diff (suc i) (suc j)


--------------------------------------------------------------------------------
