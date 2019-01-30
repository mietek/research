-- Linear space usage; no trouble with instance resolution

module Prelude-UniqueList where

open import Data.Bool using (_∧_ ; Bool ; T ; false ; not ; true)
open import Data.Nat using (_+_ ; ℕ)
open import Data.Unit using (tt)
open import Level using (_⊔_)
open import Relation.Binary using (DecSetoid)
open import Relation.Nullary using (¬_ ; Dec ; no ; yes)
open import Relation.Nullary.Decidable using (⌊_⌋)


-- For working with propositions under T
module _ where
  T-Decidable : ∀ {a b} {A : Set a} {B : Set b} → (A → B → Bool) → Set (a ⊔ b)
  T-Decidable _∼_ = ∀ x y → Dec (T (x ∼ y))

  T-decide : ∀ {p} → Dec (T p)
  T-decide {true}  = yes tt
  T-decide {false} = no λ ()

  T-pair : ∀ {p q} → T p → T q → T (p ∧ q)
  T-pair {true}  tt T[q] = T[q]
  T-pair {false} () T[q]

  T-fst : ∀ {p q} → T (p ∧ q) → T p
  T-fst {true}  T[q] = tt
  T-fst {false} ()

  T-snd : ∀ {p q} → T (p ∧ q) → T q
  T-snd {true}  T[q] = T[q]
  T-snd {false} ()


module MakeUniqueList {c ℓ} (DS : DecSetoid c ℓ) where
  open DecSetoid DS using (Carrier ; _≟_)

  mutual
    infixr 5 _∷_
    data UniqueList : Set c where
      []  : UniqueList
      _∷_ : (x : Carrier) (xs : UniqueList) {{_ : T (xs ∌ x)}} → UniqueList

    infix 4 _≠_
    _≠_ : Carrier → Carrier → Bool
    x ≠ y = not ⌊ x ≟ y ⌋

    infix 4 _∌_
    _∌_ : UniqueList → Carrier → Bool
    []       ∌ y = true
    (x ∷ xs) ∌ y = (x ≠ y) ∧ (xs ∌ y)


  [_] : Carrier → UniqueList
  [ x ] = x ∷ []

  length : UniqueList → ℕ
  length []       = 0
  length (x ∷ xs) = 1 + length xs

  _T[∌]?_ : T-Decidable _∌_
  xs T[∌]? x = T-decide


  mutual
    infixl 5 _∪_
    _∪_ : UniqueList → UniqueList → UniqueList
    []                     ∪ ys = ys
    ((x ∷ xs) {{T[xs∌x]}}) ∪ ys with ys T[∌]? x
    ... | yes T[ys∌x] = (x ∷ (xs ∪ ys)) {{∪-preserves-∌ {xs} T[xs∌x] T[ys∌x]}}
    ... | no ¬T[ys∌x] = xs ∪ ys

    ∪-preserves-∌ : ∀ {xs ys z} → T (xs ∌ z) → T (ys ∌ z) → T (xs ∪ ys ∌ z)
    ∪-preserves-∌ {[]}     {ys} tt          T[ys∌z] = T[ys∌z]
    ∪-preserves-∌ {x ∷ xs} {ys} T[x≉z∧xs∌z] T[ys∌z] with T-fst T[x≉z∧xs∌z] | T-snd T[x≉z∧xs∌z]
    ... | T[x≉z] | T[xs∌z]                          with ys T[∌]? x
    ... | yes T[ys∌x]                               = T-pair T[x≉z] (∪-preserves-∌ {xs} T[xs∌z] T[ys∌z])
    ... | no ¬T[ys∌x]                               = ∪-preserves-∌ {xs} T[xs∌z] T[ys∌z]

  mutual
    _∖_ : UniqueList → UniqueList → UniqueList
    []                     ∖ ys = []
    ((x ∷ xs) {{T[xs∌x]}}) ∖ ys with ys T[∌]? x
    ... | yes T[ys∌x] = (x ∷ (xs ∖ ys)) {{∖-preserves-∌ {xs} T[xs∌x] T[ys∌x]}}
    ... | no ¬T[ys∌x] = xs ∖ ys

    ∖-preserves-∌ : ∀ {xs ys z} → T (xs ∌ z) → T (ys ∌ z) → T (xs ∖ ys ∌ z)
    ∖-preserves-∌ {[]}     {ys} tt          T[ys∌z] = tt
    ∖-preserves-∌ {x ∷ xs} {ys} T[x≠z∧xs∌z] T[ys∌z] with T-fst T[x≠z∧xs∌z] | T-snd T[x≠z∧xs∌z]
    ... | T[x≠z] | T[xs∌z]                          with ys T[∌]? x
    ... | yes T[ys∌x]                               = T-pair T[x≠z] (∖-preserves-∌ {xs} T[xs∌z] T[ys∌z])
    ... | no ¬T[ys∌x]                               = ∖-preserves-∌ {xs} T[xs∌z] T[ys∌z]


  module _ where
    open import Data.Nat using (_≤_ ; s≤s)
    open import Data.Nat.Properties using (≤-refl ; ≤-step)

    length-triangular : ∀ xs ys → length (xs ∪ ys) ≤ length xs + length ys
    length-triangular []       ys = ≤-refl
    length-triangular (x ∷ xs) ys with ys T[∌]? x
    ... | yes _ = s≤s (length-triangular xs ys)
    ... | no _  = ≤-step (length-triangular xs ys)

    length-untitled : ∀ xs ys → length (xs ∖ ys) ≤ length xs
    length-untitled []       ys = ≤-refl
    length-untitled (x ∷ xs) ys with ys T[∌]? x
    ... | yes _ = s≤s (length-untitled xs ys)
    ... | no _  = ≤-step (length-untitled xs ys)


  module _ where
    open import Data.Nat using (_≤′_ ; ≤′-refl ; ≤′-step)
    open import Data.Nat.Properties using (s≤′s)

    length-triangular′ : ∀ xs ys → length (xs ∪ ys) ≤′ length xs + length ys
    length-triangular′ []       ys = ≤′-refl
    length-triangular′ (x ∷ xs) ys with ys T[∌]? x
    ... | yes _ = s≤′s (length-triangular′ xs ys)
    ... | no _  = ≤′-step (length-triangular′ xs ys)

    length-untitled′ : ∀ xs ys → length (xs ∖ ys) ≤′ length xs
    length-untitled′ []       ys = ≤′-refl
    length-untitled′ (x ∷ xs) ys with ys T[∌]? x
    ... | yes _ = s≤′s (length-untitled′ xs ys)
    ... | no _  = ≤′-step (length-untitled′ xs ys)


private
  module _ where
    open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
    open import Data.Nat.Properties using (≡-decSetoid)
    open module UniqueList_Nat = MakeUniqueList (≡-decSetoid)

    test0 : (0 ∷ 1 ∷ []) ∪ [] ≡ 0 ∷ 1 ∷ []
    test0 = refl

    test1 : (0 ∷ 1 ∷ []) ∪ (0 ∷ 1 ∷ []) ≡ 0 ∷ 1 ∷ []
    test1 = refl

    test2 : (1 ∷ 0 ∷ []) ∪ (0 ∷ 1 ∷ []) ≡ 0 ∷ 1 ∷ []
    test2 = refl
