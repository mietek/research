module Chapter3 where


------------------------------------------------------------------------------


-- NOTE: For comparison only
module UniqueListWithStructuredProofs where
  open import Data.Nat using (_+_ ; ℕ)
  open import Level using (_⊔_)
  open import Relation.Binary using (Decidable ; DecSetoid)
  open import Relation.Nullary using (¬_ ; no ; yes)
  open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)

  module MakeUniqueList {c ℓ} (DS : DecSetoid c ℓ) where
    open DecSetoid DS using (Carrier ; _≈_ ; _≟_)

    mutual
      infixr 5 _∷_
      data UniqueList : Set (c ⊔ ℓ) where
        []  : UniqueList
        _∷_ : (x : Carrier) (xs : UniqueList) {{_ : xs ∌ x}} → UniqueList

      infix 4 _≉_
      _≉_ : Carrier → Carrier → Set ℓ
      x ≉ y = ¬ (x ≈ y)

      infix 4 _∌_
      data _∌_ : UniqueList → Carrier → Set (c ⊔ ℓ) where
        instance
          tt  : ∀ {x} → [] ∌ x
          _∧_ : ∀ {x xs y} {{_ : xs ∌ x}} → x ≉ y → xs ∌ y → x ∷ xs ∌ y

    [_] : Carrier → UniqueList
    [ x ] = x ∷ []

    length : UniqueList → ℕ
    length []       = 0
    length (x ∷ xs) = 1 + length xs

    _∌?_ : Decidable _∌_
    []       ∌? y = yes tt
    (x ∷ xs) ∌? y with xs ∌? y | x ≟ y
    ... | yes xs∌y | no x≉y  = yes (x≉y ∧ xs∌y)
    ... | yes xs∌y | yes x≈y = no λ { (x≉y ∧ xs∌x) → x≈y ↯ x≉y }
    ... | no ¬xs∌y | _       = no λ { (x≉y ∧ xs∌y) → xs∌y ↯ ¬xs∌y }

    mutual
      infixl 5 _∪_
      _∪_ : UniqueList → UniqueList → UniqueList
      []                  ∪ ys = ys
      ((x ∷ xs) {{xs∌x}}) ∪ ys with ys ∌? x
      ... | yes ys∌x = (x ∷ (xs ∪ ys)) {{∪-preserves-∌ xs∌x ys∌x}}
      ... | no ¬ys∌x = xs ∪ ys

      ∪-preserves-∌ : ∀ {xs ys z} → xs ∌ z → ys ∌ z → xs ∪ ys ∌ z
      ∪-preserves-∌ {[]}            tt             ys∌z = ys∌z
      ∪-preserves-∌ {x′ ∷ xs′} {ys} (x′≢z ∧ xs′∌z) ys∌z with ys ∌? x′
      ... | yes ys∌x′ = x′≢z ∧ (∪-preserves-∌ xs′∌z ys∌z)
      ... | no ¬ys∌x′ = ∪-preserves-∌ xs′∌z ys∌z

    module _ where
      open import Data.Nat using (_≤_ ; s≤s)
      open import Data.Nat.Properties using (≤-refl ; ≤-step)

      length-triangular : (xs ys : UniqueList) → length (xs ∪ ys) ≤ length xs + length ys
      length-triangular []       ys = ≤-refl
      length-triangular (x ∷ xs) ys with ys ∌? x
      ... | yes _ = s≤s (length-triangular xs ys)
      ... | no _  = ≤-step (length-triangular xs ys)

    module _ where
      open import Data.Nat using (_≤′_ ; ≤′-refl ; ≤′-step)
      open import Data.Nat.Properties using (s≤′s)

      length-triangular′ : (xs ys : UniqueList) → length (xs ∪ ys) ≤′ length xs + length ys
      length-triangular′ []       ys = ≤′-refl
      length-triangular′ (x ∷ xs) ys with ys ∌? x
      ... | yes _ = s≤′s (length-triangular′ xs ys)
      ... | no _  = ≤′-step (length-triangular′ xs ys)

  private
    module _ where
      open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
      open import Data.Nat.Properties using (≡-decSetoid)
      open module UniqueList_Nat = MakeUniqueList (≡-decSetoid)

      -- NOTE: Instance resolution has trouble here; no trouble in the version below.
      -- test1 : (1 ∷ [ 0 ]) ∪ (1 ∷ [ 0 ]) ≡ 1 ∷ [ 0 ]
      -- test1 = refl


------------------------------------------------------------------------------


-- NOTE: Preferred version
module UniqueListWithUnstructuredProofs where
  open import Data.Bool using (_∧_ ; Bool ; T ; false ; not ; true)
  open import Data.Nat using (_+_ ; ℕ)
  open import Data.Unit using (tt)
  open import Level using (_⊔_)
  open import Relation.Binary using (DecSetoid)
  open import Relation.Nullary using (¬_ ; Dec ; no ; yes)
  open import Relation.Nullary.Decidable using (⌊_⌋)

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
      []                    ∪ ys = ys
      ((x ∷ xs) {{T[xs∌x]}}) ∪ ys with ys T[∌]? x
      ... | yes T[ys∌x] = (x ∷ (xs ∪ ys)) {{∪-preserves-∌ {xs} T[xs∌x] T[ys∌x]}}
      ... | no ¬T[ys∌x] = xs ∪ ys

      ∪-preserves-∌ : ∀ {xs ys z} → T (xs ∌ z) → T (ys ∌ z) → T (xs ∪ ys ∌ z)
      ∪-preserves-∌ {[]}            tt            T[ys∌z] = T[ys∌z]
      ∪-preserves-∌ {x′ ∷ xs′} {ys} T[x′≉z∧xs′∌z] T[ys∌z] with T-fst T[x′≉z∧xs′∌z] | T-snd T[x′≉z∧xs′∌z] | ys T[∌]? x′
      ... | T[x′≉z] | T[xs′∌z] | yes T[ys∌x′] = T-pair T[x′≉z] (∪-preserves-∌ {xs′} T[xs′∌z] T[ys∌z])
      ... | T[x′≉z] | T[xs′∌z] | no ¬T[ys∌x′] = ∪-preserves-∌ {xs′} T[xs′∌z] T[ys∌z]

    module _ where
      open import Data.Nat using (_≤_ ; s≤s)
      open import Data.Nat.Properties using (≤-refl ; ≤-step)

      length-triangular : (xs ys : UniqueList) → length (xs ∪ ys) ≤ length xs + length ys
      length-triangular []       ys = ≤-refl
      length-triangular (x ∷ xs) ys with ys T[∌]? x
      ... | yes _ = s≤s (length-triangular xs ys)
      ... | no _  = ≤-step (length-triangular xs ys)

    module _ where
      open import Data.Nat using (_≤′_ ; ≤′-refl ; ≤′-step)
      open import Data.Nat.Properties using (s≤′s)

      length-triangular′ : (xs ys : UniqueList) → length (xs ∪ ys) ≤′ length xs + length ys
      length-triangular′ []       ys = ≤′-refl
      length-triangular′ (x ∷ xs) ys with ys T[∌]? x
      ... | yes _ = s≤′s (length-triangular′ xs ys)
      ... | no _  = ≤′-step (length-triangular′ xs ys)

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


------------------------------------------------------------------------------


module Nat′ where
  open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _≤′_ ; ≤′-refl ; ≤′-step ; _<′_)
  import Data.Nat.Properties as Nat
  open Nat using (z≤′n ; s≤′s ; ≤′⇒≤ ; ≤⇒≤′)
  open import Data.Sum using (inj₁ ; inj₂)
  open import Level using (0ℓ)
  import Relation.Binary as Rel
  open Rel using (_⇒_)
  import Relation.Binary.PropositionalEquality as PropEq
  open PropEq using (_≡_ ; _≢_ ; refl)
  open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
  open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)

  ≤′-reflexive : _≡_ ⇒ _≤′_
  ≤′-reflexive refl = ≤′-refl

  ≤′-antisym : Rel.Antisymmetric _≡_ _≤′_
  ≤′-antisym m≤′n n≤′m = Nat.≤-antisym (≤′⇒≤ m≤′n) (≤′⇒≤ n≤′m)

  ≤′-trans : Rel.Transitive _≤′_
  ≤′-trans m≤′n n≤′o = ≤⇒≤′ (Nat.≤-trans (≤′⇒≤ m≤′n) (≤′⇒≤ n≤′o))

  ≤′-total : Rel.Total _≤′_
  ≤′-total m n with Nat.≤-total m n
  ...          | inj₁ m≤′n = inj₁ (≤⇒≤′ m≤′n)
  ...          | inj₂ n≤′m = inj₂ (≤⇒≤′ n≤′m)

  infix 4 _≤′?_
  _≤′?_ : Rel.Decidable _≤′_
  m ≤′? n with m Nat.≤? n
  ...     | yes m≤′n = yes (≤⇒≤′ m≤′n)
  ...     | no m≰n  = no λ { m≤′n → ≤′⇒≤ m≤′n ↯ m≰n }

  ≤′-isPreorder : Rel.IsPreorder _≡_ _≤′_
  ≤′-isPreorder = record
    { isEquivalence = PropEq.isEquivalence
    ; reflexive     = ≤′-reflexive
    ; trans         = ≤′-trans
    }

  ≤′-preorder : Rel.Preorder 0ℓ 0ℓ 0ℓ
  ≤′-preorder = record
    { isPreorder = ≤′-isPreorder
    }

  ≤′-isPartialOrder : Rel.IsPartialOrder _≡_ _≤′_
  ≤′-isPartialOrder = record
    { isPreorder = ≤′-isPreorder
    ; antisym    = ≤′-antisym
    }

  ≤′-isTotalOrder : Rel.IsTotalOrder _≡_ _≤′_
  ≤′-isTotalOrder = record
    { isPartialOrder = ≤′-isPartialOrder
    ; total          = ≤′-total
    }

  ≤′-totalOrder : Rel.TotalOrder 0ℓ 0ℓ 0ℓ
  ≤′-totalOrder = record
    { isTotalOrder = ≤′-isTotalOrder
    }

  ≤′-isDecTotalOrder : Rel.IsDecTotalOrder _≡_ _≤′_
  ≤′-isDecTotalOrder = record
    { isTotalOrder = ≤′-isTotalOrder
    ; _≟_          = Nat._≟_
    ; _≤?_         = _≤′?_
    }

  ≤′-decTotalOrder : Rel.DecTotalOrder 0ℓ 0ℓ 0ℓ
  ≤′-decTotalOrder = record
    { isDecTotalOrder = ≤′-isDecTotalOrder
    }

  module ≤′-Reasoning where
    open import Relation.Binary.PartialOrderReasoning (Rel.DecTotalOrder.poset ≤′-decTotalOrder) public
      using (_IsRelatedTo_ ; begin_ ; _≡⟨_⟩_ ; _∎)
      renaming (_≤⟨_⟩_ to _≤′⟨_⟩_)

    infixr 2 _<′⟨_⟩_
    _<′⟨_⟩_ : ∀ x {y z} → x <′ y → y IsRelatedTo z → suc x IsRelatedTo z
    x <′⟨ x<′y ⟩ y≤′z = suc x ≤′⟨ x<′y ⟩ y≤′z

  +-mono-≤′ : _+_ Rel.Preserves₂ _≤′_ ⟶ _≤′_ ⟶ _≤′_
  +-mono-≤′ x≤′y u≤′v = ≤⇒≤′ (Nat.+-mono-≤ (≤′⇒≤ x≤′y) (≤′⇒≤ u≤′v))

  +-monoˡ-≤′ : ∀ n → (_+ n) Rel.Preserves _≤′_ ⟶ _≤′_
  +-monoˡ-≤′ n m≤′o = +-mono-≤′ m≤′o (≤′-refl {n})


------------------------------------------------------------------------------


open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _⊔_)
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_ ; _≢_ ; refl)
open import Relation.Binary using (DecSetoid)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open UniqueListWithUnstructuredProofs


-- 3. Untyped arithmetic expressions

-- 3.1. Introduction

-- 3.2. Syntax

-- 3.2.1. Definition [Terms, inductively]

data Term : Set where
  true false zero  : Term
  succ pred iszero : (t₁ : Term) → Term
  if_then_else     : (t₁ t₂ t₃ : Term) → Term

_≟_ : (r s : Term) → Dec (r ≡ s)
true                  ≟ true                  = yes refl
true                  ≟ false                 = no λ ()
true                  ≟ zero                  = no λ ()
true                  ≟ succ s₁               = no λ ()
true                  ≟ pred s₁               = no λ ()
true                  ≟ iszero s₁             = no λ ()
true                  ≟ if s₁ then s₂ else s₃ = no λ ()
false                 ≟ true                  = no λ ()
false                 ≟ false                 = yes refl
false                 ≟ zero                  = no λ ()
false                 ≟ succ s₁               = no λ ()
false                 ≟ pred s₁               = no λ ()
false                 ≟ iszero s₁             = no λ ()
false                 ≟ if s₁ then s₂ else s₃ = no λ ()
zero                  ≟ true                  = no λ ()
zero                  ≟ false                 = no λ ()
zero                  ≟ zero                  = yes refl
zero                  ≟ succ s₁               = no λ ()
zero                  ≟ pred s₁               = no λ ()
zero                  ≟ iszero s₁             = no λ ()
zero                  ≟ if s₁ then s₂ else s₃ = no λ ()
succ r₁               ≟ true                  = no λ ()
succ r₁               ≟ false                 = no λ ()
succ r₁               ≟ zero                  = no λ ()
succ r₁               ≟ succ s₁               with r₁ ≟ s₁
... | yes refl = yes refl
... | no r₁≢s₁ = no λ { refl → refl ↯ r₁≢s₁ }
succ r₁               ≟ pred s₁               = no λ ()
succ r₁               ≟ iszero s₁             = no λ ()
succ r₁               ≟ if s₁ then s₂ else s₃ = no λ ()
pred r₁               ≟ true                  = no λ ()
pred r₁               ≟ false                 = no λ ()
pred r₁               ≟ zero                  = no λ ()
pred r₁               ≟ succ s₁               = no λ ()
pred r₁               ≟ pred s₁               with r₁ ≟ s₁
... | yes refl = yes refl
... | no r₁≢s₁ = no λ { refl → refl ↯ r₁≢s₁ }
pred r₁               ≟ iszero s₁             = no λ ()
pred r₁               ≟ if s₁ then s₂ else s₃ = no λ ()
iszero r₁             ≟ true                  = no λ ()
iszero r₁             ≟ false                 = no λ ()
iszero r₁             ≟ zero                  = no λ ()
iszero r₁             ≟ succ s₁               = no λ ()
iszero r₁             ≟ pred s₁               = no λ ()
iszero r₁             ≟ iszero s₁             with r₁ ≟ s₁
... | yes refl = yes refl
... | no r₁≢s₁ = no λ { refl → refl ↯ r₁≢s₁ }
iszero r₁             ≟ if s₁ then s₂ else s₃ = no λ ()
if r₁ then r₂ else r₃ ≟ true                  = no λ ()
if r₁ then r₂ else r₃ ≟ false                 = no λ ()
if r₁ then r₂ else r₃ ≟ zero                  = no λ ()
if r₁ then r₂ else r₃ ≟ succ s₁               = no λ ()
if r₁ then r₂ else r₃ ≟ pred s₁               = no λ ()
if r₁ then r₂ else r₃ ≟ iszero s₁             = no λ ()
if r₁ then r₂ else r₃ ≟ if s₁ then s₂ else s₃ with r₁ ≟ s₁ | r₂ ≟ s₂ | r₃ ≟ s₃
... | yes refl | yes refl | yes refl = yes refl
... | no r₁≢s₁ | _        | _        = no λ { refl → refl ↯ r₁≢s₁ }
... | _        | no r₂≢s₂ | _        = no λ { refl → refl ↯ r₂≢s₂ }
... | _        | _        | no r₃≢s₃ = no λ { refl → refl ↯ r₃≢s₃ }

Term-decSetoid : DecSetoid _ _
Term-decSetoid = record
  { Carrier = Term
  ; _≈_     = _≡_
  ; isDecEquivalence = record
    { isEquivalence = PropEq.isEquivalence
    ; _≟_           = _≟_
    }
  }

open module UniqueList-Term = MakeUniqueList (Term-decSetoid)

-- 3.2.2. Definition [Terms, by inference rules] (redundant)

-- 3.2.3. Definition [Terms, concretely] (redundant)

-- 3.2.4. Exercise (skipped)

-- 3.2.5. Exercise (skipped)

-- 3.2.6. Proposition (skipped)

-- 3.3. Induction on terms

-- 3.3.1. Definition

consts : Term → UniqueList
consts true                    = [ true ]
consts false                   = [ false ]
consts zero                    = [ zero ]
consts (succ t₁)               = consts t₁
consts (pred t₁)               = consts t₁
consts (iszero t₁)             = consts t₁
consts (if t₁ then t₂ else t₃) = consts t₁ ∪ consts t₂ ∪ consts t₃

-- 3.3.2. Definition

size : Term → ℕ
size true                    = 1
size false                   = 1
size zero                    = 1
size (succ t₁)               = 1 + size t₁
size (pred t₁)               = 1 + size t₁
size (iszero t₁)             = 1 + size t₁
size (if t₁ then t₂ else t₃) = 1 + size t₁ + size t₂ + size t₃

depth : Term → ℕ
depth true                    = 1
depth false                   = 1
depth zero                    = 1
depth (succ t₁)               = 1 + depth t₁
depth (pred t₁)               = 1 + depth t₁
depth (iszero t₁)             = 1 + depth t₁
depth (if t₁ then t₂ else t₃) = 1 + depth t₁ ⊔ depth t₂ ⊔ depth t₃

-- 3.3.3. Lemma

module Lemma333 where
  open import Data.Nat using (_≤_ ; z≤n ; s≤s)
  open import Data.Nat.Properties using (≤-refl ; ≤-step ; +-mono-≤ ; +-monoˡ-≤ ; module ≤-Reasoning)

  lem-333 : ∀ (s : Term) → length (consts s) ≤ size s
  lem-333 true                    = ≤-refl
  lem-333 false                   = ≤-refl
  lem-333 zero                    = ≤-refl
  lem-333 (succ s₁)               = ≤-step (lem-333 s₁)
  lem-333 (pred s₁)               = ≤-step (lem-333 s₁)
  lem-333 (iszero s₁)             = ≤-step (lem-333 s₁)
  lem-333 (if s₁ then s₂ else s₃) = ≤-step
    (begin
      length (consts s₁ ∪ consts s₂ ∪ consts s₃)
    ≤⟨ length-triangular (consts s₁ ∪ consts s₂) (consts s₃) ⟩
      length (consts s₁ ∪ consts s₂) + length (consts s₃)
    ≤⟨ +-monoˡ-≤ (length (consts s₃)) (length-triangular (consts s₁) (consts s₂)) ⟩
      length (consts s₁) + length (consts s₂) + length (consts s₃)
    ≤⟨ +-mono-≤ (+-mono-≤ (lem-333 s₁) (lem-333 s₂)) (lem-333 s₃) ⟩
      size s₁ + size s₂ + size s₃
    ∎)
    where
      open ≤-Reasoning

module Lemma333′ where
  open import Data.Nat using (_≤′_ ; ≤′-refl ; ≤′-step)
  open Nat′ using (+-mono-≤′ ; +-monoˡ-≤′ ; module ≤′-Reasoning)

  lem-333 : ∀ (s : Term) → length (consts s) ≤′ size s
  lem-333 true                    = ≤′-refl
  lem-333 false                   = ≤′-refl
  lem-333 zero                    = ≤′-refl
  lem-333 (succ s₁)               = ≤′-step (lem-333 s₁)
  lem-333 (pred s₁)               = ≤′-step (lem-333 s₁)
  lem-333 (iszero s₁)             = ≤′-step (lem-333 s₁)
  lem-333 (if s₁ then s₂ else s₃) = ≤′-step
    (begin
      length (consts s₁ ∪ consts s₂ ∪ consts s₃)
    ≤′⟨ length-triangular′ (consts s₁ ∪ consts s₂) (consts s₃) ⟩
      length (consts s₁ ∪ consts s₂) + length (consts s₃)
    ≤′⟨ +-monoˡ-≤′ (length (consts s₃)) (length-triangular′ (consts s₁) (consts s₂)) ⟩
      length (consts s₁) + length (consts s₂) + length (consts s₃)
    ≤′⟨ +-mono-≤′ (+-mono-≤′ (lem-333 s₁) (lem-333 s₂)) (lem-333 s₃) ⟩
      size s₁ + size s₂ + size s₃
    ∎)
    where
      open ≤′-Reasoning

-- 3.3.4. Theorem [Principles of induction on terms]

data IsSubtermOf : Term → Term → Set where
  is-subterm-of-succ   : ∀ {s₁} → IsSubtermOf s₁ (succ s₁)
  is-subterm-of-pred   : ∀ {s₁} → IsSubtermOf s₁ (pred s₁)
  is-subterm-of-iszero : ∀ {s₁} → IsSubtermOf s₁ (iszero s₁)
  is-subterm-of-ifte₁  : ∀ {s₁ s₂ s₃} → IsSubtermOf s₁ (if s₁ then s₂ else s₃)
  is-subterm-of-ifte₂  : ∀ {s₁ s₂ s₃} → IsSubtermOf s₂ (if s₁ then s₂ else s₃)
  is-subterm-of-ifte₃  : ∀ {s₁ s₂ s₃} → IsSubtermOf s₃ (if s₁ then s₂ else s₃)

ind-struct : ∀ {ℓ} → (P : Term → Set ℓ)
                   → (∀ (s : Term) → (∀ (r : Term) → IsSubtermOf r s → P r) → P s)
                   → (∀ (s : Term) → P s)
ind-struct P h s@true                 = h s λ r ()
ind-struct P h s@false                = h s λ r ()
ind-struct P h s@zero                 = h s λ r ()
ind-struct P h s@(succ _)             = h s λ { r is-subterm-of-succ → ind-struct P h r }
ind-struct P h s@(pred _)             = h s λ { r is-subterm-of-pred → ind-struct P h r }
ind-struct P h s@(iszero _)           = h s λ { r is-subterm-of-iszero → ind-struct P h r }
ind-struct P h s@(if _ then _ else _) = h s λ
  { r is-subterm-of-ifte₁ → ind-struct P h r
  ; r is-subterm-of-ifte₂ → ind-struct P h r
  ; r is-subterm-of-ifte₃ → ind-struct P h r
  }

module IndStructLemma333 where
  open import Data.Nat using (_≤_ ; z≤n ; s≤s)
  open import Data.Nat.Properties using (≤-refl ; ≤-step ; +-mono-≤ ; +-monoˡ-≤ ; module ≤-Reasoning)

  lem-333 : ∀ (s : Term) → length (consts s) ≤ size s
  lem-333 = ind-struct (λ s → length (consts s) ≤ size s) λ
    { true                    h → ≤-refl
    ; false                   h → ≤-refl
    ; zero                    h → ≤-refl
    ; (succ s₁)               h → ≤-step (h s₁ is-subterm-of-succ)
    ; (pred s₁)               h → ≤-step (h s₁ is-subterm-of-pred)
    ; (iszero s₁)             h → ≤-step (h s₁ is-subterm-of-iszero)
    ; (if s₁ then s₂ else s₃) h → ≤-step
      (begin
        length (consts s₁ ∪ consts s₂ ∪ consts s₃)
      ≤⟨ length-triangular (consts s₁ ∪ consts s₂) (consts s₃) ⟩
        length (consts s₁ ∪ consts s₂) + length (consts s₃)
      ≤⟨ +-monoˡ-≤ (length (consts s₃)) (length-triangular (consts s₁) (consts s₂)) ⟩
        length (consts s₁) + length (consts s₂) + length (consts s₃)
      ≤⟨ +-mono-≤ (+-mono-≤ (h s₁ is-subterm-of-ifte₁) (h s₂ is-subterm-of-ifte₂)) (h s₃ is-subterm-of-ifte₃) ⟩
        size s₁ + size s₂ + size s₃
      ∎)
    }
    where
      open ≤-Reasoning

{-
open import Level using (_⊔_)

data Acc {a ℓ} {A : Set a} (_<_ : A → A → Set ℓ) (x : A) : Set (a Level.⊔ ℓ) where
  acc : (∀ (y : A) → y < x → Acc _<_ y) → Acc _<_ x

WellFounded : ∀ {a ℓ} {A : Set a} → (A → A → Set ℓ) → Set _
WellFounded _<_ = ∀ x → Acc _<_ x
-}

open import Induction.WellFounded using (Acc ; WellFounded ; acc)

subterm-wf : WellFounded IsSubtermOf
subterm-wf s = acc λ
  { s₁ is-subterm-of-succ   → subterm-wf s₁
  ; s₁ is-subterm-of-pred   → subterm-wf s₁
  ; s₁ is-subterm-of-iszero → subterm-wf s₁
  ; s₁ is-subterm-of-ifte₁  → subterm-wf s₁
  ; s₂ is-subterm-of-ifte₂  → subterm-wf s₂
  ; s₃ is-subterm-of-ifte₃  → subterm-wf s₃
  }

module _ where
  open module Tmp {ℓ} = Induction.WellFounded.All subterm-wf ℓ using (wfRec)

  ind-tmp : ∀ {ℓ} → (P : Term → Set ℓ)
                 → (∀ (s : Term) → (∀ (r : Term) → IsSubtermOf r s → P r) → P s)
                 → (∀ (s : Term) → P s)
  ind-tmp = wfRec


module Foo where
  open import Data.Nat

  SmallerSize : Term → Term → Set
  SmallerSize r s = size r < size s

  lem : ∀ (s : Term) → ¬ (size s < 1)
  lem true                    = λ { (s≤s ()) }
  lem false                   = λ { (s≤s ()) }
  lem zero                    = λ { (s≤s ()) }
  lem (succ s₁)               = λ { (s≤s ()) }
  lem (pred s₁)               = λ { (s≤s ()) }
  lem (iszero s₁)             = λ { (s≤s ()) }
  lem (if s₁ then s₂ else s₃) = λ { (s≤s ()) }

  lem′ : ∀ (s : Term) → ¬ (size s <′ 1)
  lem′ true                    = λ { (≤′-step ()) }
  lem′ false                   = λ { (≤′-step ()) }
  lem′ zero                    = λ { (≤′-step ()) }
  lem′ (succ s₁)               = λ { (≤′-step ()) }
  lem′ (pred s₁)               = λ { (≤′-step ()) }
  lem′ (iszero s₁)             = λ { (≤′-step ()) }
  lem′ (if s₁ then s₂ else s₃) = λ { (≤′-step ()) }

  wf-smallersize : WellFounded SmallerSize
  wf-smallersize s = acc λ { r p → {!!} }

-- -- -- -- postulate -- TODO: use stdlib

-- -- module IndSize where
-- --   open import Data.Nat using (_≤_ ; _<_ ; z≤n ; s≤s)
-- --   open import Data.Nat.Properties using (≤-refl ; ≤-step)

-- --   lem : ∀ (s : Term) → ¬ (size s < 1)
-- --   lem true                    = λ { (s≤s ()) }
-- --   lem false                   = λ { (s≤s ()) }
-- --   lem zero                    = λ { (s≤s ()) }
-- --   lem (succ s₁)               = λ { (s≤s ()) }
-- --   lem (pred s₁)               = λ { (s≤s ()) }
-- --   lem (iszero s₁)             = λ { (s≤s ()) }
-- --   lem (if s₁ then s₂ else s₃) = λ { (s≤s ()) }

-- --   ind-size : ∀ {P : Term → Set} →
-- --                (∀ (s : Term) → (∀ (r : Term) → size r < size s → P r) → P s) →
-- --                (∀ (s : Term) → P s)
-- --   ind-size h = ind-struct λ
-- --     { s@true                    g → h s λ r p → p ↯ lem r
-- --     ; s@false                   g → h s λ r p → p ↯ lem r
-- --     ; s@zero                    g → h s λ r p → p ↯ lem r
-- --     ; s@(succ s₁)               g → h s λ { r (s≤s p) → {!!} }
-- --     ; s@(pred s₁)               g → {!!}
-- --     ; s@(iszero s₁)             g → {!!}
-- --     ; s@(if s₁ then s₂ else s₃) g → {!!}
-- --     }

-- -- -- -- SmallerDepth : Term → Term → Set
-- -- -- -- SmallerDepth r s = depth r < depth s

-- -- -- -- postulate -- TODO: use stdlib
-- -- -- --   ind-depth : ∀ (P : Term → Set) → (∀ {s} → (∀ {r} → SmallerDepth r s → P r) → P s) → (∀ s → P s)
