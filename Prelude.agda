---------------------------------------------------------------------------------------------------------------

module Prelude where

open import Agda.Builtin.FromString public
  using (IsString ; fromString)

open import Data.Bool public
  using (_∧_ ; Bool ; T ; false ; not ; true)

open import Data.Empty public
  using (⊥ ; ⊥-elim)

open import Data.List public
  using (List ; [] ; _∷_)

open import Data.Nat public
  using (_≤_ ; _≤′_ ; _<_ ; _+_ ; _⊔_ ; ≤′-refl ; ≤′-step ; s≤s ; suc ; z≤n ; zero)
  renaming (ℕ to Nat)

open import Data.Nat.Properties public
  using (module ≤-Reasoning ; ≤-refl ; ≤-step ; ≤-trans ; +-comm ; +-mono-≤ ; +-monoˡ-≤
        ; m≤m+n ; n≤m+n ; m≤m⊔n ; n≤m⊔n ; s≤′s ; z≤′n)
open ≤-Reasoning public

open import Data.Product public
  using (_×_ ; _,_ ; Σ ; ∃ ; proj₁ ; proj₂)

open import Data.String public
  using (String)

import Data.String.Unsafe as String

open import Data.Sum public
  using (_⊎_ ; inj₁ ; inj₂)

open import Data.Unit public
  using (⊤ ; tt)

open import Function public
  using (_∘_ ; case_of_ ; _on_)

open import Induction.Nat public
  using (<-wellFounded)

open import Induction.WellFounded public
  using (module All ; WellFounded ; acc)
  renaming (module Inverse-image to InverseImage ; Acc to Accessible ; WfRec to Below)

open import Level public
  using ()
  renaming (_⊔_ to _⊔ᴸ_ ; 0ℓ to 0ᴸ ; suc to sucᴸ)

open import Relation.Binary public
  using (Decidable ; Reflexive ; Rel ; Transitive)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; _≢_ ; refl)
  renaming (cong to _&_ ; sym to _⁻¹ ; isEquivalence to ≡-isEquivalence)

import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
open Star public
  using (_◅_ ; _◅◅_ ; ε)
  renaming (Star to _*)

open import Relation.Nullary public
  using (¬_ ; Dec ; no ; yes)

open import Relation.Nullary.Decidable public
  using (⌊_⌋)

open import Relation.Nullary.Negation public
  using (contraposition)
  renaming (contradiction to _↯_)

open import Relation.Unary public
  using (Pred)


---------------------------------------------------------------------------------------------------------------
--
-- Miscellaneous

_↔_ : ∀ {a b} → Set a → Set b → Set _
A ↔ B = (A → B) × (B → A)

infixl 8 _⊗_
_⊗_ : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} {x y : A} →
      f ≡ g → x ≡ y → f x ≡ g y
refl ⊗ refl = refl

coerce : ∀ {ℓ} {A B : Set ℓ} → A → A ≡ B → B
coerce x refl = x

Pred₀ : ∀ {a} → Set a → Set _
Pred₀ A = Pred A 0ᴸ

Rel₀ : ∀ {a} → Set a → Set _
Rel₀ A = Rel A 0ᴸ

record HasDecidableEquality {a} (A : Set a) : Set a where
  field
    _≟_ : Decidable {A = A} _≡_

open HasDecidableEquality {{...}} public


---------------------------------------------------------------------------------------------------------------
--
-- Data.Bool extras

T-Decidable : ∀ {a b} {A : Set a} {B : Set b} → (A → B → Bool) → Set _
T-Decidable _∼_ = ∀ x y → Dec (T (x ∼ y))

T-decide : ∀ {p} → Dec (T p)
T-decide {true}  = yes tt
T-decide {false} = no λ ()

T-pair : ∀ {p q} → T p → T q → T (p ∧ q)
T-pair {true}  tt T⟨q⟩ = T⟨q⟩
T-pair {false} () T⟨q⟩

T-fst : ∀ {p q} → T (p ∧ q) → T p
T-fst {true}  T⟨q⟩ = tt
T-fst {false} ()

T-snd : ∀ {p q} → T (p ∧ q) → T q
T-snd {true}  T⟨q⟩ = T⟨q⟩
T-snd {false} ()


---------------------------------------------------------------------------------------------------------------
--
-- Data.Nat extras

m≤m+n+o : ∀ m n o → m ≤ m + n + o
m≤m+n+o m n o = ≤-trans (m≤m+n m n) (m≤m+n (m + n) o)

n≤m+n+o : ∀ m n o → n ≤ m + n + o
n≤m+n+o m n o = ≤-trans (n≤m+n m n) (m≤m+n (m + n) o)

o≤m+n+o : ∀ m n o → o ≤ m + n + o
o≤m+n+o m n o = n≤m+n (m + n) o

m≤m⊔n⊔o : ∀ m n o → m ≤ m ⊔ n ⊔ o
m≤m⊔n⊔o m n o = ≤-trans (m≤m⊔n m n) (m≤m⊔n (m ⊔ n) o)

n≤m⊔n⊔o : ∀ m n o → n ≤ m ⊔ n ⊔ o
n≤m⊔n⊔o m n o = ≤-trans (n≤m⊔n m n) (m≤m⊔n (m ⊔ n) o)

o≤m⊔n⊔o : ∀ m n o → o ≤ m ⊔ n ⊔ o
o≤m⊔n⊔o m n o = n≤m⊔n (m ⊔ n) o


---------------------------------------------------------------------------------------------------------------
--
-- Data.Star extras

pattern _◅⟨_⟩_ r y rs = _◅_ {_} {y} {_} r rs

_◅ʳ_ : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} →
       ∀ {x y z} → (R *) x y → R y z → (R *) x z
R*xy ◅ʳ Ryz = R*xy ◅◅ (Ryz ◅ ε)

map : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} {f : A → A} →
      (∀ {x y} → R x y → R (f x) (f y)) →
      ∀ {x y} → (R *) x y → (R *) (f x) (f y)
map {f = f} = Star.gmap f


---------------------------------------------------------------------------------------------------------------
--
-- Induction.WellFounded extras

-- Below : ∀ {a p ℓ} {A : Set a} → Rel A ℓ → Pred A p → A → Set _
-- Below _<_ P x = ∀ y → y < x → P y

Closed : ∀ {a p ℓ} {A : Set a} → Rel A ℓ → Pred A p → Set _
Closed _<_ P = ∀ x → Below _<_ P x → P x

AccessibleBelow : ∀ {a ℓ} {A : Set a} → Rel A ℓ → A → Set _
AccessibleBelow _<_ x = Below _<_ (Accessible _<_) x

-- WellFounded : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
-- WellFounded _<_ = ∀ x → Accessible _<_ x

WellFoundedBelow : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
WellFoundedBelow _<_ = ∀ x → AccessibleBelow _<_ x

InductionPrinciple : ∀ {a p ℓ} {A : Set a} → Rel A ℓ → Pred A p → Set _
InductionPrinciple _<_ P = Closed _<_ P → ∀ x → P x

indWith : ∀ {a p ℓ} {A : Set a} {_<_ : Rel A ℓ} {P : Pred A p} → WellFounded _<_ → InductionPrinciple _<_ P
indWith {P = P} wf = All.wfRec wf _ P


---------------------------------------------------------------------------------------------------------------
--
-- Unique lists, or set-like containers

mutual
  infixr 5 _∷_
  data UniqueList {a} (A : Set a) {{_ : HasDecidableEquality A}} : Set a where
    []  : UniqueList A
    _∷_ : (x : A) (xs : UniqueList A) {{_ : T (xs ∌ x)}} → UniqueList A

  infix 4 _≠_
  _≠_ : ∀ {a} {A : Set a} → A → A → {{_ : HasDecidableEquality A}} → Bool
  x ≠ y = not ⌊ x ≟ y ⌋

  infix 4 _∌_
  _∌_ : ∀ {a} {A : Set a} {{_ : HasDecidableEquality A}} → UniqueList A → A → Bool
  []       ∌ y = true
  (x ∷ xs) ∌ y = (x ≠ y) ∧ (xs ∌ y)

module _ {a} {A : Set a} {{_ : HasDecidableEquality A}}
  where
    [_] : A → UniqueList A
    [ x ] = x ∷ []

    length : UniqueList A → Nat
    length []       = 0
    length (x ∷ xs) = 1 + length xs

    _T⟨∌⟩?_ : T-Decidable (_∌_ {A = A})
    xs T⟨∌⟩? x = T-decide

    private
      module OperatorWith
          (∅○ys               : UniqueList A → UniqueList A)
          (T⟨ys∌z⟩→T⟨∅○ys∌z⟩ : ∀ {ys z} → T (ys ∌ z) → T (∅○ys ys ∌ z))
        where
          mutual
            infixl 5 _○_
            _○_ : UniqueList A → UniqueList A → UniqueList A
            []                     ○ ys = ∅○ys ys
            ((x ∷ xs) {{T⟨xs∌x⟩}}) ○ ys with ys T⟨∌⟩? x
            ... | yes T⟨ys∌x⟩ = (x ∷ (xs ○ ys)) {{○-preserves-∌ {xs} T⟨xs∌x⟩ T⟨ys∌x⟩}}
            ... | no ¬T⟨ys∌x⟩ = xs ○ ys

            ○-preserves-∌ : ∀ {xs ys z} → T (xs ∌ z) → T (ys ∌ z) → T (xs ○ ys ∌ z)
            ○-preserves-∌ {[]}     {ys} tt          T⟨ys∌z⟩ = T⟨ys∌z⟩→T⟨∅○ys∌z⟩ T⟨ys∌z⟩
            ○-preserves-∌ {x ∷ xs} {ys} T⟨x≉z∧xs∌z⟩ T⟨ys∌z⟩ with T-fst T⟨x≉z∧xs∌z⟩ | T-snd T⟨x≉z∧xs∌z⟩
            ... | T⟨x≉z⟩ | T⟨xs∌z⟩                          with ys T⟨∌⟩? x
            ... | yes T⟨ys∌x⟩                               = T-pair T⟨x≉z⟩ (○-preserves-∌ {xs} T⟨xs∌z⟩ T⟨ys∌z⟩)
            ... | no ¬T⟨ys∌x⟩                               = ○-preserves-∌ {xs} T⟨xs∌z⟩ T⟨ys∌z⟩

    open OperatorWith (λ ys → ys) (λ T⟨ys∌z⟩ → T⟨ys∌z⟩) public
      renaming (_○_ to _∪_ ; ○-preserves-∌ to ∪-preserves-∌)

    open OperatorWith (λ _ → []) (λ _ → tt) public
      renaming (_○_ to _∖_ ; ○-preserves-∌ to ∖-preserves-∌)

    length-triangular : ∀ xs ys → length (xs ∪ ys) ≤ length xs + length ys
    length-triangular []       ys = ≤-refl
    length-triangular (x ∷ xs) ys with ys T⟨∌⟩? x
    ... | yes _ = s≤s (length-triangular xs ys)
    ... | no _  = ≤-step (length-triangular xs ys)

    length-untitled : ∀ xs ys → length (xs ∖ ys) ≤ length xs
    length-untitled []       ys = ≤-refl
    length-untitled (x ∷ xs) ys with ys T⟨∌⟩? x
    ... | yes _ = s≤s (length-untitled xs ys)
    ... | no _  = ≤-step (length-untitled xs ys)


---------------------------------------------------------------------------------------------------------------
--
-- String-based names

data Name : Set₀ where
  name : String → Name

_≟ᴺ_ : Decidable {A = Name} _≡_
name x ≟ᴺ name y with x String.≟ y
... | yes refl = yes refl
... | no x≢y   = no λ where refl → refl ↯ x≢y

instance
  Name-hasDecidableEquality : HasDecidableEquality Name
  Name-hasDecidableEquality = record { _≟_ = _≟ᴺ_ }

instance
  Name-isString : IsString Name
  Name-isString = record
    { Constraint = λ s → ⊤
    ; fromString = λ s → name s
    }


---------------------------------------------------------------------------------------------------------------
