module STLC where

open import Data.List using (List ; [] ; _∷_ ; [_])
open import Data.List.Any using (any ; Any ; here ; there)
open import Data.Nat using (ℕ ; zero ; suc)
import Data.Nat
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Negation using (¬? ; contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
  renaming (refl to ≡-refl ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; subst to ≡-subst ; trans to ≡-trans)

infixl 9 𝑏𝑣_ 𝑓𝑣_
infixl 7 _$_
infixr 5 𝜆_
infixr 1 _⊃_


open import Atom using (Atom ; _≟_)



module ListSet (X : Set) (_≟_ : (x y : X) → Dec (x ≡ y)) where
  infix 4 _∈_ _∉_

  ListSet : Set
  ListSet = List X

  ∷-inj : {A B : ListSet} {x : X} → A ≡ B → x ∷ A ≡ x ∷ B
  ∷-inj ≡-refl = ≡-refl

  _∈_ : (x : X) (A : ListSet) → Set
  _∈_ = Data.List.Any.Membership-≡._∈_

  _∉_ : (x : X) (A : ListSet) → Set
  _∉_ = Data.List.Any.Membership-≡._∉_

  _∈?_ : (x : X) (A : ListSet) → Dec (x ∈ A)
  x ∈? A = any (_≟_ x) A

  _∉?_ : (x : X) (A : ListSet) → Dec (x ∉ A)
  x ∉? A = ¬? (x ∈? A)

  ∈-lm₁ : ∀{A x y} → x ∈ y ∷ A → x ≢ y → x ∈ A
  ∈-lm₁ (here  x≡y) x≢y = contradiction x≡y x≢y
  ∈-lm₁ (there x∈A) x≢y = x∈A

  ∈-lm₂ : ∀{A x y} → x ∉ y ∷ A → x ≢ y → x ∉ A
  ∈-lm₂ x∉y∷A x≢y x∈A = contradiction (there x∈A) x∉y∷A

  ∈-lm₃ : ∀{A x y} → x ∈ A → y ∉ A → x ≢ y
  ∈-lm₃ x∈A y∉A ≡-refl = contradiction x∈A y∉A

  ∈-lm₄ : ∀{A x y} → x ∈ A → x ∈ y ∷ A
  ∈-lm₄ x∈A = there x∈A

  _⊎_ : (x : X) (A : ListSet) → ListSet
  x ⊎ A with x ∈? A
  ...      | yes x∈A = A
  ...      | no  x∉A = x ∷ A

  {-x ⊎ []      = [ x ]
  x ⊎ (a ∷ A) with x ∈? A
  ...            | yes x∈A = a ∷ A
  ...            | no  x∉A = x ∷ a ∷ A-}
  {-x ⊎ (a ∷ A) with x ≟ a
  ...            | yes x≡a = a ∷ A
  ...            | no  x≢a = a ∷ x ⊎ A-}

  ⊎-lm₁ : ∀{A x} → x ∈ A → A ≡ x ⊎ A
  ⊎-lm₁ {[]}    {x} ()
  ⊎-lm₁ {a ∷ A} {x} x∈a∷A with x ∈? A
  ...                      | yes x∈A = {!!}
  ...                      | no  x∉A = {!!}

{-  ⊎-lm₁ {[]}    {x} ()
  ⊎-lm₁ {a ∷ A} {x} x∈a∷A with x ≟ a
  ...                        | yes x≡a = ≡-refl
  ...                        | no  x≢a = ∷-inj (⊎-lm₁ (∈-lm₁ x∈a∷A x≢a))-}

--  ⊎-lm₀ : ∀{A x y} → x ∉ A → x ≢ a → x ∷ a ∷ A ≡ x ⊎ a ∷ A

  ⊎-lm₂ : ∀{A x} → x ∉ A → x ∷ A ≡ x ⊎ A
  ⊎-lm₂ x∉A = {!!}
{-  ⊎-lm₂ {[]}    {x} x∉[]  = ≡-refl
  ⊎-lm₂ {a ∷ A} {x} x∉a∷A with x ≟ a
  ...                        | yes x≡a = contradiction (here x≡a) x∉a∷A
  ...                        | no  x≢a = {!!}-}

-- let x∷A≡x⊎A = ⊎-lm₂ (∈-lm₂ x∉a∷A x≢a) in

  ⊎-lm₃ : ∀{A x y} → x ∈ A → x ∈ y ⊎ A
  ⊎-lm₃ {A} {x} {y} x∈A with y ∈? A
  ...                      | yes y∈A = let A≡y⊎A = ⊎-lm₁ y∈A in ≡-subst {!!} A≡y⊎A x∈A
  ...                      | no  y∉A = {!!}
{-  ⊎-lm₃ {A} {x} {y} x∈A with y ∈? A
  ...                      | yes y∈A = ≡-subst (λ Z → x ∈ Z) (⊎-lm₁ y∈A) x∈A
  ...                      | no  y∉A = ≡-subst (λ Z → x ∈ Z) (⊎-lm₂ y∉A) (there x∈A)-}

  _∪_ : (A B : ListSet) → ListSet
  A ∪ []      = A
  A ∪ (b ∷ B) = b ⊎ (A ∪ B)

  ∪-lm₁ : ∀{A} → A ≡ A ∪ []
  ∪-lm₁ {[]}    = ≡-refl
  ∪-lm₁ {a ∷ A} = ∷-inj ∪-lm₁

  ∪-lm₂ : ∀{A x} → x ∈ A → x ∈ A ∪ []
  ∪-lm₂ (here ≡-refl) = here ≡-refl
  ∪-lm₂ (there x∈A)   = there (∪-lm₂ x∈A)

  ∪-lm₃ : ∀{A B x} → x ∈ A → x ∈ A ∪ B
  ∪-lm₃ {A} {[]}    x∈A = x∈A
  ∪-lm₃ {A} {b ∷ B} x∈A = ⊎-lm₃ {A ∪ B} (∪-lm₃ {A} {B} x∈A)


module AtomSet = ListSet Atom _≟_
open AtomSet

Atoms : Set
Atoms = AtomSet.ListSet


∈∪-lm₁ : ∀{x A B} → x ∈ A → x ∈ A ∪ B
∈∪-lm₁ {B = []}    x∈A           = ∪-lm₂ x∈A
∈∪-lm₁ {B = b ∷ B} (here ≡-refl) = {!!}
∈∪-lm₁ {B = b ∷ B} (there x∈A)   = {!!}

∈∪-lm₂ : ∀{x A B} → x ∈ B → x ∈ A ∪ B
∈∪-lm₂ {x} {[]}    x∈B = {!!} -- x∈B
∈∪-lm₂ {x} {a ∷ A} x∈B with x ≟ a
...                       | yes x≡a = {!!}
...                       | no  x≢a = {!!}

∉∪-lm₁ : ∀{x A B} → x ∉ A ∪ B → x ∉ A
∉∪-lm₁ x∉A∪B x∈A = contradiction (∈∪-lm₁ x∈A) x∉A∪B

∉∪-lm₂ : ∀{x A B} → x ∉ A ∪ B → x ∉ B
∉∪-lm₂ {A = A} x∉A∪B x∈B = contradiction (∈∪-lm₂ {A = A} x∈B) x∉A∪B


-- Syntax of STLC

data Typ : Set where
  ⊥  : Typ
  _⊃_ : Typ → Typ → Typ

data Exp : Set where
  𝑏𝑣_ : ℕ → Exp
  𝑓𝑣_ : Atom → Exp
  𝜆_  : Exp → Exp
  _$_ : Exp → Exp → Exp

𝜆-inj : ∀{e d} → e ≡ d → 𝜆 e ≡ 𝜆 d
𝜆-inj = ≡-cong 𝜆_

$-inj : ∀{e₁ e₂ d₁ d₂} → e₁ ≡ d₁ → e₂ ≡ d₂ → e₁ $ e₂ ≡ d₁ $ d₂
$-inj = ≡-cong₂ _$_


module Demo₁ where
  Y : Atom
  Y = Atom.atom 0

  demo-rep₁ : Exp
  demo-rep₁ = 𝜆 𝑓𝑣 Y $ 𝑏𝑣 0

  demo-rep₂ : Exp
  demo-rep₂ = 𝜆 𝜆 𝑏𝑣 0 $ 𝑏𝑣 1

  demo-rep₃ : Exp
  demo-rep₃ = 𝜆 𝜆 𝑏𝑣 1 $ (𝑏𝑣 1 $ 𝑏𝑣 0)


-- Substitution

subst : (z : Atom) (u e : Exp) → Exp
subst z u (𝑏𝑣 i)    = 𝑏𝑣 i
subst z u (𝑓𝑣 x) with x ≟ z
...                 | yes x≡z = u
...                 | no  x≢z = 𝑓𝑣 x
subst z u (𝜆 e)     = 𝜆 (subst z u e)
subst z u (e₁ $ e₂) = subst z u e₁ $ subst z u e₂

syntax subst z u e = [ z ↦ u ] e


module Demo₂ where
  open Demo₁

  Z : Atom
  Z = 𝜄 1

  demo-subst : ([ Y ↦ 𝑓𝑣 Z ] 𝜆 𝑏𝑣 0 $ 𝑓𝑣 Y) ≡ 𝜆 𝑏𝑣 0 $ 𝑓𝑣 Z
  demo-subst = ≡-refl


-- Free variables

FV : (e : Exp) → Atoms
FV (𝑏𝑣 x)    = []
FV (𝑓𝑣 x)    = [ x ]
FV (𝜆 e)     = FV e
FV (e₁ $ e₂) = FV e₁ ∪ FV e₂


x∈[x] : ∀{x} → x ∈ [ x ]
x∈[x] = here ≡-refl

≡∈-lm : ∀{x y} → x ≡ y → y ∈ [ x ]
≡∈-lm {x} x≡y = ≡-subst (λ z → z ∈ [ x ]) x≡y x∈[x]


subst-fresh : (z : Atom) (u e : Exp) → z ∉ FV e → ([ z ↦ u ] e) ≡ e
subst-fresh z u (𝑏𝑣 i)    z∉FVe = ≡-refl
subst-fresh z u (𝑓𝑣 x)    z∉FVe with x ≟ z
...                                | yes x≡z = contradiction (≡∈-lm x≡z) z∉FVe
...                                | no  x≢z = ≡-refl
subst-fresh z u (𝜆 e)     z∉FVe = 𝜆-inj (subst-fresh z u e z∉FVe)
subst-fresh z u (e₁ $ e₂) z∉FVe = $-inj (subst-fresh z u e₁ (∉∪-lm₁ z∉FVe))
                                        (subst-fresh z u e₂ (∉∪-lm₂ {A = FV e₁} z∉FVe))


-- Opening

open-rec : (k : ℕ) (u e : Exp) → Exp
open-rec k u (𝑏𝑣 i) with k Data.Nat.≟ i
...                    | yes k≡i = u
...                    | no  k≢i = 𝑏𝑣 i
open-rec k u (𝑓𝑣 x)    = 𝑓𝑣 x
open-rec k u (𝜆 e)     = 𝜆 open-rec (suc k) u e
open-rec k u (e₁ $ e₂) = open-rec k u e₁ $ open-rec k u e₂
