{-# OPTIONS --rewriting #-}

module Prelude where

open import Agda.Primitive public
  using (Level ; _⊔_ ; lsuc)


-- Truth.

record ⊤ {ℓ} : Set ℓ where
  instance
    constructor ∅
{-# BUILTIN UNIT ⊤ #-}


-- Predicates.

Pred : ∀ {ℓ} → Set ℓ → (ℓ′ : Level) → Set (ℓ ⊔ lsuc ℓ′)
Pred X ℓ′ = X → Set ℓ′


-- Falsehood.

data ⊥ : Set where

elim⊥ : ∀ {ℓ} {X : Set ℓ} → ⊥ → X
elim⊥ ()


-- Negation.

infix 3 ¬_
¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ X = X → ⊥

_↯_ : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → X → ¬ X → Y
p ↯ ¬p = elim⊥ (¬p p)


-- Built-in implication.

refl→ : ∀ {ℓ} {X : Set ℓ} → X → X
refl→ x = x

trans→ : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
            (Y → Z) → (X → Y) → X → Z
trans→ g f x = g (f x)

id = refl→

infixr 9 _∘_
_∘_ = trans→


-- Built-in equality.

infix 4 _≡_
data _≡_ {ℓ} {X : Set ℓ} (A : X) : X → Set ℓ where
  instance
    refl : A ≡ A
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE _≡_ #-}

infix 4 _≢_
_≢_ : ∀ {ℓ} {X : Set ℓ} → X → X → Set ℓ
x ≢ x′ = ¬ (x ≡ x′)

trans : ∀ {ℓ} {X : Set ℓ} {x x′ x″ : X} →
          x ≡ x′ → x′ ≡ x″ → x ≡ x″
trans refl refl = refl

sym : ∀ {ℓ} {X : Set ℓ} {x x′ : X} →
        x ≡ x′ → x′ ≡ x
sym refl = refl

subst : ∀ {ℓ ℓ′} {X : Set ℓ} → (P : Pred X ℓ′) →
        ∀ {x x′} → x ≡ x′ → P x → P x′
subst P refl p = p

cong : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} {x x′} →
         (f : X → Y) → x ≡ x′ →
         f x ≡ f x′
cong f refl = refl

cong² : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} {x y x′ y′} →
          (f : X → Y → Z) → x ≡ x′ → y ≡ y′ →
          f x y ≡ f x′ y′
cong² f refl refl = refl

cong³ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″}
            {A : Set ℓ‴} {x y z x′ y′ z′} →
          (f : X → Y → Z → A) → x ≡ x′ → y ≡ y′ → z ≡ z′ →
          f x y z ≡ f x′ y′ z′
cong³ f refl refl refl = refl


-- Equational reasoning with built-in equality.

module ≡-Reasoning {ℓ} {X : Set ℓ} where
  infix 1 begin_
  begin_ : ∀ {x x′ : X} → x ≡ x′ → x ≡ x′
  begin p = p

  infixr 2 _≡⟨⟩_
  _≡⟨⟩_ : ∀ (x {x′} : X) → x ≡ x′ → x ≡ x′
  x ≡⟨⟩ p = p

  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ : ∀ (x {x′ x″} : X) → x ≡ x′ → x′ ≡ x″ → x ≡ x″
  x ≡⟨ p ⟩ q = trans p q

  infix 3 _∎
  _∎ : ∀ (x : X) → x ≡ x
  x ∎ = refl


-- Strong existence.

infixl 5 _,_
record Σ {ℓ ℓ′} (X : Set ℓ) (P : Pred X ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field
    π₁ : X
    π₂ : P π₁
open Σ public

infixl 4 _⁏_
pattern _⁏_ x y = x , y

∃ : ∀ {ℓ ℓ′} {X : Set ℓ} → Pred X ℓ′ → Set (ℓ ⊔ ℓ′)
∃ = Σ _

mapΣ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} {X : Set ℓ} {Y : Set ℓ″}
           {P : Pred X ℓ′} {Q : Pred Y ℓ‴}
         (f : X → Y) (g : ∀ {x} → P x → Q (f x)) →
         Σ X P → Σ Y Q
mapΣ f g (x , y) = f x , g y


-- Conjunction.

infixl 2 _∧_
_∧_ : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
X ∧ Y = Σ X (λ x → Y)

curry : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
          ((X ∧ Y) → Z) → X → Y → Z
curry f x y = f (x , y)

uncurry : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
            (X → Y → Z) → (X ∧ Y) → Z
uncurry f (x , y) = f x y


-- Disjunction.

infixl 1 _∨_
data _∨_ {ℓ ℓ′} (X : Set ℓ) (Y : Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  ι₁ : X → X ∨ Y
  ι₂ : Y → X ∨ Y

injι₁ : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} {x x′ : X} → ι₁ {Y = Y} x ≡ ι₁ x′ → x ≡ x′
injι₁ refl = refl

injι₂ : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} {y y′ : Y} → ι₂ {X = X} y ≡ ι₂ y′ → y ≡ y′
injι₂ refl = refl

elim∨ : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
          X ∨ Y → (X → Z) → (Y → Z) → Z
elim∨ (ι₁ x) f g = f x
elim∨ (ι₂ y) f g = g y


-- Equivalence.

infix 3 _↔_
_↔_ : ∀ {ℓ ℓ′} → (X : Set ℓ) (Y : Set ℓ′) → Set (ℓ ⊔ ℓ′)
X ↔ Y = (X → Y) ∧ (Y → X)

infix 3 _↮_
_↮_ : ∀ {ℓ ℓ′} → (X : Set ℓ) (Y : Set ℓ′) → Set (ℓ ⊔ ℓ′)
X ↮ Y = ¬ (X ↔ Y)

refl↔ : ∀ {ℓ} {X : Set ℓ} → X ↔ X
refl↔ = refl→ , refl→

trans↔ : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
          (X ↔ Y) → (Y ↔ Z) → (X ↔ Z)
trans↔ (P , Q) (P′ , Q′) = trans→ P′ P , trans→ Q Q′

sym↔ : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → X ↔ Y → Y ↔ X
sym↔ (P , Q) = Q , P

antisym→ : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} →
            ((X → Y) ∧ (Y → X)) ≡ (X ↔ Y)
antisym→ = refl

≡→↔ : ∀ {ℓ} {X Y : Set ℓ} → X ≡ Y → X ↔ Y
≡→↔ refl = refl↔


-- Equational reasoning with equivalence.

module ↔-Reasoning where
  infix 1 begin_
  begin_ : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → X ↔ Y → X ↔ Y
  begin P = P

  infixr 2 _↔⟨⟩_
  _↔⟨⟩_ : ∀ {ℓ ℓ′} → (X : Set ℓ) → {Y : Set ℓ′} → X ↔ Y → X ↔ Y
  X ↔⟨⟩ P = P

  infixr 2 _↔⟨_⟩_
  _↔⟨_⟩_ : ∀ {ℓ ℓ′ ℓ″} → (X : Set ℓ) → {Y : Set ℓ′} {Z : Set ℓ″} →
            X ↔ Y → Y ↔ Z → X ↔ Z
  X ↔⟨ P ⟩ Q = trans↔ P Q

  infix 3 _∎
  _∎ : ∀ {ℓ} → (X : Set ℓ) → X ↔ X
  X ∎ = refl↔


-- Decidability.

data Dec {ℓ} (X : Set ℓ) : Set ℓ where
  yes : X → Dec X
  no  : ¬ X → Dec X

injyesDec : ∀ {ℓ} {X : Set ℓ} {x x′ : X} → yes x ≡ yes x′ → x ≡ x′
injyesDec refl = refl

injnoDec : ∀ {ℓ} {X : Set ℓ} {¬x ¬x′ : ¬ X} → no ¬x ≡ no ¬x′ → ¬x ≡ ¬x′
injnoDec refl = refl


-- Function extensionality.

postulate
  fex : ∀ {ℓ ℓ′} {X : Set ℓ} {P : Pred X ℓ′} {f g : ∀ x → P x} →
          (∀ x → f x ≡ g x) →
          f ≡ g

unfex : ∀ {ℓ ℓ′} {X : Set ℓ} {P : Pred X ℓ′} {f g : ∀ x → P x} →
          f ≡ g →
          (∀ x → f x ≡ g x)
unfex refl = λ x → refl

postulate
  fex′ : ∀ {ℓ ℓ′} {X : Set ℓ} {P : Pred X ℓ′} {f g : ∀ {x} → P x} →
           (∀ {x} → f {x} ≡ g {x}) →
           (λ {x} → f {x}) ≡ (λ {x} → g {x})

unfex′ : ∀ {ℓ ℓ′} {X : Set ℓ} {P : Pred X ℓ′} {f g : ∀ {x} → P x} →
           (λ {x} → f {x}) ≡ (λ {x} → g {x}) →
           (∀ {x} → f {x} ≡ g {x})
unfex′ refl = refl


-- Instance resolution.

it : ∀ {ℓ} {X : Set ℓ} {{_ : X}} → X
it {{x}} = x


-- Booleans.

data Bool : Set where
  instance
    false : Bool
    true  : Bool
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}

elimBool : ∀ {ℓ} {X : Set ℓ} → Bool → X → X → X
elimBool false z s = z
elimBool true  z s = s


-- Options.

data Maybe {ℓ} (X : Set ℓ) : Set ℓ where
  nothing : Maybe X
  just    : X → Maybe X

injjustMaybe : ∀ {ℓ} {X : Set ℓ} {x x′ : X} → just x ≡ just x′ → x ≡ x′
injjustMaybe refl = refl

elimMaybe : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → Maybe X → Y → (X → Y) → Y
elimMaybe nothing  z f = z
elimMaybe (just x) z f = f x


-- Naturals.

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

injsucNat : ∀ {n n′} → Nat.suc n ≡ suc n′ → n ≡ n′
injsucNat refl = refl

_≟Nat_ : (n n′ : Nat) → Dec (n ≡ n′)
zero  ≟Nat zero   = yes refl
zero  ≟Nat suc n′ = no λ ()
suc n ≟Nat zero   = no λ ()
suc n ≟Nat suc n′ with n ≟Nat n′
suc n ≟Nat suc n′ | yes refl = yes refl
suc n ≟Nat suc n′ | no n≢n′  = no (n≢n′ ∘ injsucNat)

elimNat : ∀ {ℓ} {X : Set ℓ} → Nat → X → (Nat → X → X) → X
elimNat zero    z f = z
elimNat (suc n) z f = f n (elimNat n z f)


-- Partial orders on naturals.

infix 3 _≥_
data _≥_ : Nat → Nat → Set where
  done : zero ≥ zero
  weak : ∀ {n n′} → n′ ≥ n → suc n′ ≥ n
  lift : ∀ {n n′} → n′ ≥ n → suc n′ ≥ suc n

injweak≥ : ∀ {n n′} {e e′ : n′ ≥ n} → weak e ≡ weak e′ → e ≡ e′
injweak≥ refl = refl

injlift≥ : ∀ {n n′} {e e′ : n′ ≥ n} → lift e ≡ lift e′ → e ≡ e′
injlift≥ refl = refl

_≟≥_ : ∀ {n n′} → (e e′ : n′ ≥ n) → Dec (e ≡ e′)
done   ≟≥ done    = yes refl
weak e ≟≥ weak e′ with e ≟≥ e′
weak e ≟≥ weak .e | yes refl = yes refl
weak e ≟≥ weak e′ | no e≢e′  = no (e≢e′ ∘ injweak≥)
weak e ≟≥ lift e′ = no λ ()
lift e ≟≥ weak e′ = no λ ()
lift e ≟≥ lift e′ with e ≟≥ e′
lift e ≟≥ lift e′ | yes refl = yes refl
lift e ≟≥ lift e′ | no e≢e′  = no (e≢e′ ∘ injlift≥)

unweak≥ : ∀ {n n′} → n′ ≥ suc n → n′ ≥ n
unweak≥ (weak e) = weak (unweak≥ e)
unweak≥ (lift e) = weak e

unlift≥ : ∀ {n n′} → suc n′ ≥ suc n → n′ ≥ n
unlift≥ (weak e) = unweak≥ e
unlift≥ (lift e) = e

inf≥ : ∀ {n} → n ≥ zero
inf≥ {zero}  = done
inf≥ {suc n} = weak inf≥

refl≥ : ∀ {n} → n ≥ n
refl≥ {zero}  = done
refl≥ {suc n} = lift refl≥

trans≥ : ∀ {n n′ n″} → n″ ≥ n′ → n′ ≥ n → n″ ≥ n
trans≥ done      e        = e
trans≥ (weak e′) e        = weak (trans≥ e′ e)
trans≥ (lift e′) (weak e) = weak (trans≥ e′ e)
trans≥ (lift e′) (lift e) = lift (trans≥ e′ e)

idtrans≥₁ : ∀ {n n′} → (e : n′ ≥ n) → trans≥ refl≥ e ≡ e
idtrans≥₁ done     = refl
idtrans≥₁ (weak e) = cong weak (idtrans≥₁ e)
idtrans≥₁ (lift e) = cong lift (idtrans≥₁ e)

idtrans≥₂ : ∀ {n n′} → (e : n′ ≥ n) → trans≥ e refl≥ ≡ e
idtrans≥₂ done     = refl
idtrans≥₂ (weak e) = cong weak (idtrans≥₂ e)
idtrans≥₂ (lift e) = cong lift (idtrans≥₂ e)

assoctrans≥ : ∀ {n n′ n″ n‴} → (e″ : n‴ ≥ n″) (e′ : n″ ≥ n′) (e : n′ ≥ n) →
                trans≥ e″ (trans≥ e′ e) ≡ trans≥ (trans≥ e″ e′) e
assoctrans≥ done      e′        e        = refl
assoctrans≥ (weak e″) e′        e        = cong weak (assoctrans≥ e″ e′ e)
assoctrans≥ (lift e″) (weak e′) e        = cong weak (assoctrans≥ e″ e′ e)
assoctrans≥ (lift e″) (lift e′) (weak e) = cong weak (assoctrans≥ e″ e′ e)
assoctrans≥ (lift e″) (lift e′) (lift e) = cong lift (assoctrans≥ e″ e′ e)


-- Finite naturals.

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

injsucFin : ∀ {n} {i i′ : Fin n} → Fin.suc i ≡ suc i′ → i ≡ i′
injsucFin refl = refl

_≟Fin_ : ∀ {n} → (i i′ : Fin n) → Dec (i ≡ i′)
zero  ≟Fin zero   = yes refl
zero  ≟Fin suc i′ = no λ ()
suc i ≟Fin zero   = no λ ()
suc i ≟Fin suc i′ with i ≟Fin i′
suc i ≟Fin suc i′ | yes refl = yes refl
suc i ≟Fin suc i′ | no i≢i′  = no (i≢i′ ∘ injsucFin)

monoFin : ∀ {n n′} → n′ ≥ n → Fin n → Fin n′
monoFin done     ()
monoFin (weak e) i       = suc (monoFin e i)
monoFin (lift e) zero    = zero
monoFin (lift e) (suc i) = suc (monoFin e i)

injmonoFin : ∀ {n n′} → (e : n′ ≥ n) (i i′ : Fin n) →
               monoFin e i ≡ monoFin e i′ → i ≡ i′
injmonoFin done     ()      ()
injmonoFin (weak e) i       i′       p = injmonoFin e i i′ (injsucFin p)
injmonoFin (lift e) zero    zero     p = refl
injmonoFin (lift e) zero    (suc i′) ()
injmonoFin (lift e) (suc i) zero     ()
injmonoFin (lift e) (suc i) (suc i′) p = cong suc (injmonoFin e i i′ (injsucFin p))

idmonoFin : ∀ {n} → (i : Fin n) → monoFin refl≥ i ≡ i
idmonoFin zero    = refl
idmonoFin (suc i) = cong suc (idmonoFin i)

assocmonoFin : ∀ {n n′ n″} → (e′ : n″ ≥ n′) (e : n′ ≥ n) (i : Fin n) →
                 monoFin e′ (monoFin e i) ≡ monoFin (trans≥ e′ e) i
assocmonoFin done      e        i       = idmonoFin (monoFin e i)
assocmonoFin (weak e′) e        i       = cong suc (assocmonoFin e′ e i)
assocmonoFin (lift e′) (weak e) i       = cong suc (assocmonoFin e′ e i)
assocmonoFin (lift e′) (lift e) zero    = refl
assocmonoFin (lift e′) (lift e) (suc i) = cong suc (assocmonoFin e′ e i)
