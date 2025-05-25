-- 2025-03-21
-- Friedman’s A-Translation
-- https://www.mscs.dal.ca/~selinger/papers/friedman.pdf
-- thanks to roconnor, ncf, and drvink
-- first-order predicate logic with one sort (naturals) and one predicate (equality)
-- variant with first-order structures for renaming and substitution

-- {-# OPTIONS --without-K #-}

module Selinger92 where

open import Agda.Builtin.Equality public
  using (_≡_ ; refl)

open import Agda.Builtin.FromNat public
  using (Number ; fromNat)

open import Agda.Builtin.Nat public
  using (Nat ; zero ; suc ; _+_ ; _-_ ; _*_)

open import Agda.Primitive public
  using (Setω)

open import Agda.Builtin.Sigma public
  using (Σ ; fst ; snd)
  renaming (_,_ to sig)

open import Agda.Builtin.Unit public
  using (⊤ ; tt)

open import Agda.Primitive public
  using (Level ; _⊔_ ; lzero ; lsuc)


----------------------------------------------------------------------------------------------------

-- 0.0. tiny prelude

module Hidden where
  id : ∀ {𝓍} {X : Set 𝓍} → X → X
  id x = x

  flip : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : X → Y → Set 𝓏} →
           (∀ x y → Z x y) → (∀ y x → Z x y)
  flip f y x = f x y

  infixr 9 _∘_
  _∘_ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : X → Set 𝓎} {Z : ∀ {x} → Y x → Set 𝓏}
          (f : ∀ {x} (y : Y x) → Z y) (g : ∀ x → Y x) →
          ∀ x → Z (g x)
  (f ∘ g) x = f (g x)

data ⊥ : Set where

infix 3 ¬_
¬_ : ∀ {𝓍} (X : Set 𝓍) → Set 𝓍
¬ X = X → ⊥

abort : ∀ {𝓍} {X : Set 𝓍} → ⊥ → X
abort ()

_↯_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → X → ¬ X → Y
x ↯ ¬x = abort (¬x x)

infixr 1 _∨_
data _∨_ {𝓍 𝓎} (X : Set 𝓎) (Y : Set 𝓎) : Set (𝓍 ⊔ 𝓎) where
  left  : ∀ (x : X) → X ∨ Y
  right : ∀ (y : Y) → X ∨ Y

data Dec {𝓍} (X : Set 𝓍) : Set 𝓍 where
  yes : ∀ (x : X) → Dec X
  no  : ∀ (¬x : ¬ X) → Dec X

module _ {𝓍} {X : Set 𝓍} where
  True : Dec X → Set
  True (yes x) = ⊤
  True (no ¬x) = ⊥

  toWitness : {X? : Dec X} → True X? → X
  toWitness {X?} p  with X?
  toWitness {X?} p  | yes x = x
  toWitness {X?} () | no ¬x

  fromWitness : {X? : Dec X} → X → True X?
  fromWitness {X?} x with X?
  fromWitness {X?} x | yes _ = tt
  fromWitness {X?} x | no ¬x = x ↯ ¬x

-- TODO: replace this with specific instances
uip : ∀ {𝓍} {X : Set 𝓍} {x ^x : X} (p₁ p₂ : x ≡ ^x) → p₁ ≡ p₂
uip refl refl = refl
{-# INLINE uip #-}

-- numeric literals for naturals
instance
  literalNat : Number Nat
  literalNat = record
    { Constraint = λ n → ⊤
    ; fromNat    = λ n {{p}} → n
    }


----------------------------------------------------------------------------------------------------

-- 0.1. propositional equality

≡-syntax : ∀ {𝓍} (X : Set 𝓍) → X → X → Set 𝓍
≡-syntax X = _≡_

infix 4 ≡-syntax
syntax ≡-syntax X x ^x = x ≡ ^x :> X

infix 9 _⁻¹
_⁻¹ : ∀ {𝓍} {X : Set 𝓍} {x ^x : X} → x ≡ ^x → ^x ≡ x
refl ⁻¹ = refl

infixr 4 _⋮_
_⋮_ : ∀ {𝓍} {X : Set 𝓍} {x ^x ^^x : X} → x ≡ ^x → ^x ≡ ^^x → x ≡ ^^x
refl ⋮ refl = refl

infixl 9 _&_
_&_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (f : X → Y) {x ^x} → x ≡ ^x → f x ≡ f ^x
f & refl = refl

infixl 8 _⊗_
_⊗_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {f g : X → Y} {x ^x} → f ≡ g → x ≡ ^x → f x ≡ g ^x
refl ⊗ refl = refl

congapp : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} {f g : ∀ x → Y x} → f ≡ g → (∀ x → f x ≡ g x)
congapp refl x = refl

congapp′ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} {f g : ∀ {x} → Y x} → f ≡ g :> (∀ {x} → Y x) →
           (∀ {x} → f {x} ≡ g {x})
congapp′ refl {x} = refl

Funext : Setω
Funext = ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} {f g : ∀ x → Y x} → (∀ x → f x ≡ g x) → f ≡ g

Funext′ : Setω
Funext′ = ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} {f g : ∀ {x} → Y x} → (∀ {x} → f {x} ≡ g {x}) →
          f ≡ g :> (∀ {x} → Y x)

implify : Funext → Funext′
implify fe eq = (λ f {x} → f x) & fe (λ x → eq {x})

module ≡-Reasoning where
  infix  3 _∎
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_ _≡⟨_⟩⁻¹_
  infix  1 begin_

  begin_ : ∀ {𝓍} {X : Set 𝓍} {x ^x : X} → x ≡ ^x → x ≡ ^x
  begin p = p

  _≡⟨⟩_ : ∀ {𝓍} {X : Set 𝓍} (x : X) {^x : X} → x ≡ ^x → x ≡ ^x
  x ≡⟨⟩ p = p

  _≡⟨_⟩_ : ∀ {𝓍} {X : Set 𝓍} (x : X) {^x ^^x} → x ≡ ^x → ^x ≡ ^^x → x ≡ ^^x
  x ≡⟨ p ⟩ q = p ⋮ q

  _≡⟨_⟩⁻¹_ : ∀ {𝓍} {X : Set 𝓍} (x : X) {^x ^^x} → ^x ≡ x → ^x ≡ ^^x → x ≡ ^^x
  x ≡⟨ p ⟩⁻¹ q = p ⁻¹ ⋮ q

  _∎ : ∀ {𝓍} {X : Set 𝓍} (x : X) → x ≡ x
  x ∎ = refl


----------------------------------------------------------------------------------------------------

-- 0.2. heterogeneous equality

-- infix 4 _≅_
-- data _≅_ {𝓍} {X : Set 𝓍} (x : X) : ∀ {𝓎} {Y : Set 𝓎} → Y → Set 𝓍 where
--    refl : x ≅ x
--
-- infix 9 _ʰ⁻¹
-- _ʰ⁻¹ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {x : X} {y : Y} → x ≅ y → y ≅ x
-- refl ʰ⁻¹ = refl
--
-- infixr 4 _ʰ⋮_
-- _ʰ⋮_ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : Set 𝓏} {x : X} {y : Y} {z : Z} →
--          x ≅ y → y ≅ z → x ≅ z
-- refl ʰ⋮ refl = refl
--
-- infixl 9 _ʰ&_
-- _ʰ&_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} (f : ∀ x → Y x) {x ^x} → x ≅ ^x → f x ≅ f ^x
-- f ʰ& refl = refl
--
-- infixl 8 _ʰ⊗_
-- _ʰ⊗_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} {f g : ∀ x → Y x} {x ^x} → f ≅ g → x ≅ ^x →
--          f x ≅ g ^x
-- refl ʰ⊗ refl = refl
--
-- ≅→≡ : ∀ {𝓍} {X : Set 𝓍} {x ^x : X} → x ≅ ^x → x ≡ ^x
-- ≅→≡ refl = refl
--
-- ≡→≅ : ∀ {𝓍} {X : Set 𝓍} {x ^x : X} → x ≡ ^x → x ≅ ^x
-- ≡→≅ refl = refl
--
-- module ≅-Reasoning where
--   infix  3 _∎
--   infixr 2 _≅⟨⟩_ _≅⟨_⟩_ _≡⟨_⟩_
--   infix  1 begin_
--
--   begin_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {x : X} {y : Y} → x ≅ y → x ≅ y
--   begin p = p
--
--   _≅⟨⟩_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (x : X) {y : Y} → x ≅ y → x ≅ y
--   x ≅⟨⟩ p = p
--
--   _≅⟨_⟩_ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : Set 𝓏} (x : X) {y : Y} {z : Z} →
--              x ≅ y → y ≅ z → x ≅ z
--   x ≅⟨ p ⟩ q = p ʰ⋮ q
--
--   _≡⟨⟩_ : ∀ {𝓍} {X : Set 𝓍} (x : X) {^x} → x ≡ ^x → x ≅ ^x
--   x ≡⟨⟩ p = ≡→≅ p
--
--   _≡⟨_⟩_ : ∀ {𝓍 𝓏} {X : Set 𝓍} {Z : Set 𝓏} (x : X) {^x} {z : Z} →
--              x ≡ ^x → ^x ≅ z → x ≅ z
--   x ≡⟨ p ⟩ q = ≡→≅ p ʰ⋮ q
--
--   _∎ : ∀ {𝓍} {X : Set 𝓍} (x : X) → x ≅ x
--   x ∎ = refl


----------------------------------------------------------------------------------------------------

-- 0.3. tiny naive category theory

record Category (ℴ 𝓂 : Level) : Set (lsuc (ℴ ⊔ 𝓂)) where
  field
    Obj  : Set ℴ
    _▻_  : ∀ (x y : Obj) → Set 𝓂
    id   : ∀ {x} → x ▻ x
    _∘_  : ∀ {x y z} (q : y ▻ z) (p : x ▻ y) → x ▻ z
    lid▻ : ∀ {x y} (p : y ▻ x) → id ∘ p ≡ p
    rid▻ : ∀ {x y} (p : y ▻ x) → p ∘ id ≡ p
    ass▻ : ∀ {w x y z} (r : y ▻ z) (q : x ▻ y) (p : w ▻ x) → r ∘ (q ∘ p) ≡ (r ∘ q) ∘ p

  _◅_ : ∀ (y x : Obj) → Set 𝓂
  y ◅ x = x ▻ y

  _⨾_ : ∀ {x y z} (p : x ▻ y) (q : y ▻ z) → x ▻ z
  p ⨾ q = q ∘ p

  field
    ◅ssa : ∀ {w x y z} (r : y ◅ z) (q : x ◅ y) (p : w ◅ x) → r ⨾ (q ⨾ p) ≡ (r ⨾ q) ⨾ p

_ᵒᵖ : ∀ {ℴ 𝓂} (C : Category ℴ 𝓂) → Category ℴ 𝓂
_ᵒᵖ C = record
    { Obj  = C.Obj
    ; _▻_  = Hidden.flip C._▻_
    ; id   = C.id
    ; _∘_  = Hidden.flip C._∘_
    ; lid▻ = C.rid▻
    ; rid▻ = C.lid▻
    ; ass▻ = C.◅ssa
    ; ◅ssa = C.ass▻
    }
  where
    private
      module C = Category C

catSet : ∀ (𝓍 : Level) → Category (lsuc 𝓍) 𝓍
catSet 𝓍 = record
    { Obj  = Set 𝓍
    ; _▻_  = λ X Y → X → Y
    ; id   = Hidden.id
    ; _∘_  = λ q p → q Hidden.∘ p
    ; lid▻ = λ p → refl
    ; rid▻ = λ p → refl
    ; ass▻ = λ r q p → refl
    ; ◅ssa = λ r q p → refl
    }

catSet₀ : Category (lsuc lzero) lzero
catSet₀ = catSet lzero

record Functor {ℴ₁ ℴ₂ 𝓂₁ 𝓂₂} (C : Category ℴ₁ 𝓂₁) (D : Category ℴ₂ 𝓂₂) :
    Set (ℴ₁ ⊔ ℴ₂ ⊔ 𝓂₁ ⊔ 𝓂₂) where
  private
    module C = Category C
    module D = Category D

  field
    ƒObj : ∀ (x : C.Obj) → D.Obj
    ƒ    : ∀ {x y} (p : x C.▻ y) → (ƒObj x) D.▻ (ƒObj y)
    idƒ  : ∀ {x} → ƒ C.id ≡ D.id :> (ƒObj x D.▻ ƒObj x)
    _∘ƒ_ : ∀ {x y z} (q : y C.▻ z) (p : x C.▻ y) → ƒ (q C.∘ p) ≡ (ƒ q) D.∘ (ƒ p)

  -- opposite
  op : Functor (C ᵒᵖ) (D ᵒᵖ)
  op = record
         { ƒObj = ƒObj
         ; ƒ    = ƒ
         ; idƒ  = idƒ
         ; _∘ƒ_ = Hidden.flip _∘ƒ_
         }

ƒId : ∀ {ℴ 𝓂} (C : Category ℴ 𝓂) → Functor C C
ƒId C = record
          { ƒObj = Hidden.id
          ; ƒ    = Hidden.id
          ; idƒ  = refl
          ; _∘ƒ_ = λ q p → refl
          }

Presheaf : ∀ {ℴ 𝓂} (C : Category ℴ 𝓂) (𝓍 : Level) → Set (ℴ ⊔ 𝓂 ⊔ lsuc 𝓍)
Presheaf C 𝓍 = Functor (C ᵒᵖ) (catSet 𝓍)


----------------------------------------------------------------------------------------------------

-- 0.4. term variables

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} (i : Fin n) → Fin (suc n)

-- order-preserving embeddings
infix 3 _≤_
data _≤_ : Nat → Nat → Set where
  stop  : zero ≤ zero
  wk≤   : ∀ {k k′} (η : k ≤ k′) → k ≤ suc k′
  lift≤ : ∀ {k k′} (η : k ≤ k′) → suc k ≤ suc k′

id≤ : ∀ {k} → k ≤ k
id≤ {k = zero}  = stop
id≤ {k = suc k} = lift≤ id≤

infixr 9 _∘≤_
_∘≤_ : ∀ {k k′ k″} → k′ ≤ k″ → k ≤ k′ → k ≤ k″
stop     ∘≤ η       = η
wk≤ η′   ∘≤ η       = wk≤ (η′ ∘≤ η)
lift≤ η′ ∘≤ wk≤ η   = wk≤ (η′ ∘≤ η)
lift≤ η′ ∘≤ lift≤ η = lift≤ (η′ ∘≤ η)

lid≤ : ∀ {k k′} (η : k ≤ k′) → id≤ ∘≤ η ≡ η
lid≤ stop      = refl
lid≤ (wk≤ η)   = wk≤ & lid≤ η
lid≤ (lift≤ η) = lift≤ & lid≤ η

rid≤ : ∀ {k k′} (η : k ≤ k′) → η ∘≤ id≤ ≡ η
rid≤ stop      = refl
rid≤ (wk≤ η)   = wk≤ & rid≤ η
rid≤ (lift≤ η) = lift≤ & rid≤ η

ass≤ : ∀ {k k′ k″ k‴} (η″ : k″ ≤ k‴) (η′ : k′ ≤ k″) (η : k ≤ k′) →
         η″ ∘≤ (η′ ∘≤ η) ≡ (η″ ∘≤ η′) ∘≤ η
ass≤ stop       η′         η         = refl
ass≤ (wk≤ η″)   η′         η         = wk≤ & ass≤ η″ η′ η
ass≤ (lift≤ η″) (wk≤ η′)   η         = wk≤ & ass≤ η″ η′ η
ass≤ (lift≤ η″) (lift≤ η′) (wk≤ η)   = wk≤ & ass≤ η″ η′ η
ass≤ (lift≤ η″) (lift≤ η′) (lift≤ η) = lift≤ & ass≤ η″ η′ η

renFin : ∀ {k k′} → k ≤ k′ → Fin k → Fin k′
renFin stop      i       = i
renFin (wk≤ η)   i       = suc (renFin η i)
renFin (lift≤ η) zero    = zero
renFin (lift≤ η) (suc i) = renFin (wk≤ η) i

wkFin : ∀ {k} → Fin k → Fin (suc k)
wkFin i = renFin (wk≤ id≤) i

idrenFin : ∀ {k} (i : Fin k) → renFin id≤ i ≡ i
idrenFin zero    = refl
idrenFin (suc i) = suc & idrenFin i

comprenFin : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (i : Fin k) →
               renFin (η′ ∘≤ η) i ≡ renFin η′ (renFin η i)
comprenFin stop       η         i       = refl
comprenFin (wk≤ η′)   η         i       = suc & comprenFin η′ η i
comprenFin (lift≤ η′) (wk≤ η)   i       = suc & comprenFin η′ η i
comprenFin (lift≤ η′) (lift≤ η) zero    = refl
comprenFin (lift≤ η′) (lift≤ η) (suc i) = suc & comprenFin η′ η i

-- casting for term variables
module _ where
  castFin : ∀ {k ^k} → ^k ≡ k → Fin k → Fin ^k
  castFin refl i = i

  castzeroFin : ∀ {k ^k} (p : ^k ≡ k) → zero ≡ castFin (suc & p) zero
  castzeroFin refl = refl

  castsucFin : ∀ {k ^k} (p : ^k ≡ k) (i : Fin k) → suc (castFin p i) ≡ castFin (suc & p) (suc i)
  castsucFin refl zero    = refl
  castsucFin refl (suc i) = suc & castsucFin refl i

  -- casting for order-preserving embeddings
  cast≤ : ∀ {k ^k k′ ^k′} → ^k ≡ k → ^k′ ≡ k′ → k ≤ k′ → ^k ≤ ^k′
  cast≤ refl refl η = η

  castwk≤ : ∀ {k ^k k′ ^k′} (p₁ : ^k ≡ k) (p₂ : ^k′ ≡ k′) (η : k ≤ k′) →
              wk≤ (cast≤ p₁ p₂ η) ≡ cast≤ p₁ (suc & p₂) (wk≤ η)
  castwk≤ refl refl η = refl

  castlift≤ : ∀ {k ^k k′ ^k′} (p₁ : ^k ≡ k) (p₂ : ^k′ ≡ k′) (η : k ≤ k′) →
                lift≤ (cast≤ p₁ p₂ η) ≡ cast≤ (suc & p₁) (suc & p₂) (lift≤ η)
  castlift≤ refl refl η = refl

-- numeric literals for term variables
-- TODO: this actually works; see e.g. `proj 0` later on, but what was the issue further down?
module _ where
  cowk≤ : ∀ {n m} → suc n ≤ m → n ≤ m
  cowk≤ (wk≤ η)   = wk≤ (cowk≤ η)
  cowk≤ (lift≤ η) = wk≤ η

  colift≤ : ∀ {n m} → suc n ≤ suc m → n ≤ m
  colift≤ (wk≤ η)   = cowk≤ η
  colift≤ (lift≤ η) = η

  _≤?_ : ∀ n m → Dec (n ≤ m)
  zero ≤? zero   = yes stop
  zero ≤? suc m  with zero ≤? m
  ... | yes η      = yes (wk≤ η)
  ... | no ¬η      = no λ where (wk≤ η) → η ↯ ¬η
  suc n ≤? zero  = no λ ()
  suc n ≤? suc m with n ≤? m
  ... | yes η      = yes (lift≤ η)
  ... | no ¬η      = no λ where η → colift≤ η ↯ ¬η

  ≤→Fin : ∀ {n m} → suc m ≤ n → Fin n
  ≤→Fin {suc n} {zero}  η = zero
  ≤→Fin {suc n} {suc m} η = suc (≤→Fin (colift≤ η))

  Nat→Fin : ∀ {n} (m : Nat) {{p : True (suc m ≤? n)}} → Fin n
  Nat→Fin {n} m {{p}} = ≤→Fin (toWitness p)

  instance
    literalFin : ∀ {n} → Number (Fin n)
    literalFin {n} = record
      { Constraint = λ m → True (suc m ≤? n)
      ; fromNat    = Nat→Fin
      }

-- TODO: delete this
-- module _ where
--   import Data.Nat as Nat
--   import Data.Fin as Fin
--
--   instance
--     literalFin : ∀ {n} → Number (Fin n)
--     literalFin {n} = record
--       { Constraint = λ m → True (m Nat.<? n)
--       ; fromNat    = λ m {{p}} → (Fin.# m) {n} {p}
--       }


----------------------------------------------------------------------------------------------------

-- 0.5. leftist lists and vectors

infixl 4 _,_
data List {𝓍} (X : Set 𝓍) : Set 𝓍 where
  ∙   : List X
  _,_ : ∀ (ξ : List X) (x : X) → List X

data Vec {𝓍} (X : Set 𝓍) : Nat → Set 𝓍 where
  ∙   : Vec X zero
  _,_ : ∀ {n} (ξ : Vec X n) (x : X) → Vec X (suc n)

module _ {𝓍} {X : Set 𝓍} where
  peek : ∀ {n} → Fin n → Vec X n → X
  peek zero    (ξ , x) = x
  peek (suc i) (ξ , x) = peek i ξ

  poke : ∀ {n} → Fin n → X → Vec X n → Vec X n
  poke zero    w (ξ , x) = ξ , w
  poke (suc i) w (ξ , x) = poke i w ξ , x

  for : ∀ {𝓎} {Y : Set 𝓎} {n} → Vec X n → (X → Y) → Vec Y n
  for ∙       f = ∙
  for (ξ , x) f = for ξ f , f x

  tab : ∀ {n} → (Fin n → X) → Vec X n
  tab {zero}  f = ∙
  tab {suc n} f = tab (λ i → f (suc i)) , f zero


----------------------------------------------------------------------------------------------------

-- 0.6. derivation variables

module _ {𝓍} {X : Set 𝓍} where
  infix 3 _∋_
  data _∋_ : List X → X → Set 𝓍 where
    zero : ∀ {Γ A} → Γ , A ∋ A
    suc  : ∀ {Γ A C} (i : Γ ∋ A) → Γ , C ∋ A

  -- order-preserving embeddings
  infix 3 _⊆_
  data _⊆_ : List X → List X → Set 𝓍 where
    stop  : ∙ ⊆ ∙
    wk⊆   : ∀ {Γ Γ′ C} (η : Γ ⊆ Γ′) → Γ ⊆ Γ′ , C
    lift⊆ : ∀ {Γ Γ′ C} (η : Γ ⊆ Γ′) → Γ , C ⊆ Γ′ , C

  id⊆ : ∀ {Γ} → Γ ⊆ Γ
  id⊆ {Γ = ∙}     = stop
  id⊆ {Γ = Γ , A} = lift⊆ id⊆

  infixr 9 _∘⊆_
  _∘⊆_ : ∀ {Γ Γ′ Γ″} → Γ′ ⊆ Γ″ → Γ ⊆ Γ′ → Γ ⊆ Γ″
  stop     ∘⊆ η       = η
  wk⊆ η′   ∘⊆ η       = wk⊆ (η′ ∘⊆ η)
  lift⊆ η′ ∘⊆ wk⊆ η   = wk⊆ (η′ ∘⊆ η)
  lift⊆ η′ ∘⊆ lift⊆ η = lift⊆ (η′ ∘⊆ η)

  lid⊆ : ∀ {Γ Γ′} (η : Γ ⊆ Γ′) → id⊆ ∘⊆ η ≡ η
  lid⊆ stop      = refl
  lid⊆ (wk⊆ η)   = wk⊆ & lid⊆ η
  lid⊆ (lift⊆ η) = lift⊆ & lid⊆ η

  rid⊆ : ∀ {Γ Γ′} (η : Γ ⊆ Γ′) → η ∘⊆ id⊆ ≡ η
  rid⊆ stop      = refl
  rid⊆ (wk⊆ η)   = wk⊆ & rid⊆ η
  rid⊆ (lift⊆ η) = lift⊆ & rid⊆ η

  ass⊆ : ∀ {Γ Γ′ Γ″ Γ‴} (η″ : Γ″ ⊆ Γ‴) (η′ : Γ′ ⊆ Γ″) (η : Γ ⊆ Γ′) →
           η″ ∘⊆ (η′ ∘⊆ η) ≡ (η″ ∘⊆ η′) ∘⊆ η
  ass⊆ stop       η′         η         = refl
  ass⊆ (wk⊆ η″)   η′         η         = wk⊆ & ass⊆ η″ η′ η
  ass⊆ (lift⊆ η″) (wk⊆ η′)   η         = wk⊆ & ass⊆ η″ η′ η
  ass⊆ (lift⊆ η″) (lift⊆ η′) (wk⊆ η)   = wk⊆ & ass⊆ η″ η′ η
  ass⊆ (lift⊆ η″) (lift⊆ η′) (lift⊆ η) = lift⊆ & ass⊆ η″ η′ η

  ren∋ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ∋ A → Γ′ ∋ A
  ren∋ stop      i       = i
  ren∋ (wk⊆ η)   i       = suc (ren∋ η i)
  ren∋ (lift⊆ η) zero    = zero
  ren∋ (lift⊆ η) (suc i) = suc (ren∋ η i)

  wk∋ : ∀ {Γ A C} → Γ ∋ A → Γ , C ∋ A
  wk∋ i = ren∋ (wk⊆ id⊆) i

  idren∋ : ∀ {Γ A} (i : Γ ∋ A) → ren∋ id⊆ i ≡ i
  idren∋ zero    = refl
  idren∋ (suc i) = suc & idren∋ i

  compren∋ : ∀ {Γ Γ′ Γ″ A} (η′ : Γ′ ⊆ Γ″) (η : Γ ⊆ Γ′) (i : Γ ∋ A) →
               ren∋ (η′ ∘⊆ η) i ≡ ren∋ η′ (ren∋ η i)
  compren∋ stop       η         i       = refl
  compren∋ (wk⊆ η′)   η         i       = suc & compren∋ η′ η i
  compren∋ (lift⊆ η′) (wk⊆ η)   i       = suc & compren∋ η′ η i
  compren∋ (lift⊆ η′) (lift⊆ η) zero    = refl
  compren∋ (lift⊆ η′) (lift⊆ η) (suc i) = suc & compren∋ η′ η i

  -- casting for derivation variables
  module _ where
    cast∋ : ∀ {Γ ^Γ A ^A} → ^Γ ≡ Γ → ^A ≡ A → Γ ∋ A → ^Γ ∋ ^A
    cast∋ refl refl i = i

    castzero∋ : ∀ {Γ ^Γ C ^C} (p : ^Γ ≡ Γ) (q : ^C ≡ C) →
                  zero ≡ cast∋ (_,_ & p ⊗ q) q zero
    castzero∋ refl refl = refl

    castsuc∋ : ∀ {Γ ^Γ A ^A C ^C} (p : ^Γ ≡ Γ) (q₁ : ^C ≡ C) (q₂ : ^A ≡ A) (i : Γ ∋ A) →
                 suc (cast∋ p q₂ i) ≡ cast∋ (_,_ & p ⊗ q₁) q₂ (suc i)
    castsuc∋ refl refl refl zero    = refl
    castsuc∋ refl refl refl (suc i) = suc & castsuc∋ refl refl refl i

    -- casting for order-preserving embeddings
    cast⊆ : ∀ {Γ ^Γ Γ′ ^Γ′} → ^Γ ≡ Γ → ^Γ′ ≡ Γ′ → Γ ⊆ Γ′ → ^Γ ⊆ ^Γ′
    cast⊆ refl refl η = η

    castwk⊆ : ∀ {Γ ^Γ Γ′ ^Γ′ C ^C} (p₁ : ^Γ ≡ Γ) (p₂ : ^Γ′ ≡ Γ′) (q : ^C ≡ C) (η : Γ ⊆ Γ′) →
                wk⊆ (cast⊆ p₁ p₂ η) ≡ cast⊆ p₁ (_,_ & p₂ ⊗ q) (wk⊆ η)
    castwk⊆ refl refl refl η = refl

    castlift⊆ : ∀ {Γ ^Γ Γ′ ^Γ′ C ^C} (p₁ : ^Γ ≡ Γ) (p₂ : ^Γ′ ≡ Γ′) (q : ^C ≡ C) (η : Γ ⊆ Γ′) →
                  lift⊆ (cast⊆ p₁ p₂ η) ≡ cast⊆ (_,_ & p₁ ⊗ q) (_,_ & p₂ ⊗ q) (lift⊆ η)
    castlift⊆ refl refl refl η = refl

  -- numeric literals for derivation variables
  module _ where
    infix 3 _∋⟨_⟩_
    data _∋⟨_⟩_ : List X → Nat → X → Set 𝓍 where
      instance
        zero : ∀ {Γ A} → Γ , A ∋⟨ zero ⟩ A
        suc  : ∀ {m Γ A C} {{i : Γ ∋⟨ m ⟩ A}} → Γ , C ∋⟨ suc m ⟩ A

    ∋#→∋ : ∀ {Γ m A} → Γ ∋⟨ m ⟩ A → Γ ∋ A
    ∋#→∋ zero        = zero
    ∋#→∋ (suc {{i}}) = suc (∋#→∋ i)

    instance
      number∋ : ∀ {Γ A} → Number (Γ ∋ A)
      number∋ {Γ} {A} = record
        { Constraint = λ m → Γ ∋⟨ m ⟩ A
        ; fromNat    = λ m {{p}} → ∋#→∋ p
        }


----------------------------------------------------------------------------------------------------

-- 0.7. primitive recursive n-ary functions on naturals
-- Troelstra (1973) §1.3.4

mutual
  data Prim : Nat → Set where
    zero : Prim 0
    suc  : Prim 1
    proj : ∀ {n} (i : Fin n) → Prim n
    comp : ∀ {n m} (g : Prim m) (φ : Prim§ n m) → Prim n
    rec  : ∀ {n} (f : Prim n) (g : Prim (suc (suc n))) → Prim (suc n)

  Prim§ : Nat → Nat → Set
  Prim§ n m = Vec (Prim n) m

Nat§ : Nat → Set
Nat§ n = Vec Nat n

Fun : Nat → Set
Fun n = Nat§ n → Nat

Fun§ : Nat → Nat → Set
Fun§ n m = Vec (Fun n) m

#zero : Fun 0
#zero ∙ = zero

#suc : Fun 1
#suc (∙ , x) = suc x

#proj : ∀ {n} → Fin n → Fun n
#proj i ξ = peek i ξ

#comp : ∀ {n m} → Fun m → Fun§ n m → Fun n
#comp g φ ξ = g (for φ (λ f → f ξ))

#rec : ∀ {n} → Fun n → Fun (suc (suc n)) → Fun (suc n)
#rec f g (ξ , zero)  = f ξ
#rec f g (ξ , suc x) = g (ξ , x , #rec f g (ξ , x))

mutual
  ⟦_⟧ : ∀ {n} → Prim n → Fun n
  ⟦ zero ⟧     = #zero
  ⟦ suc ⟧      = #suc
  ⟦ proj i ⟧   = #proj i
  ⟦ comp g φ ⟧ = #comp ⟦ g ⟧ ⟦ φ ⟧§
  ⟦ rec f g ⟧  = #rec ⟦ f ⟧ ⟦ g ⟧

  ⟦_⟧§ : ∀ {n m} → Prim§ n m → Fun§ n m
  ⟦ ∙ ⟧§     = ∙
  ⟦ φ , f ⟧§ = ⟦ φ ⟧§ , ⟦ f ⟧


----------------------------------------------------------------------------------------------------

-- 0.8. some primitive recursive n-ary functions on naturals
-- Troelstra and van Dalen (1988) §1.3

module _ where
  private
    const : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → X → Y → X
    const x y = x

  ƒconst : ∀ {n} → Nat → Prim n
  ƒconst zero    = comp zero ∙
  ƒconst (suc x) = comp suc (∙ , ƒconst x)

  testconst : ∀ x → ⟦ ƒconst x ⟧ ∙ ≡ const {Y = Nat§ 0} x ∙
  testconst zero    = refl
  testconst (suc x) = suc & testconst x

  ƒadd : Prim 2
  ƒadd = rec (proj 0)
           (comp suc (∙ , proj 0))

  testadd : ∀ x y → ⟦ ƒadd ⟧ (∙ , y , x) ≡ x + y
  testadd zero    y = refl
  testadd (suc x) y = suc & testadd x y

  ƒmul : Prim 2
  ƒmul = rec (ƒconst 0)
           (comp ƒadd (∙ , proj 0 , proj 2))

  testmul : ∀ x y → ⟦ ƒmul ⟧ (∙ , y , x) ≡ x * y
  testmul zero    y = refl
  testmul (suc x) y = (λ z → ⟦ ƒadd ⟧ (∙ , z , y)) & testmul x y
                    ⋮ testadd y (x * y)

  pred : Nat → Nat
  pred x = x - 1

  ƒpred : Prim 1
  ƒpred = rec (ƒconst 0)
            (proj 1)

  testpred : ∀ x → ⟦ ƒpred ⟧ (∙ , x) ≡ pred x
  testpred zero    = refl
  testpred (suc x) = refl

  -- TODO: subtraction

  -- _-_ : Nat → Nat → Nat
  -- x     - zero  = x
  -- zero  - suc y = zero
  -- suc x - suc y = x - y

  -- _-_ : Nat → Nat → Nat
  -- x - zero  = x
  -- x - suc y = pred (x - y)


----------------------------------------------------------------------------------------------------

-- 0.9. meta-level continuation/double negation monad/applicative/functor
-- TODO: laws?
-- TODO: delete this?
-- module Cont where
--   return : ∀ {𝓍} {X : Set 𝓍} → X → ¬ ¬ X
--   return x = λ k → k x
--
--   infixl 1 _>>=_
--   _>>=_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → ¬ ¬ X → (X → ¬ ¬ Y) → ¬ ¬ Y
--   mx >>= f = (λ k → mx (λ x → f x k))
--
--   join : ∀ {𝓍} {X : Set 𝓍} → ¬ ¬ ¬ ¬ X → ¬ ¬ X
--   join mmx = mmx >>= (λ mx → mx)
--
--   infixl 4 _⊛_
--   _⊛_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → ¬ ¬ (X → Y) → ¬ ¬ X → ¬ ¬ Y
--   mf ⊛ mx = mf >>= (λ f → mx >>= (λ x → return (f x)))
--
--   infixl 4 _<$>_
--   _<$>_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → (X → Y) → ¬ ¬ X → ¬ ¬ Y
--   f <$> mx = return f ⊛ mx
--
--   -- TODO: report bug
--   dnem : ∀ {𝓍} {X : Set 𝓍} → ¬ ¬ (X ∨ ¬ X)
--   dnem = λ k → k (right (λ k′ → k (left k′)))


----------------------------------------------------------------------------------------------------

-- 1.0. terms, indexed by number of term variables

mutual
  data Tm (k : Nat) : Set where
    ‵tvar : ∀ (i : Fin k) → Tm k -- i-th term variable
    ‵fun  : ∀ {n} (f : Prim n) (τ : Tm§ k n) → Tm k

  -- simultaneous substitutions of terms
  Tm§ : Nat → Nat → Set
  Tm§ k n = Vec (Tm k) n

-- numeric literals for terms
-- TODO: delete this?
-- instance
--   numberTm : ∀ {k} → Number (Tm k)
--   numberTm {k} = record
--     { Constraint = λ m → True (m Nat.<? k)
--     ; fromNat    = λ m {{p}} → ‵var ((Fin.# m) {k} {p})
--     }

𝟘 : ∀ {k} → Tm k
𝟘 = ‵fun zero ∙

𝕊 : ∀ {k} → Tm k → Tm k
𝕊 t = ‵fun suc (∙ , t)

-- numeric literals for naturals encoded as object-level primitive recursive functions
-- TODO: delete this?
-- Nat→Tm : ∀ {k} → Nat → Tm k
-- Nat→Tm zero    = 𝟘
-- Nat→Tm (suc m) = 𝕊 (Nat→Tm m)
--
-- instance
--   numberTm : ∀ {k} → Number (Tm k)
--   numberTm {k} = record
--     { Constraint = const ⊤
--     ; fromNat    = λ m {{p}} → Nat→Tm m
--     }


----------------------------------------------------------------------------------------------------

-- 1.1. terms: renaming

mutual
  renTm : ∀ {k k′} → k ≤ k′ → Tm k → Tm k′
  renTm η (‵tvar i)  = ‵tvar (renFin η i)
  renTm η (‵fun f τ) = ‵fun f (renTm§ η τ)

  renTm§ : ∀ {k k′ n} → k ≤ k′ → Tm§ k n → Tm§ k′ n
  renTm§ η ∙       = ∙
  renTm§ η (τ , t) = renTm§ η τ , renTm η t


----------------------------------------------------------------------------------------------------

-- 1.2. terms: generic lemmas from RenKit

wkTm : ∀ {k} → Tm k → Tm (suc k)
wkTm t = renTm (wk≤ id≤) t

wkTm§ : ∀ {k n} → Tm§ k n → Tm§ (suc k) n
wkTm§ τ = renTm§ (wk≤ id≤) τ

liftTm§ : ∀ {k n} → Tm§ k n → Tm§ (suc k) (suc n)
liftTm§ τ = wkTm§ τ , ‵tvar zero

varTm§ : ∀ {k k′} → k ≤ k′ → Tm§ k′ k
varTm§ stop      = ∙
varTm§ (wk≤ η)   = wkTm§ (varTm§ η)
varTm§ (lift≤ η) = liftTm§ (varTm§ η)

-- TODO: check if changing this affects anything
idTm§ : ∀ {k} → Tm§ k k
-- idTm§ {k = zero}  = ∙
-- idTm§ {k = suc k} = liftTm§ idTm§
idTm§ = varTm§ id≤

subFin : ∀ {k m} → Tm§ m k → Fin k → Tm m
subFin (σ , s) zero    = s
subFin (σ , s) (suc i) = subFin σ i

eqrenpeekTm : ∀ {k k′ n} (η : k ≤ k′) (i : Fin n) (τ : Tm§ k n) →
                peek i (renTm§ η τ) ≡ renTm η (peek i τ)
eqrenpeekTm η zero    (τ , t) = refl
eqrenpeekTm η (suc i) (τ , t) = eqrenpeekTm η i τ

eqrenpokeTm : ∀ {k k′ n} (η : k ≤ k′) (i : Fin n) (s : Tm k) (τ : Tm§ k n) →
                poke i (renTm η s) (renTm§ η τ) ≡ renTm§ η (poke i s τ)
eqrenpokeTm η zero    s (τ , t) = refl
eqrenpokeTm η (suc i) s (τ , t) = (_, renTm η t) & eqrenpokeTm η i s τ

eqrenforTm : ∀ {k k′ n m} (η : k ≤ k′) (φ : Prim§ n m) (τ : Tm§ k n) →
               for φ (λ f → ‵fun f (renTm§ η τ)) ≡ renTm§ η (for φ (λ f → ‵fun f τ))
eqrenforTm η ∙       τ = refl
eqrenforTm η (φ , f) τ = (_, ‵fun f (renTm§ η τ)) & eqrenforTm η φ τ


----------------------------------------------------------------------------------------------------

-- 1.3. terms: substitution

mutual
  subTm : ∀ {k m} → Tm§ m k → Tm k → Tm m
  subTm σ (‵tvar i)  = subFin σ i
  subTm σ (‵fun f τ) = ‵fun f (subTm§ σ τ)

  subTm§ : ∀ {k m n} → Tm§ m k → Tm§ k n → Tm§ m n
  subTm§ σ ∙       = ∙
  subTm§ σ (τ , t) = subTm§ σ τ , subTm σ t


----------------------------------------------------------------------------------------------------

-- 1.4. terms: generic lemmas from SubKit

_[_/0]Tm : ∀ {k} → Tm (suc k) → Tm k → Tm k
t [ s /0]Tm = subTm (idTm§ , s) t

_[_/1]Tm : ∀ {k} → Tm (suc (suc k)) → Tm (suc k) → Tm (suc k)
t [ s /1]Tm = subTm (wkTm§ idTm§ , s , ‵tvar zero) t

getTm§ : ∀ {k n n′} → n ≤ n′ → Tm§ k n′ → Tm§ k n
getTm§ stop      τ       = τ
getTm§ (wk≤ η)   (τ , t) = getTm§ η τ
getTm§ (lift≤ η) (τ , t) = getTm§ η τ , t


----------------------------------------------------------------------------------------------------

-- 1.5. terms: fundamental renaming lemmas

mutual
  lidrenTm : ∀ {k} (t : Tm k) → renTm id≤ t ≡ t
  lidrenTm (‵tvar i)  = ‵tvar & idrenFin i
  lidrenTm (‵fun f τ) = ‵fun f & lidrenTm§ τ

  lidrenTm§ : ∀ {k n} (τ : Tm§ k n) → renTm§ id≤ τ ≡ τ
  lidrenTm§ ∙       = refl
  lidrenTm§ (τ , t) = _,_ & lidrenTm§ τ ⊗ lidrenTm t

mutual
  comprenTm : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (t : Tm k) →
                renTm (η′ ∘≤ η) t ≡ renTm η′ (renTm η t)
  comprenTm η′ η (‵tvar i)  = ‵tvar & comprenFin η′ η i
  comprenTm η′ η (‵fun f τ) = ‵fun f & comprenTm§ η′ η τ

  comprenTm§ : ∀ {k k′ k″ n} (η′ : k′ ≤ k″) (η : k ≤ k′) (τ : Tm§ k n) →
                 renTm§ (η′ ∘≤ η) τ ≡ renTm§ η′ (renTm§ η τ)
  comprenTm§ η′ η ∙       = refl
  comprenTm§ η′ η (τ , t) = _,_ & comprenTm§ η′ η τ ⊗ comprenTm η′ η t

ridrenTm : ∀ {k k′} (η : k ≤ k′) (i : Fin k) → renTm η (‵tvar i) ≡ ‵tvar (renFin η i)
ridrenTm η i = refl

ridsubTm : ∀ {k m} (σ : Tm§ m k) (i : Fin k) → subTm σ (‵tvar i) ≡ subFin σ i
ridsubTm σ i = refl


----------------------------------------------------------------------------------------------------

-- 1.6. terms: generic lemmas from RenSubKit1

eqwkrenTm : ∀ {k k′} (η : k ≤ k′) (t : Tm k) →
              renTm (lift≤ η) (wkTm t) ≡ wkTm (renTm η t)
eqwkrenTm η t = comprenTm (lift≤ η) (wk≤ id≤) t ⁻¹
              ⋮ (λ η﹠ → renTm (wk≤ η﹠) t) & (rid≤ η ⋮ lid≤ η ⁻¹)
              ⋮ comprenTm (wk≤ id≤) η t

eqwkrenTm§ : ∀ {k k′ n} (η : k ≤ k′) (τ : Tm§ k n) →
               renTm§ (lift≤ η) (wkTm§ τ) ≡ wkTm§ (renTm§ η τ)
eqwkrenTm§ η ∙       = refl
eqwkrenTm§ η (τ , t) = _,_ & eqwkrenTm§ η τ ⊗ eqwkrenTm η t

eqliftrenTm§ : ∀ {k k′ n} (η : k ≤ k′) (τ : Tm§ k n) →
                 renTm§ (lift≤ η) (liftTm§ τ) ≡ liftTm§ (renTm§ η τ)
eqliftrenTm§ η τ = _,_ & eqwkrenTm§ η τ ⊗ ridrenTm (lift≤ η) zero

ridrenTm§ : ∀ {k k′} (η : k ≤ k′) → renTm§ η idTm§ ≡ varTm§ η
ridrenTm§ stop      = refl
ridrenTm§ (wk≤ η)   = (λ η﹠ → renTm§ (wk≤ η﹠) idTm§) & lid≤ η ⁻¹
                    ⋮ comprenTm§ (wk≤ id≤) η idTm§
                    ⋮ wkTm§ & ridrenTm§ η
ridrenTm§ (lift≤ η) = _,_
                        & ( eqwkrenTm§ η idTm§
                          ⋮ wkTm§ & ridrenTm§ η
                          )
                        ⊗ ridrenTm (lift≤ η) zero

eqrensubFin : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (i : Fin k) →
                subFin (renTm§ η σ) i ≡ renTm η (subFin σ i)
eqrensubFin η (σ , s) zero    = refl
eqrensubFin η (σ , s) (suc i) = eqrensubFin η σ i

eqsubrenFin : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (i : Fin k) →
                subFin (getTm§ η σ) i ≡ subFin σ (renFin η i)
eqsubrenFin ∙       stop      i       = refl
eqsubrenFin (σ , s) (wk≤ η)   i       = eqsubrenFin σ η i
eqsubrenFin (σ , s) (lift≤ η) zero    = refl
eqsubrenFin (σ , s) (lift≤ η) (suc i) = eqsubrenFin σ η i

idsubFin : ∀ {k} (i : Fin k) → subFin idTm§ i ≡ ‵tvar i
idsubFin zero    = refl
idsubFin (suc i) = eqrensubFin (wk≤ id≤) idTm§ i
                 ⋮ wkTm & idsubFin i
                 ⋮ ridrenTm (wk≤ id≤) i
                 ⋮ (λ i﹠ → ‵tvar (suc i﹠)) & idrenFin i

compsubFin : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (i : Fin k) →
               subFin (subTm§ σ′ σ) i ≡ subTm σ′ (subFin σ i)
compsubFin σ′ (σ , s) zero    = refl
compsubFin σ′ (σ , s) (suc i) = compsubFin σ′ σ i

lidgetTm§ : ∀ {k n} (τ : Tm§ k n) → getTm§ id≤ τ ≡ τ
lidgetTm§ ∙       = refl
lidgetTm§ (τ , t) = (_, t) & lidgetTm§ τ

compgetTm§ : ∀ {k n n′ n″} (η : n ≤ n′) (η′ : n′ ≤ n″) (τ : Tm§ k n″) →
               getTm§ (η′ ∘≤ η) τ ≡ getTm§ η (getTm§ η′ τ)
compgetTm§ η         stop       ∙       = refl
compgetTm§ η         (wk≤ η′)   (τ , t) = compgetTm§ η η′ τ
compgetTm§ (wk≤ η)   (lift≤ η′) (τ , t) = compgetTm§ η η′ τ
compgetTm§ (lift≤ η) (lift≤ η′) (τ , t) = (_, t) & compgetTm§ η η′ τ

eqrengetTm§ : ∀ {k k′ n n′} (η : k ≤ k′) (η′ : n ≤ n′) (τ : Tm§ k n′) →
                getTm§ η′ (renTm§ η τ) ≡ renTm§ η (getTm§ η′ τ)
eqrengetTm§ η stop       ∙       = refl
eqrengetTm§ η (wk≤ η′)   (τ , t) = eqrengetTm§ η η′ τ
eqrengetTm§ η (lift≤ η′) (τ , t) = (_, renTm η t) & eqrengetTm§ η η′ τ

eqwkgetTm§ : ∀ {k n n′} (η : n ≤ n′) (τ : Tm§ k n′) →
               getTm§ (wk≤ η) (liftTm§ τ) ≡ wkTm§ (getTm§ η τ)
eqwkgetTm§ η τ = eqrengetTm§ (wk≤ id≤) η τ

eqliftgetTm§ : ∀ {k n n′} (η : n ≤ n′) (τ : Tm§ k n′) →
                 getTm§ (lift≤ η) (liftTm§ τ) ≡ liftTm§ (getTm§ η τ)
eqliftgetTm§ η τ = (_, ‵tvar zero) & eqwkgetTm§ η τ

ridgetTm§ : ∀ {k k′} (η : k ≤ k′) → getTm§ η idTm§ ≡ varTm§ η
ridgetTm§ stop      = refl
ridgetTm§ (wk≤ η)   = eqrengetTm§ (wk≤ id≤) η idTm§
                    ⋮ wkTm§ & ridgetTm§ η
ridgetTm§ (lift≤ η) = (_, ‵tvar zero)
                        & ( eqrengetTm§ (wk≤ id≤) η idTm§
                          ⋮ wkTm§ & ridgetTm§ η
                          )


----------------------------------------------------------------------------------------------------

-- 1.7. terms: fundamental substitution lemmas

mutual
  eqrensubTm : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (t : Tm k) →
                 subTm (renTm§ η σ) t ≡ renTm η (subTm σ t)
  eqrensubTm η σ (‵tvar i)  = eqrensubFin η σ i
  eqrensubTm η σ (‵fun f τ) = ‵fun f & eqrensubTm§ η σ τ

  eqrensubTm§ : ∀ {k m m′ n} (η : m ≤ m′) (σ : Tm§ m k) (τ : Tm§ k n) →
                  subTm§ (renTm§ η σ) τ ≡ renTm§ η (subTm§ σ τ)
  eqrensubTm§ η σ ∙       = refl
  eqrensubTm§ η σ (τ , t) = _,_ & eqrensubTm§ η σ τ ⊗ eqrensubTm η σ t

mutual
  eqsubrenTm : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (t : Tm k) →
                 subTm (getTm§ η σ) t ≡ subTm σ (renTm η t)
  eqsubrenTm σ η (‵tvar i)  = eqsubrenFin σ η i
  eqsubrenTm σ η (‵fun f τ) = ‵fun f & eqsubrenTm§ σ η τ

  eqsubrenTm§ : ∀ {k k′ m n} (σ : Tm§ m k′) (η : k ≤ k′) (τ : Tm§ k n) →
                  subTm§ (getTm§ η σ) τ ≡ subTm§ σ (renTm§ η τ)
  eqsubrenTm§ σ η ∙       = refl
  eqsubrenTm§ σ η (τ , t) = _,_ & eqsubrenTm§ σ η τ ⊗ eqsubrenTm σ η t

mutual
  lidsubTm : ∀ {k} (t : Tm k) → subTm idTm§ t ≡ t
  lidsubTm (‵tvar i)  = idsubFin i
  lidsubTm (‵fun f τ) = ‵fun f & lidsubTm§ τ

  lidsubTm§ : ∀ {k n} (τ : Tm§ k n) → subTm§ idTm§ τ ≡ τ
  lidsubTm§ ∙       = refl
  lidsubTm§ (τ , t) = _,_ & lidsubTm§ τ ⊗ lidsubTm t


----------------------------------------------------------------------------------------------------

-- 1.8. terms: generic lemmas from RenSubKit2

eqsubTm : ∀ {k m} (σ : Tm§ m k) (s : Tm m) (t : Tm k) →
            subTm (σ , s) (wkTm t) ≡ subTm σ t
eqsubTm σ s t = eqsubrenTm (σ , s) (wk≤ id≤) t ⁻¹
              ⋮ (λ σ﹠ → subTm σ﹠ t) & lidgetTm§ σ

eqsubTm§ : ∀ {k m n} (σ : Tm§ m k) (s : Tm m) (τ : Tm§ k n) →
             subTm§ (σ , s) (wkTm§ τ) ≡ subTm§ σ τ
eqsubTm§ σ s ∙       = refl
eqsubTm§ σ s (τ , t) = _,_ & eqsubTm§ σ s τ ⊗ eqsubTm σ s t

eqwksubTm : ∀ {k m} (σ : Tm§ m k) (t : Tm k) →
              subTm (liftTm§ σ) (wkTm t) ≡ wkTm (subTm σ t)
eqwksubTm σ t = eqsubrenTm (liftTm§ σ) (wk≤ id≤) t ⁻¹
              ⋮ (λ σ﹠ → subTm σ﹠ t)
                  & ( eqwkgetTm§ id≤ σ
                    ⋮ wkTm§ & lidgetTm§ σ
                    )
              ⋮ eqrensubTm (wk≤ id≤) σ t

eqwksubTm§ : ∀ {k m n} (σ : Tm§ m k) (τ : Tm§ k n) →
               subTm§ (liftTm§ σ) (wkTm§ τ) ≡ wkTm§ (subTm§ σ τ)
eqwksubTm§ σ ∙       = refl
eqwksubTm§ σ (τ , t) = _,_ & eqwksubTm§ σ τ ⊗ eqwksubTm σ t

eqliftsubTm§ : ∀ {k m n} (σ : Tm§ m k) (τ : Tm§ k n) →
                 subTm§ (liftTm§ σ) (liftTm§ τ) ≡ liftTm§ (subTm§ σ τ)
eqliftsubTm§ σ τ = _,_ & eqwksubTm§ σ τ ⊗ ridsubTm (liftTm§ σ) zero

ridsubTm§ : ∀ {k m} (σ : Tm§ m k) → subTm§ σ idTm§ ≡ σ
ridsubTm§ ∙       = refl
ridsubTm§ (σ , s) = _,_
                      & ( eqsubTm§ σ s idTm§
                        ⋮ ridsubTm§ σ
                        )
                      ⊗ ridsubTm (σ , s) zero


----------------------------------------------------------------------------------------------------

-- 1.9. terms: more fundamental substitution lemmas

mutual
  compsubTm : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (t : Tm k) →
                subTm (subTm§ σ′ σ) t ≡ subTm σ′ (subTm σ t)
  compsubTm σ′ σ (‵tvar i)  = compsubFin σ′ σ i
  compsubTm σ′ σ (‵fun f τ) = ‵fun f & asssubTm§ σ′ σ τ ⁻¹

  asssubTm§ : ∀ {k m m′ n} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (τ : Tm§ k n) →
                subTm§ σ′ (subTm§ σ τ) ≡ subTm§ (subTm§ σ′ σ) τ
  asssubTm§ σ′ σ ∙       = refl
  asssubTm§ σ′ σ (τ , t) = _,_ & asssubTm§ σ′ σ τ ⊗ compsubTm σ′ σ t ⁻¹


----------------------------------------------------------------------------------------------------

-- 1.10. terms: generic lemmas from RenSubKit3

eqrencut0Tm : ∀ {k k′} (η : k ≤ k′) (t : Tm (suc k)) (s : Tm k) →
                renTm (lift≤ η) t [ renTm η s /0]Tm ≡ renTm η (t [ s /0]Tm)
eqrencut0Tm η t s = eqsubrenTm (idTm§ , renTm η s) (lift≤ η) t ⁻¹
                  ⋮ (λ σ﹠ → subTm (σ﹠ , renTm η s) t)
                      & ( ridgetTm§ η
                        ⋮ ridrenTm§ η ⁻¹
                        )
                  ⋮ eqrensubTm η (idTm§ , s) t

eqsubcut0Tm : ∀ {k m} (σ : Tm§ m k) (t : Tm (suc k)) (s : Tm k) →
                subTm (liftTm§ σ) t [ subTm σ s /0]Tm ≡ subTm σ (t [ s /0]Tm)
eqsubcut0Tm σ t s = compsubTm (idTm§ , subTm σ s) (liftTm§ σ) t ⁻¹
                  ⋮ (λ σ﹠ → subTm σ﹠ t)
                      & ( _,_
                            & ( eqsubrenTm§ (idTm§ , subTm σ s) (wk≤ id≤) σ ⁻¹
                              ⋮ (λ σ﹠ → subTm§ σ﹠ σ) & lidgetTm§ idTm§
                              ⋮ lidsubTm§ σ
                              ⋮ ridsubTm§ σ ⁻¹
                              )
                            ⊗ ridsubTm (idTm§ , subTm σ s) zero
                        )
                  ⋮ compsubTm σ (idTm§ , s) t


----------------------------------------------------------------------------------------------------

-- 2.0. formulas, indexed by number of term variables

infix  19 _‵=_
infix  18 ‵∀_
infix  17 ‵∃_
infixl 16 _‵∧_
infixl 15 _‵∨_
infixr 14 _‵⊃_
data Fm (k : Nat) : Set where
  _‵⊃_ : ∀ (A B : Fm k) → Fm k
  _‵∧_ : ∀ (A B : Fm k) → Fm k
  _‵∨_ : ∀ (A B : Fm k) → Fm k
  ‵∀_  : ∀ (A : Fm (suc k)) → Fm k
  ‵∃_  : ∀ (A : Fm (suc k)) → Fm k
  ‵⊥  : Fm k
  _‵=_ : ∀ (t u : Tm k) → Fm k

-- simultaneous substitutions of formulas
Fm§ : Nat → Set
Fm§ k = List (Fm k)

infixr 13 _‵⫗_
_‵⫗_ : ∀ {k} → Fm k → Fm k → Fm k
A ‵⫗ B = (A ‵⊃ B) ‵∧ (B ‵⊃ A)

‵¬_ : ∀ {k} → Fm k → Fm k
‵¬ A = A ‵⊃ ‵⊥

infix 19 _‵≠_
_‵≠_ : ∀ {k} → Tm k → Tm k → Fm k
t ‵≠ u = ‵¬ (t ‵= u)


----------------------------------------------------------------------------------------------------

-- 2.1. formulas: renaming

renFm : ∀ {k k′} → k ≤ k′ → Fm k → Fm k′
renFm η (A ‵⊃ B) = renFm η A ‵⊃ renFm η B
renFm η (A ‵∧ B) = renFm η A ‵∧ renFm η B
renFm η (A ‵∨ B) = renFm η A ‵∨ renFm η B
renFm η (‵∀ A)   = ‵∀ renFm (lift≤ η) A
renFm η (‵∃ A)   = ‵∃ renFm (lift≤ η) A
renFm η ‵⊥      = ‵⊥
renFm η (t ‵= u) = renTm η t ‵= renTm η u

renFm§ : ∀ {k k′} → k ≤ k′ → Fm§ k → Fm§ k′
renFm§ η ∙       = ∙
renFm§ η (Γ , A) = renFm§ η Γ , renFm η A


----------------------------------------------------------------------------------------------------

-- 2.2. formulas: generic lemmas from RenKit

wkFm : ∀ {k} → Fm k → Fm (suc k)
wkFm A = renFm (wk≤ id≤) A

wkFm§ : ∀ {k} → Fm§ k → Fm§ (suc k)
wkFm§ Γ = renFm§ (wk≤ id≤) Γ


----------------------------------------------------------------------------------------------------

-- 2.3. formulas: substitution

subFm : ∀ {k m} → Tm§ m k → Fm k → Fm m
subFm σ (A ‵⊃ B) = subFm σ A ‵⊃ subFm σ B
subFm σ (A ‵∧ B) = subFm σ A ‵∧ subFm σ B
subFm σ (A ‵∨ B) = subFm σ A ‵∨ subFm σ B
subFm σ (‵∀ A)   = ‵∀ subFm (liftTm§ σ) A
subFm σ (‵∃ A)   = ‵∃ subFm (liftTm§ σ) A
subFm σ ‵⊥      = ‵⊥
subFm σ (t ‵= u) = subTm σ t ‵= subTm σ u

subFm§ : ∀ {k m} → Tm§ m k → Fm§ k → Fm§ m
subFm§ σ ∙       = ∙
subFm§ σ (Γ , A) = subFm§ σ Γ , subFm σ A


----------------------------------------------------------------------------------------------------

-- 2.4. formulas: generic lemmas from SubKit

_[_/0]Fm : ∀ {k} → Fm (suc k) → Tm k → Fm k
A [ s /0]Fm = subFm (idTm§ , s) A

_[_/1]Fm : ∀ {k} → Fm (suc (suc k)) → Tm (suc k) → Fm (suc k)
A [ s /1]Fm = subFm (wkTm§ idTm§ , s , ‵tvar zero) A


----------------------------------------------------------------------------------------------------

-- 2.5. formulas: fundamental renaming lemmas

lidrenFm : ∀ {k} (A : Fm k) → renFm id≤ A ≡ A
lidrenFm (A ‵⊃ B) = _‵⊃_ & lidrenFm A ⊗ lidrenFm B
lidrenFm (A ‵∧ B) = _‵∧_ & lidrenFm A ⊗ lidrenFm B
lidrenFm (A ‵∨ B) = _‵∨_ & lidrenFm A ⊗ lidrenFm B
lidrenFm (‵∀ A)   = ‵∀_ & lidrenFm A
lidrenFm (‵∃ A)   = ‵∃_ & lidrenFm A
lidrenFm ‵⊥      = refl
lidrenFm (t ‵= u) = _‵=_ & lidrenTm t ⊗ lidrenTm u

comprenFm : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (A : Fm k) →
              renFm (η′ ∘≤ η) A ≡ renFm η′ (renFm η A)
comprenFm η′ η (A ‵⊃ B) = _‵⊃_ & comprenFm η′ η A ⊗ comprenFm η′ η B
comprenFm η′ η (A ‵∧ B) = _‵∧_ & comprenFm η′ η A ⊗ comprenFm η′ η B
comprenFm η′ η (A ‵∨ B) = _‵∨_ & comprenFm η′ η A ⊗ comprenFm η′ η B
comprenFm η′ η (‵∀ A)   = ‵∀_ & comprenFm (lift≤ η′) (lift≤ η) A
comprenFm η′ η (‵∃ A)   = ‵∃_ & comprenFm (lift≤ η′) (lift≤ η) A
comprenFm η′ η ‵⊥      = refl
comprenFm η′ η (t ‵= u) = _‵=_ & comprenTm η′ η t ⊗ comprenTm η′ η u


----------------------------------------------------------------------------------------------------

-- 2.6. formulas: generic lemmas from RenSubKit1

lidrenFm§ : ∀ {k} (Γ : Fm§ k) → renFm§ id≤ Γ ≡ Γ
lidrenFm§ ∙       = refl
lidrenFm§ (Γ , A) = _,_ & lidrenFm§ Γ ⊗ lidrenFm A

comprenFm§ : ∀ {k k′ k″} (η′ : k′ ≤ k″) (η : k ≤ k′) (Γ : Fm§ k) →
               renFm§ (η′ ∘≤ η) Γ ≡ renFm§ η′ (renFm§ η Γ)
comprenFm§ η′ η ∙       = refl
comprenFm§ η′ η (Γ , A) = _,_ & comprenFm§ η′ η Γ ⊗ comprenFm η′ η A

eqwkrenFm : ∀ {k k′} (η : k ≤ k′) (A : Fm k) →
              renFm (lift≤ η) (wkFm A) ≡ wkFm (renFm η A)
eqwkrenFm η A = comprenFm (lift≤ η) (wk≤ id≤) A ⁻¹
              ⋮ (λ η﹠ → renFm (wk≤ η﹠) A) & (rid≤ η ⋮ lid≤ η ⁻¹)
              ⋮ comprenFm (wk≤ id≤) η A

eqwkrenFm§ : ∀ {k k′} (η : k ≤ k′) (Γ : Fm§ k) →
               renFm§ (lift≤ η) (wkFm§ Γ) ≡ wkFm§ (renFm§ η Γ)
eqwkrenFm§ η ∙       = refl
eqwkrenFm§ η (Γ , A) = _,_ & eqwkrenFm§ η Γ ⊗ eqwkrenFm η A


----------------------------------------------------------------------------------------------------

-- 2.7. formulas: fundamental substitution lemmas

mutual
  eqrensubFm : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (A : Fm k) →
                 subFm (renTm§ η σ) A ≡ renFm η (subFm σ A)
  eqrensubFm η σ (A ‵⊃ B) = _‵⊃_ & eqrensubFm η σ A ⊗ eqrensubFm η σ B
  eqrensubFm η σ (A ‵∧ B) = _‵∧_ & eqrensubFm η σ A ⊗ eqrensubFm η σ B
  eqrensubFm η σ (A ‵∨ B) = _‵∨_ & eqrensubFm η σ A ⊗ eqrensubFm η σ B
  eqrensubFm η σ (‵∀ A)   = ‵∀_ & eqrensubliftFm η σ A
  eqrensubFm η σ (‵∃ A)   = ‵∃_ & eqrensubliftFm η σ A
  eqrensubFm η σ ‵⊥      = refl
  eqrensubFm η σ (t ‵= u) = _‵=_ & eqrensubTm η σ t ⊗ eqrensubTm η σ u

  eqrensubliftFm : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (A : Fm (suc k)) →
                     subFm (liftTm§ (renTm§ η σ)) A ≡ renFm (lift≤ η) (subFm (liftTm§ σ) A)
  eqrensubliftFm η σ A = (λ σ﹠ → subFm σ﹠ A) & eqliftrenTm§ η σ ⁻¹
                       ⋮ eqrensubFm (lift≤ η) (liftTm§ σ) A

mutual
  eqsubrenFm : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (A : Fm k) →
                 subFm (getTm§ η σ) A ≡ subFm σ (renFm η A)
  eqsubrenFm σ η (A ‵⊃ B) = _‵⊃_ & eqsubrenFm σ η A ⊗ eqsubrenFm σ η B
  eqsubrenFm σ η (A ‵∧ B) = _‵∧_ & eqsubrenFm σ η A ⊗ eqsubrenFm σ η B
  eqsubrenFm σ η (A ‵∨ B) = _‵∨_ & eqsubrenFm σ η A ⊗ eqsubrenFm σ η B
  eqsubrenFm σ η (‵∀ A)   = ‵∀_ & eqsubrenliftFm σ η A
  eqsubrenFm σ η (‵∃ A)   = ‵∃_ & eqsubrenliftFm σ η A
  eqsubrenFm σ η ‵⊥      = refl
  eqsubrenFm σ η (t ‵= u) = _‵=_ & eqsubrenTm σ η t ⊗ eqsubrenTm σ η u

  eqsubrenliftFm : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (A : Fm (suc k)) →
                     subFm (liftTm§ (getTm§ η σ)) A ≡ subFm (liftTm§ σ) (renFm (lift≤ η) A)
  eqsubrenliftFm σ η A = (λ σ﹠ → subFm σ﹠ A) & eqliftgetTm§ η σ ⁻¹
                       ⋮ eqsubrenFm (liftTm§ σ) (lift≤ η) A

lidsubFm : ∀ {k} (A : Fm k) → subFm idTm§ A ≡ A
lidsubFm (A ‵⊃ B) = _‵⊃_ & lidsubFm A ⊗ lidsubFm B
lidsubFm (A ‵∧ B) = _‵∧_ & lidsubFm A ⊗ lidsubFm B
lidsubFm (A ‵∨ B) = _‵∨_ & lidsubFm A ⊗ lidsubFm B
lidsubFm (‵∀ A)   = ‵∀_ & lidsubFm A
lidsubFm (‵∃ A)   = ‵∃_ & lidsubFm A
lidsubFm ‵⊥      = refl
lidsubFm (t ‵= u) = _‵=_ & lidsubTm t ⊗ lidsubTm u


----------------------------------------------------------------------------------------------------

-- 2.8. formulas: generic lemmas from RenSubKit2

lidsubFm§ : ∀ {k} (Δ : Fm§ k) → subFm§ idTm§ Δ ≡ Δ
lidsubFm§ ∙       = refl
lidsubFm§ (Δ , A) = _,_ & lidsubFm§ Δ ⊗ lidsubFm A

eqrensubFm§ : ∀ {k m m′} (η : m ≤ m′) (σ : Tm§ m k) (Γ : Fm§ k) →
                subFm§ (renTm§ η σ) Γ ≡ renFm§ η (subFm§ σ Γ)
eqrensubFm§ η σ ∙       = refl
eqrensubFm§ η σ (Γ , A) = _,_ & eqrensubFm§ η σ Γ ⊗ eqrensubFm η σ A

eqsubrenFm§ : ∀ {k k′ m} (σ : Tm§ m k′) (η : k ≤ k′) (Γ : Fm§ k) →
                subFm§ (getTm§ η σ) Γ ≡ subFm§ σ (renFm§ η Γ)
eqsubrenFm§ σ η ∙       = refl
eqsubrenFm§ σ η (Γ , A) = _,_ & eqsubrenFm§ σ η Γ ⊗ eqsubrenFm σ η A

eqsubFm : ∀ {k m} (σ : Tm§ m k) (s : Tm m) (A : Fm k) →
            subFm (σ , s) (wkFm A) ≡ subFm σ A
eqsubFm σ s A = eqsubrenFm (σ , s) (wk≤ id≤) A ⁻¹
              ⋮ (λ σ﹠ → subFm σ﹠ A) & lidgetTm§ σ

eqsubFm§ : ∀ {k m} (σ : Tm§ m k) (s : Tm m) (Γ : Fm§ k) →
             subFm§ (σ , s) (wkFm§ Γ) ≡ subFm§ σ Γ
eqsubFm§ σ s ∙       = refl
eqsubFm§ σ s (Γ , A) = _,_ & eqsubFm§ σ s Γ ⊗ eqsubFm σ s A

eqwksubFm : ∀ {k m} (σ : Tm§ m k) (A : Fm k) →
              subFm (liftTm§ σ) (wkFm A) ≡ wkFm (subFm σ A)
eqwksubFm σ A = eqsubrenFm (liftTm§ σ) (wk≤ id≤) A ⁻¹
              ⋮ (λ σ﹠ → subFm σ﹠ A)
                  & ( eqwkgetTm§ id≤ σ
                    ⋮ wkTm§ & lidgetTm§ σ
                    )
              ⋮ eqrensubFm (wk≤ id≤) σ A

eqwksubFm§ : ∀ {k m} (σ : Tm§ m k) (Γ : Fm§ k) →
               subFm§ (liftTm§ σ) (wkFm§ Γ) ≡ wkFm§ (subFm§ σ Γ)
eqwksubFm§ σ ∙       = refl
eqwksubFm§ σ (Γ , A) = _,_ & eqwksubFm§ σ Γ ⊗ eqwksubFm σ A


----------------------------------------------------------------------------------------------------

-- 2.9. formulas: more fundamental substitution lemmas

mutual
  compsubFm : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (A : Fm k) →
                subFm (subTm§ σ′ σ) A ≡ subFm σ′ (subFm σ A)
  compsubFm σ′ σ (A ‵⊃ B) = _‵⊃_ & compsubFm σ′ σ A ⊗ compsubFm σ′ σ B
  compsubFm σ′ σ (A ‵∧ B) = _‵∧_ & compsubFm σ′ σ A ⊗ compsubFm σ′ σ B
  compsubFm σ′ σ (A ‵∨ B) = _‵∨_ & compsubFm σ′ σ A ⊗ compsubFm σ′ σ B
  compsubFm σ′ σ (‵∀ A)   = ‵∀_ & compsubliftFm σ′ σ A
  compsubFm σ′ σ (‵∃ A)   = ‵∃_ & compsubliftFm σ′ σ A
  compsubFm σ′ σ ‵⊥      = refl
  compsubFm σ′ σ (t ‵= u) = _‵=_ & compsubTm σ′ σ t ⊗ compsubTm σ′ σ u

  compsubliftFm : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (A : Fm (suc k)) →
                    subFm (liftTm§ (subTm§ σ′ σ)) A ≡ subFm (liftTm§ σ′) (subFm (liftTm§ σ) A)
  compsubliftFm σ′ σ A = (λ σ﹠ → subFm σ﹠ A) & eqliftsubTm§ σ′ σ ⁻¹
                       ⋮ compsubFm (liftTm§ σ′) (liftTm§ σ) A


----------------------------------------------------------------------------------------------------

-- 2.10. formulas: generic lemmas from RenSubKit3

compsubFm§ : ∀ {k m m′} (σ′ : Tm§ m′ m) (σ : Tm§ m k) (Δ : Fm§ k) →
               subFm§ (subTm§ σ′ σ) Δ ≡ subFm§ σ′ (subFm§ σ Δ)
compsubFm§ σ′ σ ∙       = refl
compsubFm§ σ′ σ (Δ , A) = _,_ & compsubFm§ σ′ σ Δ ⊗ compsubFm σ′ σ A

idcutFm : ∀ {k} (A : Fm (suc k)) → renFm (lift≤ (wk≤ id≤)) A [ ‵tvar zero /0]Fm ≡ A
idcutFm A = eqsubrenFm (idTm§ , ‵tvar zero) (lift≤ (wk≤ id≤)) A ⁻¹
          ⋮ (λ σ﹠ → subFm (σ﹠ , ‵tvar zero) A) & lidgetTm§ (wkTm§ idTm§)
          ⋮ lidsubFm A

eqrencut0Fm : ∀ {k k′} (η : k ≤ k′) (A : Fm (suc k)) (s : Tm k) →
                renFm (lift≤ η) A [ renTm η s /0]Fm ≡ renFm η (A [ s /0]Fm)
eqrencut0Fm η A s = eqsubrenFm (idTm§ , renTm η s) (lift≤ η) A ⁻¹
                  ⋮ (λ σ﹠ → subFm (σ﹠ , renTm η s) A) & (ridgetTm§ η ⋮ ridrenTm§ η ⁻¹)
                  ⋮ eqrensubFm η (idTm§ , s) A

eqrencut1Fm : ∀ {k k′} (η : k ≤ k′) (A : Fm (suc k)) (s : Tm (suc k)) →
                wkFm (renFm (lift≤ η) A) [ renTm (lift≤ η) s /1]Fm ≡
                  renFm (lift≤ η) (wkFm A [ s /1]Fm)
eqrencut1Fm η A s = subFm (wkTm§ idTm§ , renTm (lift≤ η) s , ‵tvar zero)
                      & eqwkrenFm (lift≤ η) A ⁻¹
                  ⋮ eqsubrenFm (wkTm§ idTm§ , renTm (lift≤ η) s , ‵tvar zero)
                      (lift≤ (lift≤ η)) (wkFm A) ⁻¹
                  ⋮ (λ σ﹠ → subFm (σ﹠ , renTm (lift≤ η) s , ‵tvar zero) (wkFm A))
                      & ( eqwkgetTm§ η idTm§
                        ⋮ wkTm§ & (ridgetTm§ η ⋮ ridrenTm§ η ⁻¹)
                        ⋮ eqwkrenTm§ η idTm§ ⁻¹
                        )
                  ⋮ eqrensubFm (lift≤ η) (wkTm§ idTm§ , s , ‵tvar zero) (wkFm A)

eqsubcut0Fm : ∀ {k m} (σ : Tm§ m k) (A : Fm (suc k)) (s : Tm k) →
                subFm (liftTm§ σ) A [ subTm σ s /0]Fm ≡ subFm σ (A [ s /0]Fm)
eqsubcut0Fm σ A s = compsubFm (idTm§ , subTm σ s) (liftTm§ σ) A ⁻¹
                  ⋮ (λ σ﹠ → subFm σ﹠ A)
                      & ( _,_
                            & ( eqsubrenTm§ (idTm§ , subTm σ s) (wk≤ id≤) σ ⁻¹
                              ⋮ (λ σ﹠ → subTm§ σ﹠ σ) & lidgetTm§ idTm§
                              ⋮ lidsubTm§ σ
                              ⋮ ridsubTm§ σ ⁻¹
                              )
                            ⊗ ridsubTm (idTm§ , subTm σ s) zero
                        )
                  ⋮ compsubFm σ (idTm§ , s) A


----------------------------------------------------------------------------------------------------

-- 2.11. term renaming for derivation variables

tren∋ : ∀ {k k′ Γ A} (η : k ≤ k′) → Γ ∋ A → renFm§ η Γ ∋ renFm η A
tren∋ η zero    = zero
tren∋ η (suc i) = suc (tren∋ η i)

twk∋ : ∀ {k} {Γ : Fm§ k} {A} → Γ ∋ A → wkFm§ Γ ∋ wkFm A
twk∋ i = tren∋ (wk≤ id≤) i

lidtren∋﹫ : ∀ {k} {Γ : Fm§ k} {A} (i : Γ ∋ A) → tren∋ id≤ i ≡ cast∋ (lidrenFm§ Γ) (lidrenFm A) i
lidtren∋﹫ zero    = castzero∋ (lidrenFm§ _) (lidrenFm _)
lidtren∋﹫ (suc i) = suc & lidtren∋﹫ i
                  ⋮ castsuc∋ (lidrenFm§ _) (lidrenFm _) (lidrenFm _) i

lidtren∋ : ∀ {k} {Γ : Fm§ k} {A} (p₁ : renFm§ id≤ Γ ≡ Γ) (p₂ : renFm id≤ A ≡ A) (i : Γ ∋ A) →
             tren∋ id≤ i ≡ cast∋ p₁ p₂ i
lidtren∋ p₁ p₂ i = lidtren∋﹫ i
                 ⋮ (λ p₁﹠ p₂﹠ → cast∋ p₁﹠ p₂﹠ i) & uip _ _ ⊗ uip _ _

comptren∋﹫ : ∀ {k k′ k″ Γ A} (η′ : k′ ≤ k″) (η : k ≤ k′) (i : Γ ∋ A) →
               tren∋ (η′ ∘≤ η) i ≡
                 cast∋ (comprenFm§ η′ η Γ) (comprenFm η′ η A) (tren∋ η′ (tren∋ η i))
comptren∋﹫ η′ η zero    = castzero∋ (comprenFm§ η′ η _) (comprenFm η′ η _)
comptren∋﹫ η′ η (suc i) = suc & comptren∋﹫ η′ η i
                        ⋮ castsuc∋ (comprenFm§ η′ η _) (comprenFm η′ η _)
                            (comprenFm η′ η _) (tren∋ η′ (tren∋ η i))

comptren∋ : ∀ {k k′ k″ Γ ^Γ A ^A} (η′ : k′ ≤ k″) (η : k ≤ k′)
              (p₁ : ^Γ ≡ renFm§ (η′ ∘≤ η) Γ) (q₁ : ^A ≡ renFm (η′ ∘≤ η) A)
              (p₂ : ^Γ ≡ renFm§ η′ (renFm§ η Γ)) (q₂ : ^A ≡ renFm η′ (renFm η A))
              (i : Γ ∋ A) →
              cast∋ p₁ q₁ (tren∋ (η′ ∘≤ η) i) ≡ cast∋ p₂ q₂ (tren∋ η′ (tren∋ η i))
comptren∋ η′ η refl refl p₂ q₂ i = comptren∋﹫ η′ η i
                                 ⋮ (λ p₂﹠ q₂﹠ → cast∋ p₂﹠ q₂﹠ (tren∋ η′ (tren∋ η i)))
                                     & uip _ _ ⊗ uip _ _

-- term renaming for order-preserving embeddings
tren⊆ : ∀ {k k′ Γ Γ′} (η : k ≤ k′) → Γ ⊆ Γ′ → renFm§ η Γ ⊆ renFm§ η Γ′
tren⊆ η stop      = stop
tren⊆ η (wk⊆ ζ)   = wk⊆ (tren⊆ η ζ)
tren⊆ η (lift⊆ ζ) = lift⊆ (tren⊆ η ζ)

twk⊆ : ∀ {k} {Γ Γ′ : Fm§ k} → Γ ⊆ Γ′ → wkFm§ Γ ⊆ wkFm§ Γ′
twk⊆ ζ = tren⊆ (wk≤ id≤) ζ

lidtren⊆﹫ : ∀ {k} {Γ Γ′ : Fm§ k} (ζ : Γ ⊆ Γ′) → tren⊆ id≤ ζ ≡ cast⊆ (lidrenFm§ Γ) (lidrenFm§ Γ′) ζ
lidtren⊆﹫ stop      = refl
lidtren⊆﹫ (wk⊆ ζ)   = wk⊆ & lidtren⊆﹫ ζ
                    ⋮ castwk⊆ (lidrenFm§ _) (lidrenFm§ _) (lidrenFm _) ζ
lidtren⊆﹫ (lift⊆ ζ) = lift⊆ & lidtren⊆﹫ ζ
                    ⋮ castlift⊆ (lidrenFm§ _) (lidrenFm§ _) (lidrenFm _) ζ

lidtren⊆ : ∀ {k} {Γ Γ′ : Fm§ k} (p₁ : renFm§ id≤ Γ ≡ Γ) (p₂ : renFm§ id≤ Γ′ ≡ Γ′) (ζ : Γ ⊆ Γ′) →
             tren⊆ id≤ ζ ≡ cast⊆ p₁ p₂ ζ
lidtren⊆ p₁ p₂ ζ = lidtren⊆﹫ ζ
                 ⋮ (λ p₁﹠ p₂﹠ → cast⊆ p₁﹠ p₂﹠ ζ) & uip _ _ ⊗ uip _ _

lcomptren⊆﹫ : ∀ {k k′ k″ Γ Γ′} (η′ : k′ ≤ k″) (η : k ≤ k′) (ζ : Γ ⊆ Γ′) →
                tren⊆ (η′ ∘≤ η) ζ ≡
                  cast⊆ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Γ′) (tren⊆ η′ (tren⊆ η ζ))
lcomptren⊆﹫ η′ η stop      = refl
lcomptren⊆﹫ η′ η (wk⊆ ζ)   = wk⊆ & lcomptren⊆﹫ η′ η ζ
                           ⋮ castwk⊆ (comprenFm§ η′ η _) (comprenFm§ η′ η _) (comprenFm η′ η _)
                               (tren⊆ η′ (tren⊆ η ζ))
lcomptren⊆﹫ η′ η (lift⊆ ζ) = lift⊆ & lcomptren⊆﹫ η′ η ζ
                           ⋮ castlift⊆ (comprenFm§ η′ η _) (comprenFm§ η′ η _) (comprenFm η′ η _)
                               (tren⊆ η′ (tren⊆ η ζ))

lcomptren⊆ : ∀ {k k′ k″ Γ Γ′} (η′ : k′ ≤ k″) (η : k ≤ k′)
               (p₁ : renFm§ (η′ ∘≤ η) Γ ≡ renFm§ η′ (renFm§ η Γ))
               (p₂ : renFm§ (η′ ∘≤ η) Γ′ ≡ renFm§ η′ (renFm§ η Γ′)) (ζ : Γ ⊆ Γ′) →
               tren⊆ (η′ ∘≤ η) ζ ≡ cast⊆ p₁ p₂ (tren⊆ η′ (tren⊆ η ζ))
lcomptren⊆ η′ η p₁ p₂ ζ = lcomptren⊆﹫ η′ η ζ
                        ⋮ (λ p₁﹠ p₂﹠ → cast⊆ p₁﹠ p₂﹠ (tren⊆ η′ (tren⊆ η ζ))) & uip _ _ ⊗ uip _ _

ridtren⊆ : ∀ {k k′ Γ} (η : k ≤ k′) → tren⊆ {Γ = Γ} η id⊆ ≡ id⊆
ridtren⊆ {Γ = ∙}     η = refl
ridtren⊆ {Γ = Γ , A} η = lift⊆ & ridtren⊆ η

-- TODO: does this belong to some categorical structure?
rcomptren⊆ : ∀ {k k′ Γ Γ′ Γ″} (η : k ≤ k′) (ζ′ : Γ′ ⊆ Γ″) (ζ : Γ ⊆ Γ′) →
               tren⊆ η (ζ′ ∘⊆ ζ) ≡ tren⊆ η ζ′ ∘⊆ tren⊆ η ζ
rcomptren⊆ η stop       ζ         = refl
rcomptren⊆ η (wk⊆ ζ′)   ζ         = wk⊆ & rcomptren⊆ η ζ′ ζ
rcomptren⊆ η (lift⊆ ζ′) (wk⊆ ζ)   = wk⊆ & rcomptren⊆ η ζ′ ζ
rcomptren⊆ η (lift⊆ ζ′) (lift⊆ ζ) = lift⊆ & rcomptren⊆ η ζ′ ζ


----------------------------------------------------------------------------------------------------

-- 3.0. derivations, indexed by list of derivation variables

-- Heyting and Peano arithmetic
data Theory : Set where
  HA : Theory
  PA : Theory

infixr 4 _‵$_
infix  3 _/_⊢_
data _/_⊢_ {k} : Theory → Fm§ k → Fm k → Set where
  ‵var     : ∀ {Þ Γ A} (i : Γ ∋ A) → Þ / Γ ⊢ A -- i-th derivation variable
  ‵lam     : ∀ {Þ Γ A B} (d : Þ / Γ , A ⊢ B) → Þ / Γ ⊢ A ‵⊃ B
  _‵$_     : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A ‵⊃ B) (e : Þ / Γ ⊢ A) → Þ / Γ ⊢ B
  ‵pair    : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A) (e : Þ / Γ ⊢ B) → Þ / Γ ⊢ A ‵∧ B
  ‵fst     : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A ‵∧ B) → Þ / Γ ⊢ A
  ‵snd     : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A ‵∧ B) → Þ / Γ ⊢ B
  ‵left    : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ A) → Þ / Γ ⊢ A ‵∨ B
  ‵right   : ∀ {Þ Γ A B} (d : Þ / Γ ⊢ B) → Þ / Γ ⊢ A ‵∨ B
  ‵either  : ∀ {Þ Γ A B C} (c : Þ / Γ ⊢ A ‵∨ B) (d : Þ / Γ , A ⊢ C) (e : Þ / Γ , B ⊢ C) →
               Þ / Γ ⊢ C

  --     A(x₀)
  -- --------------
  --   ∀y.A[y/xₒ]
  ‵all     : ∀ {Þ Γ Γ∗ A} (r : Γ∗ ≡ wkFm§ Γ) (d : Þ / Γ∗ ⊢ A) → Þ / Γ ⊢ ‵∀ A

  --   ∀y.A[y/x₀]
  -- --------------
  --    A[t/x₀]
  ‵unall   : ∀ {Þ Γ A A∗} (t : Tm k) (r : A [ t /0]Fm ≡ A∗) (d : Þ / Γ ⊢ ‵∀ A) → Þ / Γ ⊢ A∗

  --    A[t/x₀]
  -- --------------
  --   ∃y.A[y/x₀]
  ‵ex      : ∀ {Þ Γ A A∗} (t : Tm k) (r : A [ t /0]Fm ≡ A∗) (d : Þ / Γ ⊢ A∗) → Þ / Γ ⊢ ‵∃ A

  --                 A(x₀)
  --                   ⋮
  --   ∃y.A[y/x₀]      C
  -- -----------------------
  --           C
  ‵letex   : ∀ {Þ Γ Γ∗ A C C∗} (r₁ : Γ∗ ≡ wkFm§ Γ) (r₂ : C∗ ≡ wkFm C) (d : Þ / Γ ⊢ ‵∃ A)
               (e : Þ / Γ∗ , A ⊢ C∗) →
               Þ / Γ ⊢ C

  -- explosion (ex falso quodlibet) as primitive in Heyting arithmetic
  ‵abortHA : ∀ {Γ C} (d : HA / Γ ⊢ ‵⊥) → HA / Γ ⊢ C

  -- double negation elimination (reductio ad absurdum) as primitive in Peano arithmetic
  ‵magicPA : ∀ {Γ A} (d : PA / Γ , ‵¬ A ⊢ ‵⊥) → PA / Γ ⊢ A

  ‵refl    : ∀ {Þ Γ t} → Þ / Γ ⊢ t ‵= t
  ‵sym     : ∀ {Þ Γ t u} (d : Þ / Γ ⊢ t ‵= u) → Þ / Γ ⊢ u ‵= t
  ‵trans   : ∀ {Þ Γ s t u} (d : Þ / Γ ⊢ s ‵= t) (e : Þ / Γ ⊢ t ‵= u) → Þ / Γ ⊢ s ‵= u

  ‵cong    : ∀ {Þ n Γ τ τ∗ s t∗} (f : Prim n) (i : Fin n) (r₁ : poke i s τ ≡ τ∗)
               (r₂ : peek i τ ≡ t∗) (d : Þ / Γ ⊢ s ‵= t∗) →
               Þ / Γ ⊢ ‵fun f τ∗ ‵= ‵fun f τ

  ‵dis     : ∀ {Þ Γ t} → Þ / Γ ⊢ 𝕊 t ‵≠ 𝟘

  ‵inj     : ∀ {Þ Γ t u} (d : Þ / Γ ⊢ 𝕊 t ‵= 𝕊 u) → Þ / Γ ⊢ t ‵= u

  --   A[0/x₀]    ∀y.A[y/x₀]→A[y+1/x₀]
  -- ------------------------------------
  --              ∀y.A[y/x₀]
  ‵ind     : ∀ {Þ Γ A A∗ A∗∗} (r₁ : A [ 𝟘 /0]Fm ≡ A∗) (r₂ : wkFm A [ 𝕊 (‵tvar zero) /1]Fm ≡ A∗∗)
               (d : Þ / Γ ⊢ A∗) (e : Þ / Γ ⊢ ‵∀ (A ‵⊃ A∗∗)) →
               Þ / Γ ⊢ ‵∀ A

  ‵proj    : ∀ {Þ n Γ τ t∗} (i : Fin n) (r : peek i τ ≡ t∗) → Þ / Γ ⊢ ‵fun (proj i) τ ‵= t∗

  ‵comp    : ∀ {Þ n m Γ τ τ∗} (g : Prim m) (φ : Prim§ n m) (r : for φ (λ f → ‵fun f τ) ≡ τ∗) →
               Þ / Γ ⊢ ‵fun (comp g φ) τ ‵= ‵fun g τ∗

  ‵rec     : ∀ {Þ n Γ τ t} (f : Prim n) (g : Prim (suc (suc n))) →
               Þ / Γ ⊢ ‵fun (rec f g) (τ , 𝟘) ‵= ‵fun f τ ‵∧
                 ‵fun (rec f g) (τ , 𝕊 t) ‵= ‵fun g (τ , t , ‵fun (rec f g) (τ , t))

-- simultaneous substitutions of derivations
infix 3 _/_⊢§_
data _/_⊢§_ {k} (Þ : Theory) (Γ : Fm§ k) : Fm§ k → Set where
  ∙   : Þ / Γ ⊢§ ∙
  _,_ : ∀ {Δ A} (δ : Þ / Γ ⊢§ Δ) (d : Þ / Γ ⊢ A) → Þ / Γ ⊢§ Δ , A

-- numeric literals for derivations
instance
  number⊢ : ∀ {Þ k} {Γ : Fm§ k} {A} → Number (Þ / Γ ⊢ A)
  number⊢ {Γ = Γ} {A} = record
    { Constraint = λ m → Γ ∋⟨ m ⟩ A
    ; fromNat    = λ m {{p}} → ‵var (∋#→∋ p)
    }


----------------------------------------------------------------------------------------------------

-- 3.1. casting for equalities in derivation constructors

casteqwkFm : ∀ {k} {A ^A : Fm k} {A∗ ^A∗} (q₁ : ^A ≡ A) (q₂ : ^A∗ ≡ A∗) (r : A∗ ≡ wkFm A) →
               ^A∗ ≡ wkFm ^A
casteqwkFm refl refl r = r

casteqwkFm§ : ∀ {k} {Γ ^Γ : Fm§ k} {Γ∗ ^Γ∗} (p₁ : ^Γ ≡ Γ) (p₂ : ^Γ∗ ≡ Γ∗) (r : Γ∗ ≡ wkFm§ Γ) →
                ^Γ∗ ≡ wkFm§ ^Γ
casteqwkFm§ refl refl r = r

casteqcut0Fm : ∀ {k} {A ^A A∗ ^A∗} {s ^s : Tm k} (q₁ : ^A ≡ A) (q₂ : ^A∗ ≡ A∗) (q₃ : ^s ≡ s)
                 (r : A [ s /0]Fm ≡ A∗) →
                 ^A [ ^s /0]Fm ≡ ^A∗
casteqcut0Fm refl refl refl r = r

casteqcut1Fm : ∀ {k} {A ^A A∗∗ ^A∗∗} {s ^s : Tm (suc k)} (q₁ : ^A ≡ A) (q₂ : ^A∗∗ ≡ A∗∗)
                 (q₃ : ^s ≡ s) (r : wkFm A [ s /1]Fm ≡ A∗∗) →
                 wkFm ^A [ ^s /1]Fm ≡ ^A∗∗
casteqcut1Fm refl refl refl r = r

casteqpeek : ∀ {k n} {τ ^τ : Tm§ k n} {t∗ ^t∗} (p : ^τ ≡ τ) (q : ^t∗ ≡ t∗) (i : Fin n)
               (r : peek i τ ≡ t∗) →
               peek i ^τ ≡ ^t∗
casteqpeek refl refl i r = r

casteqpoke : ∀ {k n} {τ ^τ τ∗ ^τ∗ : Tm§ k n} {s ^s t ^t : Tm k} (p₁ : ^τ ≡ τ) (p₂ : ^τ∗ ≡ τ∗)
               (q₁ : ^s ≡ s) (q₂ : ^t ≡ t) (i : Fin n) (r : poke i s τ ≡ τ∗) →
               poke i ^s ^τ ≡ ^τ∗
casteqpoke refl refl refl refl i r = r

casteqfor : ∀ {k n m τ ^τ τ∗ ^τ∗} (p₁ : ^τ ≡ τ) (p₂ : ^τ∗ ≡ τ∗) (φ : Prim§ n m)
              (r : for φ (λ f → ‵fun {k = k} f τ) ≡ τ∗) →
              for φ (λ f → ‵fun f ^τ) ≡ ^τ∗
casteqfor refl refl φ r = r


----------------------------------------------------------------------------------------------------

-- 3.2. casting for derivations

cast : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A} → ^Γ ≡ Γ → ^A ≡ A → Þ / Γ ⊢ A → Þ / ^Γ ⊢ ^A
cast refl refl d = d

castvar : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A} (p : ^Γ ≡ Γ) (q : ^A ≡ A) (i : Γ ∋ A) →
            ‵var {Þ = Þ} (cast∋ p q i) ≡ cast p q (‵var i)
castvar refl refl i = refl

castlam : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
            (d : Þ / Γ , A ⊢ B) →
            ‵lam (cast (_,_ & p ⊗ q₁) q₂ d) ≡ cast p (_‵⊃_ & q₁ ⊗ q₂) (‵lam d)
castlam refl refl refl d = refl

castapp : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
            (d : Þ / Γ ⊢ A ‵⊃ B) (e : Þ / Γ ⊢ A) →
            (cast p (_‵⊃_ & q₁ ⊗ q₂) d ‵$ cast p q₁ e) ≡ cast p q₂ (d ‵$ e)
castapp refl refl refl d e = refl

castpair : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
             (d : Þ / Γ ⊢ A) (e : Þ / Γ ⊢ B) →
             ‵pair (cast p q₁ d) (cast p q₂ e) ≡ cast p (_‵∧_ & q₁ ⊗ q₂) (‵pair d e)
castpair refl refl refl d e = refl

castfst : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
            (d : Þ / Γ ⊢ A ‵∧ B) →
            ‵fst (cast p (_‵∧_ & q₁ ⊗ q₂) d) ≡ cast p q₁ (‵fst d)
castfst refl refl refl d = refl

castsnd : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
            (d : Þ / Γ ⊢ A ‵∧ B) →
            ‵snd (cast p (_‵∧_ & q₁ ⊗ q₂) d) ≡ cast p q₂ (‵snd d)
castsnd refl refl refl d = refl

castleft : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
             (d : Þ / Γ ⊢ A) →
             ‵left (cast p q₁ d) ≡ cast p (_‵∨_ & q₁ ⊗ q₂) (‵left d)
castleft refl refl refl d = refl

castright : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
              (d : Þ / Γ ⊢ B) →
              ‵right (cast p q₂ d) ≡ cast p (_‵∨_ & q₁ ⊗ q₂) (‵right d)
castright refl refl refl d = refl

casteither : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A B ^B C ^C} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^B ≡ B)
               (q₃ : ^C ≡ C) (c : Þ / Γ ⊢ A ‵∨ B) (d : Þ / Γ , A ⊢ C) (e : Þ / Γ , B ⊢ C) →
               ‵either (cast p (_‵∨_ & q₁ ⊗ q₂) c) (cast (_,_ & p ⊗ q₁) q₃ d)
                   (cast (_,_ & p ⊗ q₂) q₃ e) ≡
                 cast p q₃ (‵either c d e)
casteither refl refl refl refl c d e = refl

castall : ∀ {Þ k} {Γ ^Γ : Fm§ k} {Γ∗ ^Γ∗ A ^A} (p₁ : ^Γ ≡ Γ) (p₂ : ^Γ∗ ≡ Γ∗) (p₃ : ^A ≡ A)
            (r : Γ∗ ≡ wkFm§ Γ) (d : Þ / Γ∗ ⊢ A) →
            ‵all (casteqwkFm§ p₁ p₂ r) (cast p₂ p₃ d) ≡ cast p₁ (‵∀_ & p₃) (‵all r d)
castall refl refl refl r d = refl

castunall : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A A∗ ^A∗ ^t t} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^A∗ ≡ A∗)
              (q₃ : ^t ≡ t) (r : A [ t /0]Fm ≡ A∗) (d : Þ / Γ ⊢ ‵∀ A) →
              ‵unall ^t (casteqcut0Fm q₁ q₂ q₃ r) (cast p (‵∀_ & q₁) d) ≡
                cast p q₂ (‵unall t r d)
castunall refl refl refl refl r d = refl

castex : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A A∗ ^A∗ ^t t} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A) (q₂ : ^A∗ ≡ A∗)
           (q₃ : ^t ≡ t) (r : A [ t /0]Fm ≡ A∗) (d : Þ / Γ ⊢ A∗) →
           ‵ex ^t (casteqcut0Fm q₁ q₂ q₃ r) (cast p q₂ d) ≡
             cast p (‵∃_ & q₁) (‵ex t r d)
castex refl refl refl refl r d = refl

castletex : ∀ {Þ k} {Γ ^Γ : Fm§ k} {Γ∗ ^Γ∗ A ^A C ^C C∗ ^C∗} (p₁ : ^Γ ≡ Γ) (p₂ : ^Γ∗ ≡ Γ∗)
              (q₁ : ^A ≡ A) (q₂ : ^C ≡ C) (q₃ : ^C∗ ≡ C∗) (r₁ : Γ∗ ≡ wkFm§ Γ) (r₂ : C∗ ≡ wkFm C)
              (d : Þ / Γ ⊢ ‵∃ A) (e : Þ / Γ∗ , A ⊢ C∗) →
              ‵letex (casteqwkFm§ p₁ p₂ r₁) (casteqwkFm q₂ q₃ r₂)
                  (cast p₁ (‵∃_ & q₁) d) (cast (_,_ & p₂ ⊗ q₁) q₃ e) ≡
                cast p₁ q₂ (‵letex r₁ r₂ d e)
castletex refl refl refl refl refl r₁ r₂ d e = refl

castabortHA : ∀ {k} {Γ ^Γ : Fm§ k} {C ^C} (p : ^Γ ≡ Γ) (q : ^C ≡ C) (d : HA / Γ ⊢ ‵⊥) →
                ‵abortHA (cast p refl d) ≡ cast p q (‵abortHA d)
castabortHA refl refl d = refl

castmagicPA : ∀ {k} {Γ ^Γ : Fm§ k} {A ^A} (p : ^Γ ≡ Γ) (q : ^A ≡ A) (d : PA / Γ , ‵¬ A ⊢ ‵⊥) →
                ‵magicPA (cast (_,_ & p ⊗ (_‵⊃_ & q ⊗ refl)) refl d) ≡ cast p q (‵magicPA d)
castmagicPA refl refl d = refl

castrefl : ∀ {Þ k} {Γ ^Γ : Fm§ k} {t ^t} (p : ^Γ ≡ Γ) (q : ^t ≡ t) →
             ‵refl {Þ = Þ} ≡ cast p (_‵=_ & q ⊗ q) ‵refl
castrefl refl refl = refl

castsym : ∀ {Þ k} {Γ ^Γ : Fm§ k} {t ^t u ^u} (p : ^Γ ≡ Γ) (q₁ : ^t ≡ t) (q₂ : ^u ≡ u)
            (d : Þ / Γ ⊢ t ‵= u) →
            ‵sym (cast p (_‵=_ & q₁ ⊗ q₂) d) ≡ cast p (_‵=_ & q₂ ⊗ q₁) (‵sym d)
castsym refl refl refl d = refl

casttrans : ∀ {Þ k} {Γ ^Γ : Fm§ k} {s ^s t ^t u ^u} (p : ^Γ ≡ Γ) (q₁ : ^s ≡ s) (q₂ : ^t ≡ t)
              (q₃ : ^u ≡ u) (d : Þ / Γ ⊢ s ‵= t) (e : Þ / Γ ⊢ t ‵= u) →
              ‵trans (cast p (_‵=_ & q₁ ⊗ q₂) d) (cast p (_‵=_ & q₂ ⊗ q₃) e) ≡
                cast p (_‵=_ & q₁ ⊗ q₃) (‵trans d e)
casttrans refl refl refl refl d e = refl

castcong : ∀ {Þ k} {Γ ^Γ : Fm§ k} {n} {τ ^τ τ∗ ^τ∗ s ^s t∗ ^t∗} (p₁ : ^Γ ≡ Γ) (p₂ : ^τ ≡ τ)
             (p₃ : ^τ∗ ≡ τ∗) (q₁ : ^s ≡ s) (q₂ : ^t∗ ≡ t∗) (f : Prim n) (i : Fin n)
             (r₁ : poke i s τ ≡ τ∗) (r₂ : peek i τ ≡ t∗) (d : Þ / Γ ⊢ s ‵= t∗) →
             ‵cong f i (casteqpoke p₂ p₃ q₁ q₂ i r₁) (casteqpeek p₂ q₂ i r₂)
                 (cast p₁ (_‵=_ & q₁ ⊗ q₂) d) ≡
               cast p₁ (_‵=_ & (‵fun f & p₃) ⊗ ‵fun f & p₂) (‵cong f i r₁ r₂ d)
castcong refl refl refl refl refl f i r₁ r₂ d = refl

castdis : ∀ {Þ k} {Γ ^Γ : Fm§ k} {t ^t} (p : ^Γ ≡ Γ) (q : ^t ≡ t) →
            ‵dis {Þ = Þ} {t = ^t} ≡
              cast p (_‵⊃_ & (_‵=_ & (‵fun suc & (refl ⊗ q)) ⊗ refl) ⊗ refl) (‵dis {t = t})
castdis refl refl = refl

castinj : ∀ {Þ k} {Γ ^Γ : Fm§ k} {t ^t u ^u} (p : ^Γ ≡ Γ) (q₁ : ^t ≡ t) (q₂ : ^u ≡ u)
            (d : Þ / Γ ⊢ 𝕊 t ‵= 𝕊 u) →
            ‵inj (cast p (_‵=_ & (‵fun suc & (refl ⊗ q₁)) ⊗ ‵fun suc & (refl ⊗ q₂)) d) ≡
              cast p (_‵=_ & q₁ ⊗ q₂) (‵inj d)
castinj refl refl refl d = refl

castind : ∀ {Þ k} {Γ ^Γ : Fm§ k} {A ^A A∗ ^A∗ A∗∗ ^A∗∗} (p : ^Γ ≡ Γ) (q₁ : ^A ≡ A)
            (q₂ : ^A∗ ≡ A∗) (q₃ : ^A∗∗ ≡ A∗∗)
            (r₁ : A [ 𝟘 /0]Fm ≡ A∗) (r₂ : wkFm A [ 𝕊 (‵tvar zero) /1]Fm ≡ A∗∗)
            (d : Þ / Γ ⊢ A∗) (e : Þ / Γ ⊢ ‵∀ (A ‵⊃ A∗∗)) →
            ‵ind (casteqcut0Fm q₁ q₂ refl r₁) (casteqcut1Fm q₁ q₃ refl r₂)
                (cast p q₂ d) (cast p (‵∀_ & (_‵⊃_ & q₁ ⊗ q₃)) e) ≡
              cast p (‵∀_ & q₁) (‵ind r₁ r₂ d e)
castind refl refl refl refl r₁ r₂ d e = refl

castproj : ∀ {Þ k} {Γ ^Γ : Fm§ k} {n} {τ ^τ t∗ ^t∗} (p₁ : ^Γ ≡ Γ) (p₂ : ^τ ≡ τ) (q : ^t∗ ≡ t∗)
             (i : Fin n) (r : peek i τ ≡ t∗) →
             ‵proj i (casteqpeek p₂ q i r) ≡
               cast {Þ = Þ} p₁ (_‵=_ & (‵fun (proj i) & p₂) ⊗ q) (‵proj i r)
castproj refl refl refl i r = refl

castcomp : ∀ {Þ k} {Γ ^Γ : Fm§ k} {n m τ ^τ τ∗ ^τ∗} (p₁ : ^Γ ≡ Γ) (p₂ : ^τ ≡ τ) (p₃ : ^τ∗ ≡ τ∗)
             (g : Prim m) (φ : Prim§ n m) (r : for φ (λ f → ‵fun f τ) ≡ τ∗) →
             ‵comp {Þ = Þ} g φ (casteqfor p₂ p₃ φ r) ≡
               cast p₁ (_‵=_ & (‵fun (comp g φ) & p₂) ⊗ ‵fun g & p₃) (‵comp g φ r)
castcomp refl refl refl g φ r = refl

-- send help
castrec : ∀ {Þ k} {Γ ^Γ : Fm§ k} {n ^τ τ t ^t f g} (p₁ : ^Γ ≡ Γ) (p₂ : ^τ ≡ τ) (q : ^t ≡ t) →
            ‵rec {Þ = Þ} {n = n} f g ≡
              cast p₁
                (_‵∧_
                  & (_‵=_ & (‵fun (rec f g) & (_,_ & p₂ ⊗ refl)) ⊗ ‵fun f & p₂)
                  ⊗ (_‵=_
                      & (‵fun (rec f g) & (_,_ & p₂ ⊗ ‵fun suc & (_⊗_ {f = (∙ ,_)} refl q)))
                      ⊗ ‵fun g & (_,_ & (_,_ & p₂ ⊗ q) ⊗ ‵fun (rec f g) & (_,_ & p₂ ⊗ q))))
                (‵rec f g)
castrec refl refl refl = refl

-- casting for simultaneous substitutions of derivations
cast§ : ∀ {Þ k} {Γ ^Γ : Fm§ k} {Δ ^Δ} → ^Γ ≡ Γ → ^Δ ≡ Δ → Þ / Γ ⊢§ Δ → Þ / ^Γ ⊢§ ^Δ
cast§ refl refl δ = δ

castnil : ∀ {Þ k} {Γ ^Γ : Fm§ k} (p : ^Γ ≡ Γ) → ∙ ≡ cast§ {Þ = Þ} p refl ∙
castnil refl = refl

castcons : ∀ {Þ k} {Γ ^Γ Δ ^Δ : Fm§ k} {A ^A} (p₁ : ^Γ ≡ Γ) (p₂ : ^Δ ≡ Δ) (q : ^A ≡ A)
             (δ : Þ / Γ ⊢§ Δ) (d : Þ / Γ ⊢ A) →
             (cast§ p₁ p₂ δ , cast p₁ q d) ≡ cast§ p₁ (_,_ & p₂ ⊗ q) (δ , d)
castcons refl refl refl δ d = refl


----------------------------------------------------------------------------------------------------

-- 3.3. term renaming for derivations

tren : ∀ {Þ k k′ Γ A} (η : k ≤ k′) → Þ / Γ ⊢ A → Þ / renFm§ η Γ ⊢ renFm η A
tren η (‵var i)            = ‵var (tren∋ η i)
tren η (‵lam d)            = ‵lam (tren η d)
tren η (d ‵$ e)            = tren η d ‵$ tren η e
tren η (‵pair d e)         = ‵pair (tren η d) (tren η e)
tren η (‵fst d)            = ‵fst (tren η d)
tren η (‵snd d)            = ‵snd (tren η d)
tren η (‵left d)           = ‵left (tren η d)
tren η (‵right d)          = ‵right (tren η d)
tren η (‵either c d e)     = ‵either (tren η c) (tren η d) (tren η e)
tren η (‵all r d)          = ‵all (renFm§ (lift≤ η) & r ⋮ eqwkrenFm§ η _) (tren (lift≤ η) d)
tren η (‵unall t r d)      = ‵unall (renTm η t) (eqrencut0Fm η _ t ⋮ renFm η & r) (tren η d)
tren η (‵ex t r d)         = ‵ex (renTm η t) (eqrencut0Fm η _ t ⋮ renFm η & r) (tren η d)
tren η (‵letex r₁ r₂ d e)  = ‵letex (renFm§ (lift≤ η) & r₁ ⋮ eqwkrenFm§ η _)
                               (renFm (lift≤ η) & r₂ ⋮ eqwkrenFm η _) (tren η d) (tren (lift≤ η) e)
tren η (‵abortHA d)        = ‵abortHA (tren η d)
tren η (‵magicPA d)        = ‵magicPA (tren η d)
tren η ‵refl               = ‵refl
tren η (‵sym d)            = ‵sym (tren η d)
tren η (‵trans d e)        = ‵trans (tren η d) (tren η e)
tren η (‵cong f i r₁ r₂ d) = ‵cong f i (eqrenpokeTm η i _ _ ⋮ renTm§ η & r₁)
                               (eqrenpeekTm η i _ ⋮ renTm η & r₂) (tren η d)
tren η ‵dis                = ‵dis
tren η (‵inj d)            = ‵inj (tren η d)
tren η (‵ind r₁ r₂ d e)    = ‵ind (eqrencut0Fm η _ 𝟘 ⋮ renFm η & r₁)
                               (eqrencut1Fm η _ (𝕊 (‵tvar zero)) ⋮ renFm (lift≤ η) & r₂) (tren η d)
                               (tren η e)
tren η (‵proj i r)         = ‵proj i (eqrenpeekTm η i _ ⋮ renTm η & r)
tren η (‵comp g φ r)       = ‵comp g φ (eqrenforTm η φ _ ⋮ renTm§ η & r)
tren η (‵rec f g)          = ‵rec f g

twk : ∀ {Þ k} {Γ : Fm§ k} {A} → Þ / Γ ⊢ A → Þ / wkFm§ Γ ⊢ wkFm A
twk d = tren (wk≤ id≤) d

-- term renaming for simultanous substitutions of derivations
tren§ : ∀ {Þ k k′ Γ Δ} (η : k ≤ k′) → Þ / Γ ⊢§ Δ → Þ / renFm§ η Γ ⊢§ renFm§ η Δ
tren§ η ∙       = ∙
tren§ η (δ , d) = tren§ η δ , tren η d

twk§ : ∀ {Þ k} {Γ : Fm§ k} {Δ} → Þ / Γ ⊢§ Δ → Þ / wkFm§ Γ ⊢§ wkFm§ Δ
twk§ d = tren§ (wk≤ id≤) d

lidtren﹫ : ∀ {Þ k} {Γ : Fm§ k} {A} (d : Þ / Γ ⊢ A) →
             tren id≤ d ≡ cast (lidrenFm§ Γ) (lidrenFm A) d
lidtren﹫ (‵var i)            = ‵var & lidtren∋﹫ i
                             ⋮ castvar (lidrenFm§ _) (lidrenFm _) i
lidtren﹫ (‵lam d)            = ‵lam & lidtren﹫ d
                             ⋮ castlam (lidrenFm§ _) (lidrenFm _) (lidrenFm _) d
lidtren﹫ (d ‵$ e)            = _‵$_ & lidtren﹫ d ⊗ lidtren﹫ e
                             ⋮ castapp (lidrenFm§ _) (lidrenFm _) (lidrenFm _) d e
lidtren﹫ (‵pair d e)         = ‵pair & lidtren﹫ d ⊗ lidtren﹫ e
                             ⋮ castpair (lidrenFm§ _) (lidrenFm _) (lidrenFm _) d e
lidtren﹫ (‵fst d)            = ‵fst & lidtren﹫ d
                             ⋮ castfst (lidrenFm§ _) (lidrenFm _) (lidrenFm _) d
lidtren﹫ (‵snd d)            = ‵snd & lidtren﹫ d
                             ⋮ castsnd (lidrenFm§ _) (lidrenFm _) (lidrenFm _) d
lidtren﹫ (‵left d)           = ‵left & lidtren﹫ d
                             ⋮ castleft (lidrenFm§ _) (lidrenFm _) (lidrenFm _) d
lidtren﹫ (‵right d)          = ‵right & lidtren﹫ d
                             ⋮ castright (lidrenFm§ _) (lidrenFm _) (lidrenFm _) d
lidtren﹫ (‵either c d e)     = ‵either & lidtren﹫ c ⊗ lidtren﹫ d ⊗ lidtren﹫ e
                             ⋮ casteither (lidrenFm§ _) (lidrenFm _) (lidrenFm _)
                                 (lidrenFm _) c d e
lidtren﹫ (‵all r d)          = ‵all & uip _ _ ⊗ lidtren﹫ d
                             ⋮ castall (lidrenFm§ _) (lidrenFm§ _) (lidrenFm _) r d
lidtren﹫ (‵unall t r d)      = ‵unall (renTm id≤ t) & uip _ _ ⊗ lidtren﹫ d
                             ⋮ castunall (lidrenFm§ _) (lidrenFm _) (lidrenFm _)
                                 (lidrenTm t) r d
lidtren﹫ (‵ex t r d)         = ‵ex (renTm id≤ t) & uip _ _ ⊗ lidtren﹫ d
                             ⋮ castex (lidrenFm§ _) (lidrenFm _) (lidrenFm _) (lidrenTm t) r d
lidtren﹫ (‵letex r₁ r₂ d e)  = ‵letex & uip _ _ ⊗ uip _ _ ⊗ lidtren﹫ d ⊗ lidtren﹫ e
                             ⋮ castletex (lidrenFm§ _) (lidrenFm§ _) (lidrenFm _) (lidrenFm _)
                                 (lidrenFm _) r₁ r₂ d e
lidtren﹫ (‵abortHA d)        = ‵abortHA & lidtren﹫ d
                             ⋮ castabortHA (lidrenFm§ _) (lidrenFm _) d
lidtren﹫ (‵magicPA d)        = ‵magicPA & lidtren﹫ d
                             ⋮ castmagicPA (lidrenFm§ _) (lidrenFm _) d
lidtren﹫ ‵refl               = castrefl (lidrenFm§ _) (lidrenTm _)
lidtren﹫ (‵sym d)            = ‵sym & lidtren﹫ d
                             ⋮ castsym (lidrenFm§ _) (lidrenTm _) (lidrenTm _) d
lidtren﹫ (‵trans d e)        = ‵trans & lidtren﹫ d ⊗ lidtren﹫ e
                             ⋮ casttrans (lidrenFm§ _) (lidrenTm _) (lidrenTm _) (lidrenTm _) d e
lidtren﹫ (‵cong f i r₁ r₂ d) = ‵cong f i & uip _ _ ⊗ uip _ _ ⊗ lidtren﹫ d
                             ⋮ castcong (lidrenFm§ _) (lidrenTm§ _) (lidrenTm§ _) (lidrenTm _)
                                 (lidrenTm _) f i r₁ r₂ d
lidtren﹫ ‵dis                = castdis (lidrenFm§ _) (lidrenTm _)
lidtren﹫ (‵inj d)            = ‵inj & lidtren﹫ d
                             ⋮ castinj (lidrenFm§ _) (lidrenTm _) (lidrenTm _) d
lidtren﹫ (‵ind r₁ r₂ d e)    = ‵ind & uip _ _ ⊗ uip _ _ ⊗ lidtren﹫ d ⊗ lidtren﹫ e
                             ⋮ castind (lidrenFm§ _) (lidrenFm _) (lidrenFm _)
                                 (lidrenFm _) r₁ r₂ d e
lidtren﹫ (‵proj i r)         = ‵proj i & uip _ _
                             ⋮ castproj (lidrenFm§ _) (lidrenTm§ _) (lidrenTm _) i r
lidtren﹫ (‵comp g φ r)       = ‵comp g φ & uip _ _
                             ⋮ castcomp (lidrenFm§ _) (lidrenTm§ _) (lidrenTm§ _) g φ r
lidtren﹫ (‵rec f g)          = castrec (lidrenFm§ _) (lidrenTm§ _) (lidrenTm _)

lidtren : ∀ {Þ k} {Γ : Fm§ k} {A} (p₁ : renFm§ id≤ Γ ≡ Γ) (p₂ : renFm id≤ A ≡ A) (d : Þ / Γ ⊢ A) →
            tren id≤ d ≡ cast p₁ p₂ d
lidtren p₁ p₂ d = lidtren﹫ d
                ⋮ (λ p₁﹠ p₂﹠ → cast p₁﹠ p₂﹠ d) & uip _ _ ⊗ uip _ _

comptren﹫ : ∀ {Þ k k′ k″ Γ A} (η′ : k′ ≤ k″) (η : k ≤ k′) (d : Þ / Γ ⊢ A) →
              tren (η′ ∘≤ η) d ≡ cast (comprenFm§ η′ η Γ) (comprenFm η′ η A) (tren η′ (tren η d))
comptren﹫ η′ η (‵var i)            = ‵var & comptren∋﹫ η′ η i
                                   ⋮ castvar (comprenFm§ η′ η _) (comprenFm η′ η _)
                                       (tren∋ η′ (tren∋ η i))
comptren﹫ η′ η (‵lam d)            = ‵lam & comptren﹫ η′ η d
                                   ⋮ castlam (comprenFm§ η′ η _) (comprenFm η′ η _)
                                       (comprenFm η′ η _) (tren η′ (tren η d))
comptren﹫ η′ η (d ‵$ e)            = _‵$_ & comptren﹫ η′ η d ⊗ comptren﹫ η′ η e
                                   ⋮ castapp (comprenFm§ η′ η _) (comprenFm η′ η _)
                                       (comprenFm η′ η _) (tren η′ (tren η d))
                                       (tren η′ (tren η e))
comptren﹫ η′ η (‵pair d e)         = ‵pair & comptren﹫ η′ η d ⊗ comptren﹫ η′ η e
                                   ⋮ castpair (comprenFm§ η′ η _) (comprenFm η′ η _)
                                       (comprenFm η′ η _) (tren η′ (tren η d))
                                       (tren η′ (tren η e))
comptren﹫ η′ η (‵fst d)            = ‵fst & comptren﹫ η′ η d
                                   ⋮ castfst (comprenFm§ η′ η _) (comprenFm η′ η _)
                                       (comprenFm η′ η _) (tren η′ (tren η d))
comptren﹫ η′ η (‵snd d)            = ‵snd & comptren﹫ η′ η d
                                   ⋮ castsnd (comprenFm§ η′ η _) (comprenFm η′ η _)
                                       (comprenFm η′ η _) (tren η′ (tren η d))
comptren﹫ η′ η (‵left d)           = ‵left & comptren﹫ η′ η d
                                   ⋮ castleft (comprenFm§ η′ η _) (comprenFm η′ η _)
                                       (comprenFm η′ η _) (tren η′ (tren η d))
comptren﹫ η′ η (‵right d)          = ‵right & comptren﹫ η′ η d
                                   ⋮ castright (comprenFm§ η′ η _) (comprenFm η′ η _)
                                       (comprenFm η′ η _) (tren η′ (tren η d))
comptren﹫ η′ η (‵either c d e)     = ‵either
                                      & comptren﹫ η′ η c
                                      ⊗ comptren﹫ η′ η d
                                      ⊗ comptren﹫ η′ η e
                                   ⋮ casteither (comprenFm§ η′ η _) (comprenFm η′ η _)
                                       (comprenFm η′ η _) (comprenFm η′ η _) (tren η′ (tren η c))
                                       (tren η′ (tren η d)) (tren η′ (tren η e))
comptren﹫ η′ η (‵all r d)          = ‵all & uip _ _ ⊗ comptren﹫ (lift≤ η′) (lift≤ η) d
                                   ⋮ castall (comprenFm§ η′ η _) (comprenFm§ (lift≤ η′) (lift≤ η) _)
                                       (comprenFm (lift≤ η′) (lift≤ η) _)
                                       ( renFm§ (lift≤ η′) & (renFm§ (lift≤ η) & r ⋮ eqwkrenFm§ η _)
                                       ⋮ eqwkrenFm§ η′ (renFm§ η _)
                                       )
                                      (tren (lift≤ η′) (tren (lift≤ η) d))
comptren﹫ η′ η (‵unall t r d)      = ‵unall (renTm (η′ ∘≤ η) t) & uip _ _ ⊗ comptren﹫ η′ η d
                                   ⋮ castunall (comprenFm§ η′ η _)
                                       (comprenFm (lift≤ η′) (lift≤ η) _)
                                       (comprenFm η′ η _) (comprenTm η′ η t)
                                       ( eqrencut0Fm η′ (renFm (lift≤ η) _) (renTm η t)
                                       ⋮ renFm η′ & (eqrencut0Fm η _ t ⋮ renFm η & r)
                                       )
                                      (tren η′ (tren η d))
comptren﹫ η′ η (‵ex t r d)         = ‵ex (renTm (η′ ∘≤ η) t) & uip _ _ ⊗ comptren﹫ η′ η d
                                   ⋮ castex (comprenFm§ η′ η _) (comprenFm (lift≤ η′) (lift≤ η) _)
                                       (comprenFm η′ η _) (comprenTm η′ η t)
                                       ( eqrencut0Fm η′ (renFm (lift≤ η) _) (renTm η t)
                                       ⋮ renFm η′
                                           & ( eqrencut0Fm η _ t
                                             ⋮ renFm η & r
                                             )
                                       )
                                      (tren η′ (tren η d))
comptren﹫ η′ η (‵letex r₁ r₂ d e)  = ‵letex
                                      & uip _ _
                                      ⊗ uip _ _
                                      ⊗ comptren﹫ η′ η d
                                      ⊗ comptren﹫ (lift≤ η′) (lift≤ η) e
                                   ⋮ castletex (comprenFm§ η′ η _)
                                       (comprenFm§ (lift≤ η′) (lift≤ η) _)
                                       (comprenFm (lift≤ η′) (lift≤ η) _) (comprenFm η′ η _)
                                       (comprenFm (lift≤ η′) (lift≤ η) _)
                                       ( renFm§ (lift≤ η′)
                                           & (renFm§ (lift≤ η) & r₁ ⋮ eqwkrenFm§ η _)
                                       ⋮ eqwkrenFm§ η′ (renFm§ η _)
                                       )
                                       ( renFm (lift≤ η′) & (renFm (lift≤ η) & r₂ ⋮ eqwkrenFm η _)
                                       ⋮ eqwkrenFm η′ (renFm η _)
                                       )
                                       (tren η′ (tren η d)) (tren (lift≤ η′) (tren (lift≤ η) e))
comptren﹫ η′ η (‵abortHA d)        = ‵abortHA & comptren﹫ η′ η d
                                   ⋮ castabortHA (comprenFm§ η′ η _) (comprenFm η′ η _)
                                       (tren η′ (tren η d))
comptren﹫ η′ η (‵magicPA d)        = ‵magicPA & comptren﹫ η′ η d
                                   ⋮ castmagicPA (comprenFm§ η′ η _) (comprenFm η′ η _)
                                       (tren η′ (tren η d))
comptren﹫ η′ η ‵refl               = castrefl (comprenFm§ η′ η _) (comprenTm η′ η _)
comptren﹫ η′ η (‵sym d)            = ‵sym & comptren﹫ η′ η d
                                   ⋮ castsym (comprenFm§ η′ η _) (comprenTm η′ η _)
                                       (comprenTm η′ η _) (tren η′ (tren η d))
comptren﹫ η′ η (‵trans d e)        = ‵trans & comptren﹫ η′ η d ⊗ comptren﹫ η′ η e
                                   ⋮ casttrans (comprenFm§ η′ η _) (comprenTm η′ η _)
                                       (comprenTm η′ η _) (comprenTm η′ η _) (tren η′ (tren η d))
                                       (tren η′ (tren η e))
comptren﹫ η′ η (‵cong f i r₁ r₂ d) = ‵cong f i & uip _ _ ⊗ uip _ _ ⊗ comptren﹫ η′ η d
                                   ⋮ castcong (comprenFm§ η′ η _) (comprenTm§ η′ η _)
                                       (comprenTm§ η′ η _) (comprenTm η′ η _) (comprenTm η′ η _) f i
                                       ( eqrenpokeTm η′ i (renTm η _) (renTm§ η _)
                                       ⋮ renTm§ η′ & (eqrenpokeTm η i _ _ ⋮ renTm§ η & r₁)
                                       )
                                       ( eqrenpeekTm η′ i (renTm§ η _)
                                       ⋮ renTm η′ & (eqrenpeekTm η i _ ⋮ renTm η & r₂)
                                       )
                                       (tren η′ (tren η d))
comptren﹫ η′ η ‵dis                = castdis (comprenFm§ η′ η _) (comprenTm η′ η _)
comptren﹫ η′ η (‵inj d)            = ‵inj & comptren﹫ η′ η d
                                   ⋮ castinj (comprenFm§ η′ η _) (comprenTm η′ η _)
                                       (comprenTm η′ η _) (tren η′ (tren η d))
comptren﹫ η′ η (‵ind r₁ r₂ d e)    = ‵ind
                                      & uip _ _
                                      ⊗ uip _ _
                                      ⊗ comptren﹫ η′ η d
                                      ⊗ comptren﹫ η′ η e
                                   ⋮ castind (comprenFm§ η′ η _) (comprenFm (lift≤ η′) (lift≤ η) _)
                                       (comprenFm η′ η _) (comprenFm (lift≤ η′) (lift≤ η) _)
                                       ( eqrencut0Fm η′ (renFm (lift≤ η) _) 𝟘
                                       ⋮ renFm η′ & (eqrencut0Fm η _ 𝟘 ⋮ renFm η & r₁)
                                       )
                                       ( eqrencut1Fm η′ (renFm (lift≤ η) _)
                                           (‵fun suc (∙ , ‵tvar zero))
                                       ⋮ renFm (lift≤ η′)
                                           & ( eqrencut1Fm η _ (‵fun suc (∙ , ‵tvar zero))
                                             ⋮ renFm (lift≤ η) & r₂
                                             )
                                       )
                                       (tren η′ (tren η d)) (tren η′ (tren η e))
comptren﹫ η′ η (‵proj i r)         = ‵proj i & uip _ _
                                   ⋮ castproj (comprenFm§ η′ η _) (comprenTm§ η′ η _)
                                       (comprenTm η′ η _) i
                                       ( eqrenpeekTm η′ i (renTm§ η _)
                                       ⋮ renTm η′ & (eqrenpeekTm η i _ ⋮ renTm η & r)
                                       )
comptren﹫ η′ η (‵comp g φ r)       = ‵comp g φ & uip _ _
                                   ⋮ castcomp (comprenFm§ η′ η _) (comprenTm§ η′ η _)
                                       (comprenTm§ η′ η _) g φ
                                       ( eqrenforTm η′ φ (renTm§ η _)
                                       ⋮ renTm§ η′ & (eqrenforTm η φ _ ⋮ renTm§ η & r)
                                       )
comptren﹫ η′ η (‵rec f g)          = castrec (comprenFm§ η′ η _) (comprenTm§ η′ η _)
                                       (comprenTm η′ η _)

comptren : ∀ {Þ k k′ k″ Γ ^Γ A ^A} (η′ : k′ ≤ k″) (η : k ≤ k′)
             (p₁ : ^Γ ≡ renFm§ (η′ ∘≤ η) Γ) (q₁ : ^A ≡ renFm (η′ ∘≤ η) A)
             (p₂ : ^Γ ≡ renFm§ η′ (renFm§ η Γ)) (q₂ : ^A ≡ renFm η′ (renFm η A))
             (d : Þ / Γ ⊢ A) →
             cast p₁ q₁ (tren (η′ ∘≤ η) d) ≡ cast p₂ q₂ (tren η′ (tren η d))
comptren η′ η refl refl p₂ q₂ d = comptren﹫ η′ η d
                                ⋮ (λ p₂﹠ q₂﹠ → cast p₂﹠ q₂﹠ (tren η′ (tren η d)))
                                    & uip _ _ ⊗ uip _ _

comptren§﹫ : ∀ {Þ k k′ k″ Γ Δ} (η′ : k′ ≤ k″) (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
               tren§ (η′ ∘≤ η) δ ≡
                 cast§ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Δ) (tren§ η′ (tren§ η δ))
comptren§﹫ η′ η ∙       = castnil (comprenFm§ η′ η _)
comptren§﹫ η′ η (δ , d) = _,_ & comptren§﹫ η′ η δ ⊗ comptren﹫ η′ η d
                        ⋮ castcons (comprenFm§ η′ η _) (comprenFm§ η′ η _) (comprenFm η′ η _)
                            (tren§ η′ (tren§ η δ)) (tren η′ (tren η d))

comptren§ : ∀ {Þ k k′ k″ Γ ^Γ Δ ^Δ} (η′ : k′ ≤ k″) (η : k ≤ k′)
              (p₁ : ^Γ ≡ renFm§ (η′ ∘≤ η) Γ) (p₂ : ^Δ ≡ renFm§ (η′ ∘≤ η) Δ)
              (p₃ : ^Γ ≡ renFm§ η′ (renFm§ η Γ)) (p₄ : ^Δ ≡ renFm§ η′ (renFm§ η Δ))
              (δ : Þ / Γ ⊢§ Δ) →
              cast§ p₁ p₂ (tren§ (η′ ∘≤ η) δ) ≡ cast§ p₃ p₄ (tren§ η′ (tren§ η δ))
comptren§ η′ η refl refl p₃ p₄ δ = comptren§﹫ η′ η δ
                                 ⋮ (λ p₃﹠ p₄﹠ → cast§ p₃﹠ p₄﹠ (tren§ η′ (tren§ η δ)))
                                      & uip _ _ ⊗ uip _ _

ridtren : ∀ {Þ k k′ Γ A} (η : k ≤ k′) (i : Γ ∋ A) →
            tren {Þ = Þ} η (‵var i) ≡ ‵var (tren∋ η i)
ridtren η i = refl


----------------------------------------------------------------------------------------------------

-- 3.4. derivations: renaming

ren : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A} → Γ ⊆ Γ′ → Þ / Γ ⊢ A → Þ / Γ′ ⊢ A
ren η (‵var i)             = ‵var (ren∋ η i)
ren η (‵lam d)             = ‵lam (ren (lift⊆ η) d)
ren η (d ‵$ e)             = ren η d ‵$ ren η e
ren η (‵pair d e)          = ‵pair (ren η d) (ren η e)
ren η (‵fst d)             = ‵fst (ren η d)
ren η (‵snd d)             = ‵snd (ren η d)
ren η (‵left d)            = ‵left (ren η d)
ren η (‵right d)           = ‵right (ren η d)
ren η (‵either c d e)      = ‵either (ren η c) (ren (lift⊆ η) d) (ren (lift⊆ η) e)
ren η (‵all refl d)        = ‵all refl (ren (twk⊆ η) d)
ren η (‵unall t r d)       = ‵unall t r (ren η d)
ren η (‵ex t r d)          = ‵ex t r (ren η d)
ren η (‵letex refl r₂ d e) = ‵letex refl r₂ (ren η d) (ren (lift⊆ (twk⊆ η)) e)
ren η (‵abortHA d)         = ‵abortHA (ren η d)
ren η (‵magicPA d)         = ‵magicPA (ren (lift⊆ η) d)
ren η ‵refl                = ‵refl
ren η (‵sym d)             = ‵sym (ren η d)
ren η (‵trans d e)         = ‵trans (ren η d) (ren η e)
ren η (‵cong f i r₁ r₂ d)  = ‵cong f i r₁ r₂ (ren η d)
ren η ‵dis                 = ‵dis
ren η (‵inj d)             = ‵inj (ren η d)
ren η (‵ind r₁ r₂ d e)     = ‵ind r₁ r₂ (ren η d) (ren η e)
ren η (‵proj i r)          = ‵proj i r
ren η (‵comp g φ r)        = ‵comp g φ r
ren η (‵rec f g)           = ‵rec f g


----------------------------------------------------------------------------------------------------

-- 3.5. derivations: generic lemmas from RenKit

wk : ∀ {Þ k} {Γ : Fm§ k} {A C} → Þ / Γ ⊢ A → Þ / Γ , C ⊢ A
wk d = ren (wk⊆ id⊆) d

ren§ : ∀ {Þ k} {Γ Γ′ : Fm§ k} {Δ} → Γ ⊆ Γ′ → Þ / Γ ⊢§ Δ → Þ / Γ′ ⊢§ Δ
ren§ η ∙       = ∙
ren§ η (δ , d) = ren§ η δ , ren η d

wk§ : ∀ {Þ k} {Γ : Fm§ k} {Δ C} → Þ / Γ ⊢§ Δ → Þ / Γ , C ⊢§ Δ
wk§ δ = ren§ (wk⊆ id⊆) δ

lift§ : ∀ {Þ k} {Γ : Fm§ k} {Δ C} → Þ / Γ ⊢§ Δ → Þ / Γ , C ⊢§ Δ , C
lift§ δ = wk§ δ , ‵var zero

var§ : ∀ {Þ k} {Γ Γ′ : Fm§ k} → Γ ⊆ Γ′ → Þ / Γ′ ⊢§ Γ
var§ stop      = ∙
var§ (wk⊆ η)   = wk§ (var§ η)
var§ (lift⊆ η) = lift§ (var§ η)

-- TODO: check if changing this affects anything
id§ : ∀ {Þ k} {Γ : Fm§ k} → Þ / Γ ⊢§ Γ
-- id§ {Γ = ∙}     = ∙
-- id§ {Γ = Γ , A} = lift§ id§
id§ = var§ id⊆

sub∋ : ∀ {Þ k} {Γ Ξ : Fm§ k} {A} → Þ / Ξ ⊢§ Γ → Γ ∋ A → Þ / Ξ ⊢ A
sub∋ (σ , s) zero    = s
sub∋ (σ , s) (suc i) = sub∋ σ i


----------------------------------------------------------------------------------------------------

-- 3.6. derivations: substitution

sub : ∀ {Þ k} {Γ Ξ : Fm§ k} {A} → Þ / Ξ ⊢§ Γ → Þ / Γ ⊢ A → Þ / Ξ ⊢ A
sub σ (‵var i)             = sub∋ σ i
sub σ (‵lam d)             = ‵lam (sub (lift§ σ) d)
sub σ (d ‵$ e)             = sub σ d ‵$ sub σ e
sub σ (‵pair d e)          = ‵pair (sub σ d) (sub σ e)
sub σ (‵fst d)             = ‵fst (sub σ d)
sub σ (‵snd d)             = ‵snd (sub σ d)
sub σ (‵left d)            = ‵left (sub σ d)
sub σ (‵right d)           = ‵right (sub σ d)
sub σ (‵either c d e)      = ‵either (sub σ c) (sub (lift§ σ) d) (sub (lift§ σ) e)
sub σ (‵all refl d)        = ‵all refl (sub (twk§ σ) d)
sub σ (‵unall t r d)       = ‵unall t r (sub σ d)
sub σ (‵ex t r d)          = ‵ex t r (sub σ d)
sub σ (‵letex refl r₂ d e) = ‵letex refl r₂ (sub σ d) (sub (lift§ (twk§ σ)) e)
sub σ (‵abortHA d)         = ‵abortHA (sub σ d)
sub σ (‵magicPA d)         = ‵magicPA (sub (lift§ σ) d)
sub σ ‵refl                = ‵refl
sub σ (‵sym d)             = ‵sym (sub σ d)
sub σ (‵trans d e)         = ‵trans (sub σ d) (sub σ e)
sub σ (‵cong f i r₁ r₂ d)  = ‵cong f i r₁ r₂ (sub σ d)
sub σ ‵dis                 = ‵dis
sub σ (‵inj d)             = ‵inj (sub σ d)
sub σ (‵ind r₁ r₂ d e)     = ‵ind r₁ r₂ (sub σ d) (sub σ e)
sub σ (‵proj i r)          = ‵proj i r
sub σ (‵comp g φ r)        = ‵comp g φ r
sub σ (‵rec f g)           = ‵rec f g


----------------------------------------------------------------------------------------------------

-- 3.7. derivations: generic lemmas from SubKit

sub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} → Þ / Ξ ⊢§ Γ → Þ / Γ ⊢§ Δ → Þ / Ξ ⊢§ Δ
sub§ σ ∙       = ∙
sub§ σ (δ , d) = sub§ σ δ , sub σ d

_[_/0] : ∀ {Þ k} {Γ : Fm§ k} {A B} → Þ / Γ , A ⊢ B → Þ / Γ ⊢ A → Þ / Γ ⊢ B
d [ s /0] = sub (id§ , s) d

get§ : ∀ {Þ k} {Γ Δ Δ′ : Fm§ k} → Δ ⊆ Δ′ → Þ / Γ ⊢§ Δ′ → Þ / Γ ⊢§ Δ
get§ stop      δ       = δ
get§ (wk⊆ η)   (δ , d) = get§ η δ
get§ (lift⊆ η) (δ , d) = get§ η δ , d


----------------------------------------------------------------------------------------------------

-- 3.8. derivations: fundamental renaming lemmas

lidren : ∀ {Þ k} {Γ : Fm§ k} {A} (d : Þ / Γ ⊢ A) → ren id⊆ d ≡ d
lidren (‵var i)                = ‵var & idren∋ i
lidren (‵lam d)                = ‵lam & lidren d
lidren (d ‵$ e)                = _‵$_ & lidren d ⊗ lidren e
lidren (‵pair d e)             = ‵pair & lidren d ⊗ lidren e
lidren (‵fst d)                = ‵fst & lidren d
lidren (‵snd d)                = ‵snd & lidren d
lidren (‵left d)               = ‵left & lidren d
lidren (‵right d)              = ‵right & lidren d
lidren (‵either c d e)         = ‵either & lidren c ⊗ lidren d ⊗ lidren e
lidren (‵all refl d)           = ‵all refl & ((λ η﹠ → ren η﹠ d) & ridtren⊆ (wk≤ id≤) ⋮ lidren d)
lidren (‵unall t refl d)       = ‵unall t refl & lidren d
lidren (‵ex t refl d)          = ‵ex t refl & lidren d
lidren (‵letex refl refl d e)  = ‵letex refl refl
                                   & lidren d
                                   ⊗ ((λ η﹠ → ren (lift⊆ η﹠) e) & ridtren⊆ (wk≤ id≤) ⋮ lidren e)
lidren (‵abortHA d)            = ‵abortHA & lidren d
lidren (‵magicPA d)            = ‵magicPA & lidren d
lidren ‵refl                   = refl
lidren (‵sym d)                = ‵sym & lidren d
lidren (‵trans d e)            = ‵trans & lidren d ⊗ lidren e
lidren (‵cong f i refl refl d) = ‵cong f i refl refl & lidren d
lidren ‵dis                    = refl
lidren (‵inj d)                = ‵inj & lidren d
lidren (‵ind refl refl d e)    = ‵ind refl refl & lidren d ⊗ lidren e
lidren (‵proj i refl)          = refl
lidren (‵comp g φ refl)        = refl
lidren (‵rec f g)              = refl

compren : ∀ {Þ k} {Γ Γ′ Γ″ : Fm§ k} {A} (η′ : Γ′ ⊆ Γ″) (η : Γ ⊆ Γ′) (d : Þ / Γ ⊢ A) →
            ren (η′ ∘⊆ η) d ≡ ren η′ (ren η d)
compren η′ η (‵var i)                = ‵var & compren∋ η′ η i
compren η′ η (‵lam d)                = ‵lam & compren (lift⊆ η′) (lift⊆ η) d
compren η′ η (d ‵$ e)                = _‵$_ & compren η′ η d ⊗ compren η′ η e
compren η′ η (‵pair d e)             = ‵pair & compren η′ η d ⊗ compren η′ η e
compren η′ η (‵fst d)                = ‵fst & compren η′ η d
compren η′ η (‵snd d)                = ‵snd & compren η′ η d
compren η′ η (‵left d)               = ‵left & compren η′ η d
compren η′ η (‵right d)              = ‵right & compren η′ η d
compren η′ η (‵either c d e)         = ‵either
                                         & compren η′ η c
                                         ⊗ compren (lift⊆ η′) (lift⊆ η) d
                                         ⊗ compren (lift⊆ η′) (lift⊆ η) e
compren η′ η (‵all refl d)           = ‵all refl
                                         & ( (λ η﹠ → ren η﹠ d) & rcomptren⊆ (wk≤ id≤) η′ η
                                           ⋮ compren (twk⊆ η′) (twk⊆ η) d
                                           )
compren η′ η (‵unall t refl d)       = ‵unall t refl & compren η′ η d
compren η′ η (‵ex t refl d)          = ‵ex t refl & compren η′ η d
compren η′ η (‵letex refl refl d e)  = ‵letex refl refl
                                         & compren η′ η d
                                         ⊗ ( (λ η﹠ → ren (lift⊆ η﹠) e) & rcomptren⊆ (wk≤ id≤) η′ η
                                           ⋮ compren (lift⊆ (twk⊆ η′)) (lift⊆ (twk⊆ η)) e
                                           )
compren η′ η (‵abortHA d)            = ‵abortHA & compren η′ η d
compren η′ η (‵magicPA d)            = ‵magicPA & compren (lift⊆ η′) (lift⊆ η) d
compren η′ η ‵refl                   = refl
compren η′ η (‵sym d)                = ‵sym & compren η′ η d
compren η′ η (‵trans d e)            = ‵trans & compren η′ η d ⊗ compren η′ η e
compren η′ η (‵cong f i refl refl d) = ‵cong f i refl refl & compren η′ η d
compren η′ η ‵dis                    = refl
compren η′ η (‵inj d)                = ‵inj & compren η′ η d
compren η′ η (‵ind refl refl d e)    = ‵ind refl refl & compren η′ η d ⊗ compren η′ η e
compren η′ η (‵proj i refl)          = refl
compren η′ η (‵comp g φ refl)        = refl
compren η′ η (‵rec f g)              = refl

ridren : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A} (η : Γ ⊆ Γ′) (i : Γ ∋ A) →
           ren {Þ = Þ} η (‵var i) ≡ ‵var (ren∋ η i)
ridren η i = refl

ridsub : ∀ {Þ k} {Γ Ξ : Fm§ k} {A} (σ : Þ / Ξ ⊢§ Γ) (i : Γ ∋ A) →
           sub σ (‵var i) ≡ sub∋ σ i
ridsub σ i = refl


----------------------------------------------------------------------------------------------------

-- 3.9. TODO: title this section
-- TODO: clean this up

castid⊆ : ∀ {k} {Γ Γ′ : Fm§ k} → Γ ≡ Γ′ → Γ ⊆ Γ′
castid⊆ p = cast⊆ p refl id⊆

-- TODO: rename this
castid⊆-pair : ∀ {k} {Γ ^Γ : Fm§ k} {C ^C} (p : Γ ≡ ^Γ) (q : C ≡ ^C) →
               castid⊆ ((^Γ ,_) & q) ∘⊆ lift⊆ (castid⊆ p) ≡ castid⊆ (_,_ & p ⊗ q)
castid⊆-pair refl refl = lift⊆ & lid⊆ id⊆

-- TODO: rename this
castid⊆-pair-alt : ∀ {k} {Γ ^Γ : Fm§ k} {C ^C} (p : Γ ≡ ^Γ) (q : C ≡ ^C) →
                   lift⊆ (castid⊆ p) ∘⊆ castid⊆ ((Γ ,_) & q) ≡ castid⊆ (_,_ & p ⊗ q)
castid⊆-pair-alt refl refl = lift⊆ & lid⊆ id⊆

-- TODO: rename this
castid⊆-eat : ∀ {k} {Γ ^Γ : Fm§ k} {C ^C} (q : C ≡ ^C) (η : Γ ⊆ ^Γ) →
              castid⊆ ((^Γ ,_) & q) ∘⊆ wk⊆ η ≡ wk⊆ η
castid⊆-eat refl η = wk⊆ & lid⊆ η

-- TODO: rename this
castid⊆-slide : ∀ {k} {Γ ^Γ : Fm§ k} {C ^C} (q : C ≡ ^C) (η : Γ ⊆ ^Γ) →
                castid⊆ ((^Γ ,_) & q) ∘⊆ lift⊆ η ≡ lift⊆ η ∘⊆ castid⊆ ((Γ ,_) & q)
castid⊆-slide refl η = lift⊆ & (lid⊆ η ⋮ rid⊆ η ⁻¹)

-- castid⊆-trans : ∀ {k} {Γ Γ′ Γ″ : Fm§ k} (e₂ : Γ ≡ Γ′) (e₁ : Γ′ ≡ Γ″) →
--                 castid⊆ (e₂ ⋮ e₁) ≡ castid⊆ e₁ ∘⊆ castid⊆ e₂
-- castid⊆-trans refl refl = lid⊆ id⊆ ⁻¹

-- castid⊆-cancel : ∀ {k} {Γ Γ′ : Fm§ k} (e : Γ ≡ Γ′) → castid⊆ e ∘⊆ castid⊆ (e ⁻¹) ≡ id⊆
-- castid⊆-cancel refl = lid⊆ id⊆

-- castid⊆-cancel-alt : ∀ {k} {Γ Γ′ : Fm§ k} (e : Γ ≡ Γ′) → castid⊆ (e ⁻¹) ∘⊆ castid⊆ e ≡ id⊆
-- castid⊆-cancel-alt refl = lid⊆ id⊆

-- castid⊆-ren : ∀ {k k′} {Γ Γ′ : Fm§ k} {η η′ : k ≤ k′} (ζ : Γ ⊆ Γ′) (e : η ≡ η′) →
--                 castid⊆ ((flip renFm§ Γ′) & e) ∘⊆ tren⊆ η ζ ≡
--                   tren⊆ η′ ζ ∘⊆ castid⊆ ((flip renFm§ Γ) & e)
-- castid⊆-ren {η = η} {η′ = η′} ζ refl = (lid⊆ (tren⊆ η ζ) ⋮ rid⊆ (tren⊆ η ζ) ⁻¹)


-- TODO: rename this
eqall : ∀ {Þ k} {Γ : Fm§ k} {Γ∗ A} (r : Γ∗ ≡ wkFm§ Γ) (d : Þ / Γ∗ ⊢ A) →
          ‵all refl (ren (castid⊆ r) d) ≡ ‵all r d
eqall refl d = ‵all refl & lidren d

-- TODO: rename this
eqletex : ∀ {Þ k} {Γ : Fm§ k} {Γ∗ A C C∗} (r₁ : Γ∗ ≡ wkFm§ Γ) (r₂ : C∗ ≡ wkFm C)
            (d : Þ / Γ ⊢ ‵∃ A) (e : Þ / Γ∗ , A ⊢ C∗) →
            ‵letex refl r₂ d (ren (lift⊆ (castid⊆ r₁)) e) ≡ ‵letex r₁ r₂ d e
eqletex refl r₂ d e = ‵letex refl r₂ d & lidren e


----------------------------------------------------------------------------------------------------

-- 3.10. interaction between term renaming and derivation renaming

-- TODO: rename this
untitled1 : ∀ {k k′ Γ Γ′} (η : k ≤ k′) (ζ : Γ ⊆ Γ′) →
              twk⊆ (tren⊆ η ζ) ∘⊆ castid⊆ (eqwkrenFm§ η Γ) ≡
                castid⊆ (eqwkrenFm§ η Γ′) ∘⊆ tren⊆ (lift≤ η) (twk⊆ ζ)
untitled1 η stop      = refl
untitled1 η (wk⊆ ζ)   = castid⊆-eat (eqwkrenFm η _)
                          (twk⊆ (tren⊆ η ζ) ∘⊆ castid⊆ (eqwkrenFm§ η _)) ⁻¹
                      ⋮ (λ η﹠ → castid⊆ ((wkFm§ (renFm§ η _) ,_)
                          & eqwkrenFm η _) ∘⊆ wk⊆ η﹠) & untitled1 η ζ
                      ⋮ ass⊆ (castid⊆ ((wkFm§ (renFm§ η _) ,_) & eqwkrenFm η _))
                          (lift⊆ (castid⊆ (eqwkrenFm§ η _))) (wk⊆ (tren⊆ (lift≤ η) (twk⊆ ζ)))
                      ⋮ (_∘⊆ (wk⊆ (tren⊆ (lift≤ η) (twk⊆ ζ))))
                          & castid⊆-pair (eqwkrenFm§ η _) (eqwkrenFm η _)
untitled1 η (lift⊆ ζ) = (twk⊆ (lift⊆ (tren⊆ η ζ)) ∘⊆_)
                          & castid⊆-pair-alt (eqwkrenFm§ η _) (eqwkrenFm η _) ⁻¹
                      ⋮ ass⊆ (twk⊆ (lift⊆ (tren⊆ η ζ))) (lift⊆ (castid⊆ (eqwkrenFm§ η _)))
                          (castid⊆ ((renFm§ (lift≤ η) (wkFm§ _) ,_) & eqwkrenFm η _))
                      ⋮ castid⊆-slide (eqwkrenFm η _)
                          (twk⊆ (tren⊆ η ζ) ∘⊆ castid⊆ (eqwkrenFm§ η _)) ⁻¹
                      ⋮ (λ η﹠ → castid⊆ ((wkFm§ (renFm§ η _) ,_) & eqwkrenFm η _) ∘⊆ lift⊆ η﹠)
                          & untitled1 η ζ
                      ⋮ ass⊆ (castid⊆ ((wkFm§ (renFm§ η _) ,_) & eqwkrenFm η _))
                          (lift⊆ (castid⊆ (eqwkrenFm§ η _))) (lift⊆ (tren⊆ (lift≤ η) (twk⊆ ζ)))
                      ⋮ (_∘⊆ lift⊆ (tren⊆ (lift≤ η) (twk⊆ ζ)))
                          & castid⊆-pair (eqwkrenFm§ η _) (eqwkrenFm η _)

eqtrenren∋ : ∀ {k k′ Γ Γ′ A} (η : k ≤ k′) (ζ : Γ ⊆ Γ′) (i : Γ ∋ A) →
               ren∋ (tren⊆ η ζ) (tren∋ η i) ≡ tren∋ η (ren∋ ζ i)
eqtrenren∋ η (wk⊆ ζ)   i       = suc & eqtrenren∋ η ζ i
eqtrenren∋ η (lift⊆ ζ) zero    = refl
eqtrenren∋ η (lift⊆ ζ) (suc i) = suc & eqtrenren∋ η ζ i

eqtrenren : ∀ {Þ k k′ Γ Γ′ A} (η : k ≤ k′) (ζ : Γ ⊆ Γ′) (d : Þ / Γ ⊢ A) →
              ren (tren⊆ η ζ) (tren η d) ≡ tren η (ren ζ d)
eqtrenren η ζ (‵var i)                = ‵var & eqtrenren∋ η ζ i
eqtrenren η ζ (‵lam d)                = ‵lam & eqtrenren η (lift⊆ ζ) d
eqtrenren η ζ (d ‵$ e)                = _‵$_ & eqtrenren η ζ d ⊗ eqtrenren η ζ e
eqtrenren η ζ (‵pair d e)             = ‵pair & eqtrenren η ζ d ⊗ eqtrenren η ζ e
eqtrenren η ζ (‵fst d)                = ‵fst & eqtrenren η ζ d
eqtrenren η ζ (‵snd d)                = ‵snd & eqtrenren η ζ d
eqtrenren η ζ (‵left d)               = ‵left & eqtrenren η ζ d
eqtrenren η ζ (‵right d)              = ‵right & eqtrenren η ζ d
eqtrenren η ζ (‵either c d e)         = ‵either
                                          & eqtrenren η ζ c
                                          ⊗ eqtrenren η (lift⊆ ζ) d
                                          ⊗ eqtrenren η (lift⊆ ζ) e
eqtrenren η ζ (‵all refl d)           = ren (tren⊆ η ζ)
                                          & ( (λ r﹠ → ‵all r﹠ (tren (lift≤ η) d)) & uip _ _
                                            ⋮ eqall (eqwkrenFm§ η _) (tren (lift≤ η) d) ⁻¹
                                            )
                                      ⋮ ‵all refl
                                          & ( compren (twk⊆ (tren⊆ η ζ)) (castid⊆ (eqwkrenFm§ η _))
                                                (tren (lift≤ η) d) ⁻¹
                                            ⋮ (λ η﹠ → ren η﹠ (tren (lift≤ η) d)) & untitled1 η ζ
                                            ⋮ compren (castid⊆ (eqwkrenFm§ η _))
                                                (tren⊆ (lift≤ η) (twk⊆ ζ)) (tren (lift≤ η) d)
                                            )
                                      ⋮ eqall (eqwkrenFm§ η _) (ren (tren⊆ (lift≤ η) (twk⊆ ζ))
                                          (tren (lift≤ η) d))
                                      ⋮ ‵all (eqwkrenFm§ η _) & eqtrenren (lift≤ η) (twk⊆ ζ) d
                                      ⋮ (λ r﹠ → ‵all r﹠ (tren (lift≤ η)
                                            (ren (tren⊆ (wk≤ id≤) ζ) d)))
                                          & uip _ _
eqtrenren η ζ (‵unall t refl d)       = ‵unall (renTm η t) (eqrencut0Fm η _ t ⋮ refl)
                                          & eqtrenren η ζ d
eqtrenren η ζ (‵ex t refl d)          = ‵ex (renTm η t) (eqrencut0Fm η _ t ⋮ refl)
                                          & eqtrenren η ζ d
eqtrenren η ζ (‵letex refl refl d e)  = ren (tren⊆ η ζ)
                                          & ( (λ r₁﹠ r₂﹠ → ‵letex r₁﹠ r₂﹠ (tren η d)
                                                  (tren (lift≤ η) e))
                                                & uip _ _
                                                ⊗ uip _ _
                                            ⋮ eqletex (eqwkrenFm§ η _) (eqwkrenFm η _) (tren η d)
                                                (tren (lift≤ η) e) ⁻¹
                                            )
                                      ⋮ ‵letex refl (eqwkrenFm η _) (ren (tren⊆ η ζ) (tren η d))
                                          & ( compren (lift⊆ (twk⊆ (tren⊆ η ζ)))
                                                (lift⊆ (castid⊆ (eqwkrenFm§ η _)))
                                                (tren (lift≤ η) e) ⁻¹
                                            ⋮ (λ η﹠ → ren (lift⊆ η﹠) (tren (lift≤ η) e))
                                                & untitled1 η ζ
                                            ⋮ compren (lift⊆ (castid⊆ (eqwkrenFm§ η _)))
                                                (tren⊆ (lift≤ η) (lift⊆ (twk⊆ ζ)))
                                                (tren (lift≤ η) e)
                                            )
                                      ⋮ eqletex (eqwkrenFm§ η _) (eqwkrenFm η _)
                                          (ren (tren⊆ η ζ) (tren η d))
                                          (ren (tren⊆ (lift≤ η) (lift⊆ (twk⊆ ζ)))
                                            (tren (lift≤ η) e))
                                      ⋮ ‵letex
                                          & uip _ _
                                          ⊗ uip _ _
                                          ⊗ eqtrenren η ζ d
                                          ⊗ eqtrenren (lift≤ η) (lift⊆ (twk⊆ ζ)) e
eqtrenren η ζ (‵abortHA d)            = ‵abortHA & eqtrenren η ζ d
eqtrenren η ζ (‵magicPA d)            = ‵magicPA & eqtrenren η (lift⊆ ζ) d
eqtrenren η ζ ‵refl                   = refl
eqtrenren η ζ (‵sym d)                = ‵sym & eqtrenren η ζ d
eqtrenren η ζ (‵trans d e)            = ‵trans & eqtrenren η ζ d ⊗ eqtrenren η ζ e
eqtrenren η ζ (‵cong f i refl refl d) = ‵cong f i (eqrenpokeTm η i _ _ ⋮ refl)
                                            (eqrenpeekTm η i _ ⋮ refl)
                                          & eqtrenren η ζ d
eqtrenren η ζ ‵dis                    = refl
eqtrenren η ζ (‵inj d)                = ‵inj & eqtrenren η ζ d
eqtrenren η ζ (‵ind refl refl d e)    = ‵ind (eqrencut0Fm η _ 𝟘 ⋮ refl)
                                            (eqrencut1Fm η _ (𝕊 (‵tvar zero)) ⋮ refl)
                                          & eqtrenren η ζ d
                                          ⊗ eqtrenren η ζ e
eqtrenren η ζ (‵proj i refl)          = refl
eqtrenren η ζ (‵comp g φ refl)        = refl
eqtrenren η ζ (‵rec f g)              = refl

eqtrenren§ : ∀ {Þ k k′ Γ Γ′ Δ} (η : k ≤ k′) (ζ : Γ ⊆ Γ′) (δ : Þ / Γ ⊢§ Δ) →
               ren§ (tren⊆ η ζ) (tren§ η δ) ≡ tren§ η (ren§ ζ δ)
eqtrenren§ η ζ ∙       = refl
eqtrenren§ η ζ (δ , d) = _,_ & eqtrenren§ η ζ δ ⊗ eqtrenren η ζ d

eqtrenget§ : ∀ {Þ k k′ Γ Δ Δ′} (η : k ≤ k′) (ζ : Δ ⊆ Δ′) (δ : Þ / Γ ⊢§ Δ′) →
               get§ (tren⊆ η ζ) (tren§ η δ) ≡ tren§ η (get§ ζ δ)
eqtrenget§ η stop      δ       = refl
eqtrenget§ η (wk⊆ ζ)   (δ , d) = eqtrenget§ η ζ δ
eqtrenget§ η (lift⊆ ζ) (δ , d) = (_, tren η d) & eqtrenget§ η ζ δ

ridtren§ : ∀ {Þ k k′ Γ} (η : k ≤ k′) → tren§ {Þ = Þ} {Γ = Γ} η id§ ≡ id§
ridtren§ {Γ = ∙}     η = refl
ridtren§ {Γ = Γ , A} η = (_, ‵var zero)
                           & ( eqtrenren§ η (wk⊆ id⊆) id§ ⁻¹
                             ⋮ ren§ & (wk⊆ & ridtren⊆ η) ⊗ ridtren§ η
                             )


----------------------------------------------------------------------------------------------------

-- 3.11. derivations: generic lemmas from RenSubKit1

lidren§ : ∀ {Þ k} {Γ Δ : Fm§ k} (δ : Þ / Γ ⊢§ Δ) → ren§ id⊆ δ ≡ δ
lidren§ ∙       = refl
lidren§ (δ , d) = _,_ & lidren§ δ ⊗ lidren d

compren§ : ∀ {Þ k} {Γ Γ′ Γ″ Δ : Fm§ k} (η′ : Γ′ ⊆ Γ″) (η : Γ ⊆ Γ′) (δ : Þ / Γ ⊢§ Δ) →
             ren§ (η′ ∘⊆ η) δ ≡ ren§ η′ (ren§ η δ)
compren§ η′ η ∙       = refl
compren§ η′ η (δ , d) = _,_ & compren§ η′ η δ ⊗ compren η′ η d

eqwkren : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A C} (η : Γ ⊆ Γ′) (d : Þ / Γ ⊢ A) →
            ren (lift⊆ η) (wk {C = C} d) ≡ wk (ren η d)
eqwkren η d = compren (lift⊆ η) (wk⊆ id⊆) d ⁻¹
            ⋮ (λ η﹠ → ren (wk⊆ η﹠) d) & (rid⊆ η ⋮ lid⊆ η ⁻¹)
            ⋮ compren (wk⊆ id⊆) η d

eqwkren§ : ∀ {Þ k} {Γ Γ′ Δ : Fm§ k} {C} (η : Γ ⊆ Γ′) (δ : Þ / Γ ⊢§ Δ) →
             ren§ (lift⊆ η) (wk§ {C = C} δ) ≡ wk§ (ren§ η δ)
eqwkren§ η ∙       = refl
eqwkren§ η (δ , d) = _,_ & eqwkren§ η δ ⊗ eqwkren η d

eqliftren§ : ∀ {Þ k} {Γ Γ′ Δ : Fm§ k} {C} (η : Γ ⊆ Γ′) (δ : Þ / Γ ⊢§ Δ) →
               ren§ (lift⊆ η) (lift§ {C = C} δ) ≡ lift§ (ren§ η δ)
eqliftren§ η δ = _,_ & eqwkren§ η δ ⊗ ridren (lift⊆ η) zero

ridren§ : ∀ {Þ k} {Γ Γ′ : Fm§ k} (η : Γ ⊆ Γ′) → ren§ {Þ = Þ} η id§ ≡ var§ η
ridren§ stop      = refl
ridren§ (wk⊆ η)   = (λ η﹠ → ren§ (wk⊆ η﹠) id§) & lid⊆ η ⁻¹
                  ⋮ compren§ (wk⊆ id⊆) η id§
                  ⋮ wk§ & ridren§ η
ridren§ (lift⊆ η) = _,_
                      & ( eqwkren§ η id§
                        ⋮ wk§ & ridren§ η
                        )
                      ⊗ ridren (lift⊆ η) zero

eqrensub∋ : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A} (η : Ξ ⊆ Ξ′) (σ : Þ / Ξ ⊢§ Γ) (i : Γ ∋ A) →
              sub∋ (ren§ η σ) i ≡ ren η (sub∋ σ i)
eqrensub∋ η (σ , s) zero    = refl
eqrensub∋ η (σ , s) (suc i) = eqrensub∋ η σ i

eqsubren∋ : ∀ {Þ k} {Γ Γ′ Ξ : Fm§ k} {A} (σ : Þ / Ξ ⊢§ Γ′) (η : Γ ⊆ Γ′) (i : Γ ∋ A) →
              sub∋ (get§ η σ) i ≡ sub∋ σ (ren∋ η i)
eqsubren∋ ∙       stop      i       = refl
eqsubren∋ (σ , s) (wk⊆ η)   i       = eqsubren∋ σ η i
eqsubren∋ (σ , s) (lift⊆ η) zero    = refl
eqsubren∋ (σ , s) (lift⊆ η) (suc i) = eqsubren∋ σ η i

idsub∋ : ∀ {Þ k} {Γ : Fm§ k} {A} (i : Γ ∋ A) → sub∋ {Þ = Þ} id§ i ≡ ‵var i
idsub∋ zero    = refl
idsub∋ (suc i) = eqrensub∋ (wk⊆ id⊆) id§ i
               ⋮ wk & idsub∋ i
               ⋮ ridren (wk⊆ id⊆) i
               ⋮ (λ i﹠ → ‵var (suc i﹠)) & idren∋ i

compsub∋ : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ) (i : Γ ∋ A) →
             sub∋ (sub§ σ′ σ) i ≡ sub σ′ (sub∋ σ i)
compsub∋ σ′ (σ , s) zero    = refl
compsub∋ σ′ (σ , s) (suc i) = compsub∋ σ′ σ i

lidget§ : ∀ {Þ k} {Γ Δ : Fm§ k} (δ : Þ / Γ ⊢§ Δ) → get§ id⊆ δ ≡ δ
lidget§ ∙       = refl
lidget§ (δ , d) = (_, d) & lidget§ δ

compget§ : ∀ {Þ k} {Γ Δ Δ′ Δ″ : Fm§ k} (η : Δ ⊆ Δ′) (η′ : Δ′ ⊆ Δ″) (δ : Þ / Γ ⊢§ Δ″) →
             get§ (η′ ∘⊆ η) δ ≡ get§ η (get§ η′ δ)
compget§ η         stop       ∙       = refl
compget§ η         (wk⊆ η′)   (δ , d) = compget§ η η′ δ
compget§ (wk⊆ η)   (lift⊆ η′) (δ , d) = compget§ η η′ δ
compget§ (lift⊆ η) (lift⊆ η′) (δ , d) = (_, d) & compget§ η η′ δ

eqrenget§ : ∀ {Þ k} {Γ Γ′ Δ Δ′ : Fm§ k} (η : Γ ⊆ Γ′) (η′ : Δ ⊆ Δ′) (δ : Þ / Γ ⊢§ Δ′) →
              get§ η′ (ren§ η δ) ≡ ren§ η (get§ η′ δ)
eqrenget§ η stop       ∙       = refl
eqrenget§ η (wk⊆ η′)   (δ , d) = eqrenget§ η η′ δ
eqrenget§ η (lift⊆ η′) (δ , d) = (_, ren η d) & eqrenget§ η η′ δ

eqwkget§ : ∀ {Þ k} {Γ Δ Δ′ : Fm§ k} {C} (η : Δ ⊆ Δ′) (δ : Þ / Γ ⊢§ Δ′) →
             get§ (wk⊆ η) (lift§ {C = C} δ) ≡ wk§ (get§ η δ)
eqwkget§ η δ = eqrenget§ (wk⊆ id⊆) η δ

eqliftget§ : ∀ {Þ k} {Γ Δ Δ′ : Fm§ k} {C} (η : Δ ⊆ Δ′) (δ : Þ / Γ ⊢§ Δ′) →
               get§ (lift⊆ η) (lift§ {C = C} δ) ≡ lift§ (get§ η δ)
eqliftget§ η δ = (_, ‵var zero) & eqwkget§ η δ

ridget§ : ∀ {Þ k} {Γ Γ′ : Fm§ k} (η : Γ ⊆ Γ′) → get§ {Þ = Þ} η id§ ≡ var§ η
ridget§ stop      = refl
ridget§ (wk⊆ η)   = eqrenget§ (wk⊆ id⊆) η id§
                  ⋮ wk§ & ridget§ η
ridget§ (lift⊆ η) = (_, ‵var zero)
                      & ( eqrenget§ (wk⊆ id⊆) η id§
                        ⋮ wk§ & ridget§ η
                        )


----------------------------------------------------------------------------------------------------

-- 3.12. derivations: fundamental substitution lemmas

mutual
  eqrensub : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A} (η : Ξ ⊆ Ξ′) (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ ⊢ A) →
               sub (ren§ η σ) d ≡ ren η (sub σ d)
  eqrensub η σ (‵var i)                = eqrensub∋ η σ i
  eqrensub η σ (‵lam d)                = ‵lam & eqrensublift η σ d
  eqrensub η σ (d ‵$ e)                = _‵$_ & eqrensub η σ d ⊗ eqrensub η σ e
  eqrensub η σ (‵pair d e)             = ‵pair & eqrensub η σ d ⊗ eqrensub η σ e
  eqrensub η σ (‵fst d)                = ‵fst & eqrensub η σ d
  eqrensub η σ (‵snd d)                = ‵snd & eqrensub η σ d
  eqrensub η σ (‵left d)               = ‵left & eqrensub η σ d
  eqrensub η σ (‵right d)              = ‵right & eqrensub η σ d
  eqrensub η σ (‵either c d e)         = ‵either
                                           & eqrensub η σ c
                                           ⊗ eqrensublift η σ d
                                           ⊗ eqrensublift η σ e
  eqrensub η σ (‵all refl d)           = ‵all refl
                                           & ( (λ σ﹠ → sub σ﹠ d) & eqtrenren§ (wk≤ id≤) η σ ⁻¹
                                             ⋮ eqrensub (twk⊆ η) (twk§ σ) d
                                             )
  eqrensub η σ (‵unall t refl d)       = ‵unall t refl & eqrensub η σ d
  eqrensub η σ (‵ex t refl d)          = ‵ex t refl & eqrensub η σ d
  eqrensub η σ (‵letex refl refl d e)  = ‵letex refl refl
                                           & eqrensub η σ d
                                           ⊗ ( (λ σ﹠ → sub (lift§ σ﹠) e)
                                                 & eqtrenren§ (wk≤ id≤) η σ ⁻¹
                                             ⋮ eqrensublift (twk⊆ η) (twk§ σ) e
                                             )
  eqrensub η σ (‵abortHA d)            = ‵abortHA & eqrensub η σ d
  eqrensub η σ (‵magicPA d)            = ‵magicPA & eqrensublift η σ d
  eqrensub η σ ‵refl                   = refl
  eqrensub η σ (‵sym d)                = ‵sym & eqrensub η σ d
  eqrensub η σ (‵trans d e)            = ‵trans & eqrensub η σ d ⊗ eqrensub η σ e
  eqrensub η σ (‵cong f i refl refl d) = ‵cong f i refl refl & eqrensub η σ d
  eqrensub η σ ‵dis                    = refl
  eqrensub η σ (‵inj d)                = ‵inj & eqrensub η σ d
  eqrensub η σ (‵ind refl refl d e)    = ‵ind refl refl & eqrensub η σ d ⊗ eqrensub η σ e
  eqrensub η σ (‵proj i refl)          = refl
  eqrensub η σ (‵comp g φ refl)        = refl
  eqrensub η σ (‵rec f g)              = refl

  eqrensublift : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A B} (η : Ξ ⊆ Ξ′) (σ : Þ / Ξ ⊢§ Γ)
                   (d : Þ / Γ , A ⊢ B) →
                   sub (lift§ (ren§ η σ)) d ≡ ren (lift⊆ η) (sub (lift§ σ) d)
  eqrensublift η σ d = (λ σ﹠ → sub σ﹠ d) & eqliftren§ η σ ⁻¹
                     ⋮ eqrensub (lift⊆ η) (lift§ σ) d

mutual
  eqsubren : ∀ {Þ k} {Γ Γ′ Ξ : Fm§ k} {A} (σ : Þ / Ξ ⊢§ Γ′) (η : Γ ⊆ Γ′) (d : Þ / Γ ⊢ A) →
               sub (get§ η σ) d ≡ sub σ (ren η d)
  eqsubren σ η (‵var i)                = eqsubren∋ σ η i
  eqsubren σ η (‵lam d)                = ‵lam & eqsubrenlift σ η d
  eqsubren σ η (d ‵$ e)                = _‵$_ & eqsubren σ η d ⊗ eqsubren σ η e
  eqsubren σ η (‵pair d e)             = ‵pair & eqsubren σ η d ⊗ eqsubren σ η e
  eqsubren σ η (‵fst d)                = ‵fst & eqsubren σ η d
  eqsubren σ η (‵snd d)                = ‵snd & eqsubren σ η d
  eqsubren σ η (‵left d)               = ‵left & eqsubren σ η d
  eqsubren σ η (‵right d)              = ‵right & eqsubren σ η d
  eqsubren σ η (‵either c d e)         = ‵either
                                           & eqsubren σ η c
                                           ⊗ eqsubrenlift σ η d
                                           ⊗ eqsubrenlift σ η e
  eqsubren σ η (‵all refl d)           = ‵all refl
                                           & ( (λ σ﹠ → sub σ﹠ d) & eqtrenget§ (wk≤ id≤) η σ ⁻¹
                                             ⋮ eqsubren (twk§ σ) (twk⊆ η) d
                                             )
  eqsubren σ η (‵unall t refl d)       = ‵unall t refl & eqsubren σ η d
  eqsubren σ η (‵ex t refl d)          = ‵ex t refl & eqsubren σ η d
  eqsubren σ η (‵letex refl refl d e)  = ‵letex refl refl
                                           & eqsubren σ η d
                                           ⊗ ( (λ σ﹠ → sub (lift§ σ﹠) e)
                                                 & eqtrenget§ (wk≤ id≤) η σ ⁻¹
                                             ⋮ eqsubrenlift (twk§ σ) (twk⊆ η) e
                                             )
  eqsubren σ η (‵abortHA d)            = ‵abortHA & eqsubren σ η d
  eqsubren σ η (‵magicPA d)            = ‵magicPA & eqsubrenlift σ η d
  eqsubren σ η ‵refl                   = refl
  eqsubren σ η (‵sym d)                = ‵sym & eqsubren σ η d
  eqsubren σ η (‵trans d e)            = ‵trans & eqsubren σ η d ⊗ eqsubren σ η e
  eqsubren σ η (‵cong f i refl refl d) = ‵cong f i refl refl & eqsubren σ η d
  eqsubren σ η ‵dis                    = refl
  eqsubren σ η (‵inj d)                = ‵inj & eqsubren σ η d
  eqsubren σ η (‵ind refl refl d e)    = ‵ind refl refl & eqsubren σ η d ⊗ eqsubren σ η e
  eqsubren σ η (‵proj i refl)          = refl
  eqsubren σ η (‵comp g φ refl)        = refl
  eqsubren σ η (‵rec f g)              = refl

  eqsubrenlift : ∀ {Þ k} {Γ Γ′ Ξ : Fm§ k} {A B} (σ : Þ / Ξ ⊢§ Γ′) (η : Γ ⊆ Γ′)
                   (d : Þ / Γ , A ⊢ B) →
                   sub (lift§ (get§ η σ)) d ≡ sub (lift§ σ) (ren (lift⊆ η) d)
  eqsubrenlift σ η d = (λ σ﹠ → sub σ﹠ d) & eqliftget§ η σ ⁻¹
                     ⋮ eqsubren (lift§ σ) (lift⊆ η) d

lidsub : ∀ {Þ k} {Γ : Fm§ k} {A} (d : Þ / Γ ⊢ A) → sub id§ d ≡ d
lidsub (‵var i)                = idsub∋ i
lidsub (‵lam d)                = ‵lam & lidsub d
lidsub (d ‵$ e)                = _‵$_ & lidsub d ⊗ lidsub e
lidsub (‵pair d e)             = ‵pair & lidsub d ⊗ lidsub e
lidsub (‵fst d)                = ‵fst & lidsub d
lidsub (‵snd d)                = ‵snd & lidsub d
lidsub (‵left d)               = ‵left & lidsub d
lidsub (‵right d)              = ‵right & lidsub d
lidsub (‵either c d e)         = ‵either & lidsub c ⊗ lidsub d ⊗ lidsub e
lidsub (‵all refl d)           = ‵all refl
                                   & ((λ σ﹠ → sub σ﹠ d) & ridtren§ (wk≤ id≤) ⋮ lidsub d)
lidsub (‵unall t refl d)       = ‵unall t refl & lidsub d
lidsub (‵ex t refl d)          = ‵ex t refl & lidsub d
lidsub (‵letex refl refl d e)  = ‵letex refl refl
                                   & lidsub d
                                   ⊗ ((λ σ﹠ → sub (lift§ σ﹠) e) & ridtren§ (wk≤ id≤) ⋮ lidsub e)
lidsub (‵abortHA d)            = ‵abortHA & lidsub d
lidsub (‵magicPA d)            = ‵magicPA & lidsub d
lidsub ‵refl                   = refl
lidsub (‵sym d)                = ‵sym & lidsub d
lidsub (‵trans d e)            = ‵trans & lidsub d ⊗ lidsub e
lidsub (‵cong f i refl refl d) = ‵cong f i refl refl & lidsub d
lidsub ‵dis                    = refl
lidsub (‵inj d)                = ‵inj & lidsub d
lidsub (‵ind refl refl d e)    = ‵ind refl refl & lidsub d ⊗ lidsub e
lidsub (‵proj i refl)          = refl
lidsub (‵comp g φ refl)        = refl
lidsub (‵rec f g)              = refl


----------------------------------------------------------------------------------------------------

-- 3.13. interaction between term renaming and derivation substitution
-- TODO: clean this up

-- module _ where
--   open ≅-Reasoning
--
--   hlidren§ : ∀ {Þ k} {Γ ^Γ Δ : Fm§ k} (p : Γ ≡ ^Γ) (δ : Þ / Γ ⊢§ Δ) → ren§ (castid⊆ p) δ ≅ δ
--   hlidren§ refl δ = ≡→≅ (lidren§ δ)
--
--   hlidget§ : ∀ {Þ k} {Γ Δ ^Δ : Fm§ k} (p : Δ ≡ ^Δ) (δ : Þ / Γ ⊢§ ^Δ) → get§ (castid⊆ p) δ ≅ δ
--   hlidget§ refl δ = ≡→≅ (lidget§ δ)
--
--   cast§→≅ : ∀ {Þ k} {Γ ^Γ Δ ^Δ : Fm§ k} (p₁ : ^Γ ≡ Γ) (p₂ : ^Δ ≡ Δ) (δ : Þ / Γ ⊢§ Δ) →
--                cast§ p₁ p₂ δ ≅ δ
--   cast§→≅ refl refl δ = refl
--
--   hcomptren§ : ∀ {Þ k k′ k″ Γ Δ} (η′ : k′ ≤ k″) (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
--                  tren§ (η′ ∘≤ η) δ ≅ tren§ η′ (tren§ η δ)
--   hcomptren§ {Γ = Γ} {Δ} η′ η δ =
--       begin
--         tren§ (η′ ∘≤ η) δ
--       ≡⟨ comptren§﹫ η′ η δ ⟩
--         cast§ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Δ) (tren§ η′ (tren§ η δ))
--       ≅⟨ cast§→≅ (comprenFm§ η′ η Γ) (comprenFm§ η′ η Δ) (tren§ η′ (tren§ η δ)) ⟩
--         tren§ η′ (tren§ η δ)
--       ∎
--
--   huntitled2 : ∀ {Þ k k′ Γ Δ} (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
--                  get§ (castid⊆ (eqwkrenFm§ η Δ)) (twk§ (tren§ η δ)) ≅
--                    ren§ (castid⊆ (eqwkrenFm§ η Γ)) (tren§ (lift≤ η) (twk§ δ))
--   huntitled2 {Γ = Γ} {Δ} η δ =
--       begin
--         get§ (castid⊆ (eqwkrenFm§ η Δ)) (twk§ (tren§ η δ))
--       ≅⟨ hlidget§ (eqwkrenFm§ η Δ) (twk§ (tren§ η δ)) ⟩
--         twk§ (tren§ η δ)
--       ≅⟨ hcomptren§ (wk≤ id≤) η δ ʰ⁻¹ ⟩
--         tren§ (wk≤ id≤ ∘≤ η) δ
--       ≅⟨ (λ η﹠ → tren§ (wk≤ η﹠) δ) ʰ& ≡→≅ (lid≤ η ⋮ rid≤ η ⁻¹) ⟩
--         tren§ (lift≤ η ∘≤ wk≤ id≤) δ
--       ≅⟨ hcomptren§ (lift≤ η) (wk≤ id≤) δ ⟩
--         tren§ (lift≤ η) (twk§ δ)
--       ≅⟨ hlidren§ (eqwkrenFm§ η Γ) (tren§ (lift≤ η) (twk§ δ)) ʰ⁻¹ ⟩
--         ren§ (castid⊆ (eqwkrenFm§ η Γ)) (tren§ (lift≤ η) (twk§ δ))
--       ∎

castlidget§ : ∀ {Þ k} {Γ : Fm§ k} {Δ ^Δ} (p : ^Δ ≡ Δ) (δ : Þ / Γ ⊢§ Δ) →
                get§ (castid⊆ p) δ ≡ cast§ refl p δ
castlidget§ refl δ = lidget§ δ

castlidren§ : ∀ {Þ k} {Γ ^Γ : Fm§ k} {Δ} (p : Γ ≡ ^Γ) (δ : Þ / Γ ⊢§ Δ) →
                ren§ (castid⊆ p) δ ≡ cast§ (p ⁻¹) refl δ
castlidren§ refl δ = lidren§ δ

-- TODO: rewrite this
untitled2′ : ∀ {Þ k k′ Γ ^Γ Δ ^Δ} (η : k ≤ k′)
               (p₁ : ^Γ ≡ renFm§ (wk≤ (id≤ ∘≤ η)) Γ) (p₂ : ^Δ ≡ renFm§ (wk≤ (id≤ ∘≤ η)) Δ)
               (p₃ : ^Γ ≡ renFm§ (wk≤ (η ∘≤ id≤)) Γ) (p₄ : ^Δ ≡ renFm§ (wk≤ (η ∘≤ id≤)) Δ)
               (δ : Þ / Γ ⊢§ Δ) →
               cast§ p₁ p₂ (tren§ (wk≤ (id≤ ∘≤ η)) δ) ≡ cast§ p₃ p₄ (tren§ (wk≤ (η ∘≤ id≤)) δ)
untitled2′ η p₁ p₂ p₃ p₄ δ
  rewrite (lid≤ η ⋮ rid≤ η ⁻¹) = cast§ & uip p₁ p₃ ⊗ uip p₂ p₄ ⊗ refl

-- TODO: rename this
untitled2 : ∀ {Þ k k′ Γ Δ} (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
              get§ (castid⊆ (eqwkrenFm§ η Δ)) (twk§ (tren§ η δ)) ≡
                ren§ (castid⊆ (eqwkrenFm§ η Γ)) (tren§ (lift≤ η) (twk§ δ))
untitled2 {Γ = Γ} {Δ} η δ =
      castlidget§ (eqwkrenFm§ η Δ) (twk§ (tren§ η δ))
    ⋮ comptren§ (wk≤ id≤) η (comprenFm§ (wk≤ id≤) η Γ ⁻¹)
        (comprenFm§ (lift≤ η) (wk≤ id≤) Δ ⁻¹ ⋮ (λ η﹠ → renFm§ (wk≤ η﹠) Δ) & (rid≤ η ⋮ lid≤ η ⁻¹))
        refl (eqwkrenFm§ η Δ) δ ⁻¹
    ⋮ untitled2′ η _ _ _ _ δ
    ⋮ comptren§ (lift≤ η) (wk≤ id≤)
        (comprenFm§ (wk≤ id≤) η Γ ⁻¹ ⋮ (λ η﹠ → renFm§ (wk≤ η﹠) Γ) & (lid≤ η ⋮ rid≤ η ⁻¹))
        (comprenFm§ (lift≤ η) (wk≤ id≤) Δ ⁻¹) (eqwkrenFm§ η Γ ⁻¹) refl δ
    ⋮ castlidren§ (eqwkrenFm§ η Γ) (tren§ (lift≤ η) (twk§ δ)) ⁻¹

eqtrensub∋ : ∀ {Þ k k′ Γ Ξ A} (η : k ≤ k′) (σ : Þ / Ξ ⊢§ Γ) (i : Γ ∋ A) →
               sub∋ (tren§ η σ) (tren∋ η i) ≡ tren η (sub∋ σ i)
eqtrensub∋ η (σ , d) zero    = refl
eqtrensub∋ η (σ , d) (suc i) = eqtrensub∋ η σ i

eqtrenlift§ : ∀ {Þ k k′ Γ Δ C} (η : k ≤ k′) (δ : Þ / Γ ⊢§ Δ) →
                lift§ (tren§ η δ) ≡ tren§ η (lift§ {C = C} δ)
eqtrenlift§ η ∙       = refl
eqtrenlift§ η (δ , d) = (_, ‵var zero)
                        & ( _,_
                              & ((λ ζ﹠ → ren§ (wk⊆ ζ﹠) (tren§ η δ)) & ridtren⊆ η ⁻¹)
                              ⊗ ((λ ζ﹠ → ren (wk⊆ ζ﹠) (tren η d)) & ridtren⊆ η ⁻¹)
                          ⋮ eqtrenren§ η (wk⊆ id⊆) (δ , d)
                          )

mutual
  eqtrensub : ∀ {Þ k k′ Γ Ξ A} (η : k ≤ k′) (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ ⊢ A) →
                sub (tren§ η σ) (tren η d) ≡ tren η (sub σ d)
  eqtrensub η σ (‵var i)                = eqtrensub∋ η σ i
  eqtrensub η σ (‵lam d)                = ‵lam & eqtrensublift η σ d
  eqtrensub η σ (d ‵$ e)                = _‵$_ & eqtrensub η σ d ⊗ eqtrensub η σ e
  eqtrensub η σ (‵pair d e)             = ‵pair & eqtrensub η σ d ⊗ eqtrensub η σ e
  eqtrensub η σ (‵fst d)                = ‵fst & eqtrensub η σ d
  eqtrensub η σ (‵snd d)                = ‵snd & eqtrensub η σ d
  eqtrensub η σ (‵left d)               = ‵left & eqtrensub η σ d
  eqtrensub η σ (‵right d)              = ‵right & eqtrensub η σ d
  eqtrensub η σ (‵either c d e)         = ‵either
                                            & eqtrensub η σ c
                                            ⊗ eqtrensublift η σ d
                                            ⊗ eqtrensublift η σ e
  eqtrensub η σ (‵all refl d)           = sub (tren§ η σ)
                                            & ( (λ r﹠ → ‵all r﹠ (tren (lift≤ η) d))
                                                  & uip (refl ⋮ eqwkrenFm§ η _) _
                                              ⋮ eqall (eqwkrenFm§ η _) (tren (lift≤ η) d) ⁻¹
                                              )
                                        ⋮ ‵all refl
                                           & ( eqsubren (twk§ (tren§ η σ))
                                                 (castid⊆ (eqwkrenFm§ η _)) (tren (lift≤ η) d) ⁻¹
                                             ⋮ (λ σ﹠ → sub σ﹠ (tren (lift≤ η) d)) & untitled2 η σ
                                             ⋮ eqrensub (castid⊆ (eqwkrenFm§ η _))
                                                 (tren§ (lift≤ η) (twk§ σ)) (tren (lift≤ η) d)
                                             )
                                        ⋮ eqall (eqwkrenFm§ η _) (sub (tren§ (lift≤ η) (twk§ σ))
                                            (tren (lift≤ η) d))
                                        ⋮ ‵all (eqwkrenFm§ η _) & eqtrensub (lift≤ η) (twk§ σ) d
                                        ⋮ (λ r﹠ → ‵all r﹠ (tren (lift≤ η) (sub (twk§ σ) d)))
                                            & uip _ _
  eqtrensub η σ (‵unall t refl d)       = ‵unall (renTm η t) (eqrencut0Fm η _ t ⋮ refl)
                                            & eqtrensub η σ d
  eqtrensub η σ (‵ex t refl d)          = ‵ex (renTm η t) (eqrencut0Fm η _ t ⋮ refl)
                                            & eqtrensub η σ d
  eqtrensub η σ (‵letex refl refl d e)  = sub (tren§ η σ)
                                            & ( (λ r₁﹠ r₂﹠ → ‵letex r₁﹠ r₂﹠ (tren η d)
                                                    (tren (lift≤ η) e))
                                                  & uip (refl ⋮ eqwkrenFm§ η _) _
                                                  ⊗ uip _ _
                                              ⋮ eqletex (eqwkrenFm§ η _) (eqwkrenFm η _) (tren η d)
                                                  (tren (lift≤ η) e) ⁻¹
                                              )
                                        ⋮ ‵letex refl (eqwkrenFm η _) (sub (tren§ η σ) (tren η d))
                                            & ( eqsubrenlift (twk§ (tren§ η σ))
                                                  (castid⊆ (eqwkrenFm§ η _)) (tren (lift≤ η) e) ⁻¹
                                              ⋮ (λ σ﹠ → sub (lift§ σ﹠) (tren (lift≤ η) e))
                                                  & untitled2 η σ
                                              ⋮ eqrensublift (castid⊆ (eqwkrenFm§ η _))
                                                  (tren§ (lift≤ η) (twk§ σ)) (tren (lift≤ η) e)                                                   )
                                        ⋮ eqletex (eqwkrenFm§ η _) (eqwkrenFm η _)
                                            (sub (tren§ η σ) (tren η d))
                                            (sub (lift§ (tren§ (lift≤ η) (twk§ σ)))
                                            (tren (lift≤ η) e))
                                        ⋮ ‵letex (eqwkrenFm§ η _) (eqwkrenFm η _)
                                            & eqtrensub η σ d
                                            ⊗ eqtrensublift (lift≤ η) (twk§ σ) e
                                        ⋮ (λ r₁﹠ r₂﹠ → ‵letex r₁﹠ r₂﹠ (tren η (sub σ d))
                                              (tren (lift≤ η) (sub (lift§ (twk§ σ)) e)))
                                            & uip _ _
                                            ⊗ uip _ _
  eqtrensub η σ (‵abortHA d)            = ‵abortHA & eqtrensub η σ d
  eqtrensub η σ (‵magicPA d)            = ‵magicPA & eqtrensublift η σ d
  eqtrensub η σ ‵refl                   = refl
  eqtrensub η σ (‵sym d)                = ‵sym & eqtrensub η σ d
  eqtrensub η σ (‵trans d e)            = ‵trans & eqtrensub η σ d ⊗ eqtrensub η σ e
  eqtrensub η σ (‵cong f i refl refl d) = ‵cong f i (eqrenpokeTm η i _ _ ⋮ refl)
                                              (eqrenpeekTm η i _ ⋮ refl)
                                            & eqtrensub η σ d
  eqtrensub η σ ‵dis                    = refl
  eqtrensub η σ (‵inj d)                = ‵inj & eqtrensub η σ d
  eqtrensub η σ (‵ind refl refl d e)    = ‵ind (eqrencut0Fm η _ 𝟘 ⋮ renFm η & refl)
                                              ( eqrencut1Fm η _ (𝕊 (‵tvar zero))
                                              ⋮ renFm (lift≤ η) & refl
                                              )
                                            & eqtrensub η σ d ⊗ eqtrensub η σ e
  eqtrensub η σ (‵proj i refl)          = refl
  eqtrensub η σ (‵comp g φ refl)        = refl
  eqtrensub η σ (‵rec f g)              = refl

  eqtrensublift : ∀ {Þ k k′ Γ Ξ A C} (η : k ≤ k′) (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ , C ⊢ A) →
                    sub (lift§ (tren§ η σ)) (tren η d) ≡ tren η (sub (lift§ σ) d)
  eqtrensublift η σ d = (λ σ﹠ → sub σ﹠ (tren η d)) & eqtrenlift§ η σ
                      ⋮ eqtrensub η (lift§ σ) d

eqtrensub§ : ∀ {Þ k k′ Γ Ξ Δ} (η : k ≤ k′) (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
               sub§ (tren§ η σ) (tren§ η δ) ≡ tren§ η (sub§ σ δ)
eqtrensub§ η σ ∙       = refl
eqtrensub§ η σ (δ , d) = _,_ & eqtrensub§ η σ δ ⊗ eqtrensub η σ d


----------------------------------------------------------------------------------------------------

-- 3.14. derivations: generic lemmas from RenSubKit2

eqrensub§ : ∀ {Þ k} {Γ Ξ Ξ′ Δ : Fm§ k} (η : Ξ ⊆ Ξ′) (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
              sub§ (ren§ η σ) δ ≡ ren§ η (sub§ σ δ)
eqrensub§ η σ ∙       = refl
eqrensub§ η σ (δ , d) = _,_ & eqrensub§ η σ δ ⊗ eqrensub η σ d

eqsubren§ : ∀ {Þ k} {Γ Γ′ Ξ Δ : Fm§ k} (σ : Þ / Ξ ⊢§ Γ′) (η : Γ ⊆ Γ′) (δ : Þ / Γ ⊢§ Δ) →
              sub§ (get§ η σ) δ ≡ sub§ σ (ren§ η δ)
eqsubren§ σ η ∙       = refl
eqsubren§ σ η (δ , d) = _,_ & eqsubren§ σ η δ ⊗ eqsubren σ η d

lidsub§ : ∀ {Þ k} {Γ Δ : Fm§ k} (δ : Þ / Γ ⊢§ Δ) → sub§ id§ δ ≡ δ
lidsub§ ∙       = refl
lidsub§ (δ , d) = _,_ & lidsub§ δ ⊗ lidsub d

eqsub : ∀ {Þ k} {Γ Ξ : Fm§ k} {A B} (σ : Þ / Ξ ⊢§ Γ) (s : Þ / Ξ ⊢ B) (d : Þ / Γ ⊢ A) →
          sub (σ , s) (wk d) ≡ sub σ d
eqsub σ s d = eqsubren (σ , s) (wk⊆ id⊆) d ⁻¹
            ⋮ (λ σ﹠ → sub σ﹠ d) & lidget§ σ

eqsub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} {B} (σ : Þ / Ξ ⊢§ Γ) (s : Þ / Ξ ⊢ B) (δ : Þ / Γ ⊢§ Δ) →
           sub§ (σ , s) (wk§ δ) ≡ sub§ σ δ
eqsub§ σ s ∙       = refl
eqsub§ σ s (δ , d) = _,_ & eqsub§ σ s δ ⊗ eqsub σ s d

eqwksub : ∀ {Þ k} {Γ Ξ : Fm§ k} {A C} (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ ⊢ A) →
            sub (lift§ σ) (wk {C = C} d) ≡ wk (sub σ d)
eqwksub σ d = eqsubren (lift§ σ) (wk⊆ id⊆) d ⁻¹
            ⋮ (λ σ﹠ → sub σ﹠ d)
                & ( eqwkget§ id⊆ σ
                  ⋮ wk§ & lidget§ σ
                  )
            ⋮ eqrensub (wk⊆ id⊆) σ d

eqwksub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} {C} (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
             sub§ (lift§ σ) (wk§ {C = C} δ) ≡ wk§ (sub§ σ δ)
eqwksub§ σ ∙       = refl
eqwksub§ σ (δ , d) = _,_ & eqwksub§ σ δ ⊗ eqwksub σ d

eqliftsub§ : ∀ {Þ k} {Γ Ξ Δ : Fm§ k} {C} (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
               sub§ (lift§ σ) (lift§ {C = C} δ) ≡ lift§ (sub§ σ δ)
eqliftsub§ σ δ = _,_ & eqwksub§ σ δ ⊗ ridsub (lift§ σ) zero

ridsub§ : ∀ {Þ k} {Γ Ξ : Fm§ k} (σ : Þ / Ξ ⊢§ Γ) → sub§ σ id§ ≡ σ
ridsub§ ∙       = refl
ridsub§ (σ , s) = _,_
                    & ( eqsub§ σ s id§
                      ⋮ ridsub§ σ
                      )
                    ⊗ ridsub (σ , s) zero


----------------------------------------------------------------------------------------------------

-- 3.15. derivations: more fundamental substitution lemmas

mutual
  compsub : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ ⊢ A) →
              sub (sub§ σ′ σ) d ≡ sub σ′ (sub σ d)

  compsub σ′ σ (‵var i)                = compsub∋ σ′ σ i
  compsub σ′ σ (‵lam d)                = ‵lam & compsublift σ′ σ d
  compsub σ′ σ (d ‵$ e)                = _‵$_ & compsub σ′ σ d ⊗ compsub σ′ σ e
  compsub σ′ σ (‵pair d e)             = ‵pair & compsub σ′ σ d ⊗ compsub σ′ σ e
  compsub σ′ σ (‵fst d)                = ‵fst & compsub σ′ σ d
  compsub σ′ σ (‵snd d)                = ‵snd & compsub σ′ σ d
  compsub σ′ σ (‵left d)               = ‵left & compsub σ′ σ d
  compsub σ′ σ (‵right d)              = ‵right & compsub σ′ σ d
  compsub σ′ σ (‵either c d e)         = ‵either
                                           & compsub σ′ σ c
                                           ⊗ compsublift σ′ σ d
                                           ⊗ compsublift σ′ σ e
  compsub σ′ σ (‵all refl d)           = ‵all refl
                                           & ( (λ σ﹠ → sub σ﹠ d) & eqtrensub§ (wk≤ id≤) σ′ σ ⁻¹
                                             ⋮ compsub (twk§ σ′) (twk§ σ) d
                                             )
  compsub σ′ σ (‵unall t refl d)       = ‵unall t refl & compsub σ′ σ d
  compsub σ′ σ (‵ex t refl d)          = ‵ex t refl & compsub σ′ σ d
  compsub σ′ σ (‵letex refl refl d e)  = ‵letex refl refl
                                           & compsub σ′ σ d
                                           ⊗ ( (λ σ﹠ → sub (lift§ σ﹠) e)
                                                 & eqtrensub§ (wk≤ id≤) σ′ σ ⁻¹
                                             ⋮ compsublift (twk§ σ′) (twk§ σ) e
                                             )
  compsub σ′ σ (‵abortHA d)            = ‵abortHA & compsub σ′ σ d
  compsub σ′ σ (‵magicPA d)            = ‵magicPA & compsublift σ′ σ d
  compsub σ′ σ ‵refl                   = refl
  compsub σ′ σ (‵sym d)                = ‵sym & compsub σ′ σ d
  compsub σ′ σ (‵trans d e)            = ‵trans & compsub σ′ σ d ⊗ compsub σ′ σ e
  compsub σ′ σ (‵cong f i refl refl d) = ‵cong f i refl refl & compsub σ′ σ d
  compsub σ′ σ ‵dis                    = refl
  compsub σ′ σ (‵inj d)                = ‵inj & compsub σ′ σ d
  compsub σ′ σ (‵ind refl refl d e)    = ‵ind refl refl & compsub σ′ σ d ⊗ compsub σ′ σ e
  compsub σ′ σ (‵proj i refl)          = refl
  compsub σ′ σ (‵comp g φ refl)        = refl
  compsub σ′ σ (‵rec f g)              = refl

  compsublift : ∀ {Þ k} {Γ Ξ Ξ′ : Fm§ k} {A B} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ)
                  (d : Þ / Γ , A ⊢ B) →
                  sub (lift§ (sub§ σ′ σ)) d ≡ sub (lift§ σ′) (sub (lift§ σ) d)
  compsublift σ′ σ d = (λ σ﹠ → sub σ﹠ d) & eqliftsub§ σ′ σ ⁻¹
                     ⋮ compsub (lift§ σ′) (lift§ σ) d


----------------------------------------------------------------------------------------------------

-- 3.16. derivations: generic lemmas from RenSubKit3

asssub§ : ∀ {Þ k} {Γ Ξ Ξ′ Δ : Fm§ k} (σ′ : Þ / Ξ′ ⊢§ Ξ) (σ : Þ / Ξ ⊢§ Γ) (δ : Þ / Γ ⊢§ Δ) →
            sub§ σ′ (sub§ σ δ) ≡ sub§ (sub§ σ′ σ) δ
asssub§ σ′ σ ∙       = refl
asssub§ σ′ σ (δ , d) = _,_ & asssub§ σ′ σ δ ⊗ compsub σ′ σ d ⁻¹

eqrencut : ∀ {Þ k} {Γ Γ′ : Fm§ k} {A B} (η : Γ ⊆ Γ′) (d : Þ / Γ , A ⊢ B) (s : Þ / Γ ⊢ A) →
             ren (lift⊆ η) d [ ren η s /0] ≡ ren η (d [ s /0])
eqrencut η d s = eqsubren (id§ , ren η s) (lift⊆ η) d ⁻¹
               ⋮ (λ σ﹠ → sub (σ﹠ , ren η s) d) & (ridget§ η ⋮ ridren§ η ⁻¹)
               ⋮ eqrensub η (id§ , s) d

eqsubcut : ∀ {Þ k} {Γ Ξ : Fm§ k} {A B} (σ : Þ / Ξ ⊢§ Γ) (d : Þ / Γ , A ⊢ B) (s : Þ / Γ ⊢ A) →
             sub (lift§ σ) d [ sub σ s /0] ≡ sub σ (d [ s /0])
eqsubcut σ d s = compsub (id§ , sub σ s) (lift§ σ) d ⁻¹
               ⋮ (λ σ﹠ → sub σ﹠ d)
                   & ( _,_
                         & ( eqsubren§ (id§ , sub σ s) (wk⊆ id⊆) σ ⁻¹
                           ⋮ (λ σ﹠ → sub§ σ﹠ σ) & lidget§ id§
                           ⋮ lidsub§ σ
                           ⋮ ridsub§ σ ⁻¹
                           )
                         ⊗ ridsub (id§ , sub σ s) zero
                     )
               ⋮ compsub σ (id§ , s) d


----------------------------------------------------------------------------------------------------

-- 4.0. category of order-preserving embeddings

module Section-4-0 (funext : Funext) where
  -- TODO: report bug with `record where`
  cat≥ : Category lzero lzero
  cat≥ = record
      { Obj  = Nat
      ; _▻_  = _≤_
      ; id   = id≤
      ; _∘_  = _∘≤_
      ; lid▻ = lid≤
      ; rid▻ = rid≤
      ; ass▻ = ass≤
      ; ◅ssa = λ η η′ η″ → ass≤ η″ η′ η ⁻¹
      } ᵒᵖ

  pshrenFin : Presheaf cat≥ lzero
  pshrenFin = record
      { ƒObj = Fin
      ; ƒ    = renFin
      ; idƒ  = funext idrenFin
      ; _∘ƒ_ = λ η′ η → funext (comprenFin η′ η)
      }

  module _ {𝓍} {X : Set 𝓍} where
    cat⊇ : Category 𝓍 𝓍
    cat⊇ = record
        { Obj  = List X
        ; _▻_  = _⊆_
        ; id   = id⊆
        ; _∘_  = _∘⊆_
        ; lid▻ = lid⊆
        ; rid▻ = rid⊆
        ; ass▻ = ass⊆
        ; ◅ssa = λ η η′ η″ → ass⊆ η″ η′ η ⁻¹
        } ᵒᵖ

    pshren∋ : X → Presheaf cat⊇ 𝓍
    pshren∋ X = record
        { ƒObj = _∋ X
        ; ƒ    = ren∋
        ; idƒ  = funext idren∋
        ; _∘ƒ_ = λ η′ η → funext (compren∋ η′ η)
        }


----------------------------------------------------------------------------------------------------

-- 4.1. category of simultaneous substitutions of terms

module Section-4-1 (funext : Funext) where
  open Section-4-0 funext

  pshrenTm : Presheaf cat≥ lzero
  pshrenTm = record
      { ƒObj = λ k → Tm k
      ; ƒ    = renTm
      ; idƒ  = funext lidrenTm
      ; _∘ƒ_ = λ η′ η → funext (comprenTm η′ η)
      }

  pshrenTm§ : Nat → Presheaf cat≥ lzero
  pshrenTm§ n = record
      { ƒObj = λ k → Tm§ k n
      ; ƒ    = renTm§
      ; idƒ  = funext lidrenTm§
      ; _∘ƒ_ = λ η′ η → funext (comprenTm§ η′ η)
      }

  pshgetTm§ : Nat → Presheaf (cat≥ ᵒᵖ) lzero
  pshgetTm§ k = record
      { ƒObj = λ n → Tm§ k n
      ; ƒ    = getTm§
      ; idƒ  = funext lidgetTm§
      ; _∘ƒ_ = λ η′ η → funext (compgetTm§ η′ η)
      }

  catTm§ : Category lzero lzero
  catTm§ = record
      { Obj  = Nat
      ; _▻_  = λ n k → Tm§ k n
      ; id   = idTm§
      ; _∘_  = subTm§
      ; lid▻ = lidsubTm§
      ; rid▻ = ridsubTm§
      ; ass▻ = asssubTm§
      ; ◅ssa = λ τ σ σ′ → asssubTm§ σ′ σ τ ⁻¹
      } ᵒᵖ

  pshsubTm : Presheaf catTm§ lzero
  pshsubTm = record
      { ƒObj = λ k → Tm k
      ; ƒ    = subTm
      ; idƒ  = funext lidsubTm
      ; _∘ƒ_ = λ σ′ σ → funext (compsubTm σ′ σ)
      }

  pshsubTm§ : Nat → Presheaf catTm§ lzero
  pshsubTm§ n = record
      { ƒObj = λ k → Tm§ k n
      ; ƒ    = subTm§
      ; idƒ  = funext lidsubTm§
      ; _∘ƒ_ = λ σ′ σ → funext (λ τ → asssubTm§ σ′ σ τ ⁻¹) -- TODO: what? why?!
      }

  pshrenFm : Presheaf cat≥ lzero
  pshrenFm = record
      { ƒObj = λ k → Fm k
      ; ƒ    = renFm
      ; idƒ  = funext lidrenFm
      ; _∘ƒ_ = λ η′ η → funext (comprenFm η′ η)
      }

  pshrenFm§ : Presheaf cat≥ lzero
  pshrenFm§ = record
      { ƒObj = λ k → Fm§ k
      ; ƒ    = renFm§
      ; idƒ  = funext lidrenFm§
      ; _∘ƒ_ = λ η′ η → funext (comprenFm§ η′ η)
      }

  pshsubFm : Presheaf catTm§ lzero
  pshsubFm = record
      { ƒObj = λ k → Fm k
      ; ƒ    = subFm
      ; idƒ  = funext lidsubFm
      ; _∘ƒ_ = λ σ′ σ → funext (compsubFm σ′ σ)
      }

  pshsubFm§ : Presheaf catTm§ lzero
  pshsubFm§ = record
      { ƒObj = λ k → Fm§ k
      ; ƒ    = subFm§
      ; idƒ  = funext lidsubFm§
      ; _∘ƒ_ = λ σ′ σ → funext (compsubFm§ σ′ σ)
      }

----------------------------------------------------------------------------------------------------

-- TODO: 4.2. category of something something

module Section-4-2 (funext : Funext) where
  -- TODO: tren∋, lidtren∋, comptren∋
  -- TODO: tren⊆, lidtren⊆, lcomptren⊆
  -- TODO: tren, lidtren, comptren
  -- TODO: tren§, lidtren§, comptren§


----------------------------------------------------------------------------------------------------

-- 4.3. category of simultaneous substitutions of derivations

module Section-4-3 (funext : Funext) where
  open Section-4-0 funext

  pshren : ∀ {Þ k} → Fm k → Presheaf cat⊇ lzero
  pshren {Þ} A = record
      { ƒObj = λ Γ → Þ / Γ ⊢ A
      ; ƒ    = ren
      ; idƒ  = funext lidren
      ; _∘ƒ_ = λ η′ η → funext (compren η′ η)
      }

  pshren§ : ∀ {Þ k} → Fm§ k → Presheaf cat⊇ lzero
  pshren§ {Þ} Δ = record
      { ƒObj = λ Γ → Þ / Γ ⊢§ Δ
      ; ƒ    = ren§
      ; idƒ  = funext lidren§
      ; _∘ƒ_ = λ η′ η → funext (compren§ η′ η)
      }

  pshget§ : ∀ {Þ k} → Fm§ k → Presheaf (cat⊇ ᵒᵖ) lzero
  pshget§ {Þ} Γ = record
      { ƒObj = λ Δ → Þ / Γ ⊢§ Δ
      ; ƒ    = get§
      ; idƒ  = funext lidget§
      ; _∘ƒ_ = λ η′ η → funext (compget§ η′ η)
      }

  cat§ : ∀ {Þ k} → Category lzero lzero
  cat§ {Þ} {k} = record
      { Obj  = Fm§ k
      ; _▻_  = λ Δ Γ → Þ / Γ ⊢§ Δ
      ; id   = id§
      ; _∘_  = sub§
      ; lid▻ = lidsub§
      ; rid▻ = ridsub§
      ; ass▻ = asssub§
      ; ◅ssa = λ τ σ σ′ → asssub§ σ′ σ τ ⁻¹
      } ᵒᵖ

  pshsub : ∀ {Þ k} → Fm k → Presheaf cat§ lzero
  pshsub {Þ} A = record
      { ƒObj = λ Γ → Þ / Γ ⊢ A
      ; ƒ    = sub
      ; idƒ  = funext lidsub
      ; _∘ƒ_ = λ σ′ σ → funext (compsub σ′ σ)
      }

  pshsub§ : ∀ {Þ k} → Fm§ k → Presheaf cat§ lzero
  pshsub§ {Þ} Δ = record
      { ƒObj = λ Γ → Þ / Γ ⊢§ Δ
      ; ƒ    = sub§
      ; idƒ  = funext lidsub§
      ; _∘ƒ_ = λ σ′ σ → funext (λ τ → asssub§ σ′ σ τ ⁻¹) -- TODO: what? why?!
      }


----------------------------------------------------------------------------------------------------
