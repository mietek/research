module mi.Prelude where

open import Agda.Builtin.Bool public
  using (Bool ; true ; false)

open import Agda.Builtin.Equality public
  using (_≡_ ; refl)

open import Agda.Builtin.FromNat public
  using (Number ; fromNat)

open import Agda.Builtin.Nat public
  using (Nat ; zero ; suc ; _+_ ; _-_ ; _*_)

open import Agda.Builtin.Sigma public
  using (Σ ; fst ; snd)
  renaming (_,_ to sig)

open import Agda.Builtin.Unit public
  using (⊤ ; tt)

open import Agda.Primitive public
  using (Level ; _⊔_ ; Setω)
  renaming (lzero to 0ℓ ; lsuc to sucℓ)


----------------------------------------------------------------------------------------------------

-- tiny basics

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

T : Bool → Set
T true  = ⊤
T false = ⊥

T? : ∀ (b : Bool) → Dec (T b)
T? true  = yes tt
T? false = no (λ ())

module _ {𝓍} {X : Set 𝓍} where
  True : Dec X → Set
  True (yes _) = ⊤
  True (no _)  = ⊥

  toWitness : {X? : Dec X} → True X? → X
  toWitness {X?} p  with X?
  toWitness {X?} _  | yes x = x
  toWitness {X?} () | no _

  fromWitness : {X? : Dec X} → X → True X?
  fromWitness {X?} x with X?
  fromWitness {X?} _ | yes _ = tt
  fromWitness {X?} x | no ¬x = x ↯ ¬x

  mapDec : ∀ {𝓎} {Y : Set 𝓎} → (X → Y) → (Y → X) → Dec X → Dec Y
  mapDec f _ (yes x) = yes (f x)
  mapDec _ g (no ¬x) = no (λ y → g y ↯ ¬x)

-- numeric literals for naturals
instance
  literalNat : Number Nat
  literalNat = record
      { Constraint = λ _ → ⊤
      ; fromNat    = λ n {{_}} → n
      }

module Pointless where
  id : ∀ {𝓍} {X : Set 𝓍} → X → X
  id x = x

  infixr 9 _∘_
  _∘_ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : X → Set 𝓎} {Z : ∀ {x} → Y x → Set 𝓏}
          (f : ∀ {x} (y : Y x) → Z y) (g : ∀ x → Y x) → ∀ x → Z (g x)
  (f ∘ g) x = f (g x)

  flip : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : X → Y → Set 𝓏} →
           (∀ x y → Z x y) → (∀ y x → Z x y)
  flip f y x = f x y


----------------------------------------------------------------------------------------------------

-- equality

≡-syntax : ∀ {𝓍} (X : Set 𝓍) → X → X → Set 𝓍
≡-syntax X = _≡_

infix 4 ≡-syntax
syntax ≡-syntax X x x′ = x ≡ x′ :> X

module ≡ where
  infix 9 _⁻¹
  _⁻¹ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} → x ≡ x′ → x′ ≡ x
  refl ⁻¹ = refl

  infixr 4 _⋮_
  _⋮_ : ∀ {𝓍} {X : Set 𝓍} {x x′ x″ : X} → x ≡ x′ → x′ ≡ x″ → x ≡ x″
  refl ⋮ q = q

  infixl 9 _&_
  _&_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (f : X → Y) {x x′} → x ≡ x′ → f x ≡ f x′
  _ & refl = refl

  infixl 8 _⊗_
  _⊗_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {f g : X → Y} {x x′} → f ≡ g → x ≡ x′ → f x ≡ g x′
  refl ⊗ refl = refl

congapp : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} →
            {f g : ∀ x → Y x} → f ≡ g → (∀ x → f x ≡ g x)
congapp refl _ = refl

Funext : Setω
Funext = ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} →
           {f g : ∀ x → Y x} → (∀ x → f x ≡ g x) → f ≡ g

congapp′ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} →
             {f g : ∀ {x} → Y x} → f ≡ g :> (∀ {x} → Y x) → (∀ {x} → f {x} ≡ g {x})
congapp′ refl {_} = refl

Funext′ : Setω
Funext′ = ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} →
            {f g : ∀ {x} → Y x} → (∀ {x} → f {x} ≡ g {x}) → f ≡ g :> (∀ {x} → Y x)

implify : Funext → Funext′
implify funext p = (λ f {x} → f x) ≡.& funext (λ x → p {x})

module ≡-Reasoning where
  open ≡ public

  infix  3 _∎
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  1 begin_

  begin_ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} → x ≡ x′ → x ≡ x′
  begin p = p

  _≡⟨⟩_ : ∀ {𝓍} {X : Set 𝓍} (x : X) {x′ : X} → x ≡ x′ → x ≡ x′
  _ ≡⟨⟩ p = p

  _≡⟨_⟩_ : ∀ {𝓍} {X : Set 𝓍} (x : X) {x′ x″} → x ≡ x′ → x′ ≡ x″ → x ≡ x″
  _ ≡⟨ p ⟩ q = p ⋮ q

  _∎ : ∀ {𝓍} {X : Set 𝓍} (x : X) → x ≡ x
  _ ∎ = refl

uip : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} (p p′ : x ≡ x′) → p ≡ p′
uip refl refl = refl


----------------------------------------------------------------------------------------------------

-- heterogeneous equality
-- TODO: compare with stdlib

infix 4 _≅_
data _≅_ {𝓍} {X : Set 𝓍} (x : X) : ∀ {𝓎} {Y : Set 𝓎} → Y → Set 𝓍 where
   refl : x ≅ x

module ≅ where
  infix 9 _⁻¹
  _⁻¹ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {x : X} {y : Y} → x ≅ y → y ≅ x
  refl ⁻¹ = refl

  infixr 4 _⋮_
  _⋮_ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : Set 𝓏} {x : X} {y : Y} {z : Z} →
          x ≅ y → y ≅ z → x ≅ z
  refl ⋮ q = q

  infixl 9 _&_
  _&_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} (f : ∀ x → Y x) {x x′} →
          x ≅ x′ → f x ≅ f x′
  _ & refl = refl

  infixl 8 _⊗_
  _⊗_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} {f g : ∀ x → Y x} {x x′} →
          f ≅ g → x ≅ x′ → f x ≅ g x′
  refl ⊗ refl = refl

≅→≡ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} → x ≅ x′ → x ≡ x′
≅→≡ refl = refl

≡→≅ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} → x ≡ x′ → x ≅ x′
≡→≅ refl = refl

module ≅-Reasoning where
  open ≅ public

  infix  3 _∎
  infixr 2 _≅⟨⟩_ _≅⟨_⟩_ _≡⟨⟩_ _≡⟨_⟩_
  infix  1 begin_

  begin_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {x : X} {y : Y} → x ≅ y → x ≅ y
  begin p = p

  _≅⟨⟩_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (x : X) {y : Y} → x ≅ y → x ≅ y
  _ ≅⟨⟩ p = p

  _≅⟨_⟩_ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : Set 𝓏} (x : X) {y : Y} {z : Z} →
             x ≅ y → y ≅ z → x ≅ z
  _ ≅⟨ p ⟩ q = p ⋮ q

  _≡⟨⟩_ : ∀ {𝓍} {X : Set 𝓍} (x : X) {x′} → x ≡ x′ → x ≅ x′
  _ ≡⟨⟩ p = ≡→≅ p

  _≡⟨_⟩_ : ∀ {𝓍 𝓏} {X : Set 𝓍} {Z : Set 𝓏} (x : X) {x′} {z : Z} → x ≡ x′ → x′ ≅ z → x ≅ z
  _ ≡⟨ p ⟩ q = ≡→≅ p ⋮ q

  _∎ : ∀ {𝓍} {X : Set 𝓍} (x : X) → x ≅ x
  _ ∎ = refl


----------------------------------------------------------------------------------------------------

-- tiny naive category theory

module Gan (funext : Funext) where
  open ≡ public

  record Category (ℴ 𝓂 : Level) : Set (sucℓ (ℴ ⊔ 𝓂)) where
    field
      Obj  : Set ℴ
      _▻_  : ∀ (x y : Obj) → Set 𝓂
      id   : ∀ {x} → x ▻ x
      _∘_  : ∀ {x y z} (q : y ▻ z) (p : x ▻ y) → x ▻ z
      lid▻ : ∀ {x y} (p : y ▻ x) → id ∘ p ≡ p
      rid▻ : ∀ {x y} (p : y ▻ x) → p ∘ id ≡ p
      ass▻ : ∀ {w x y z} (r : y ▻ z) (q : x ▻ y) (p : w ▻ x) → r ∘ (q ∘ p) ≡ (r ∘ q) ∘ p

    _◅_ : ∀ (y x : Obj) → Set 𝓂
    _◅_ = Pointless.flip _▻_

    _⨾_ : ∀ {x y z} (p : x ▻ y) (q : y ▻ z) → x ▻ z
    _⨾_ = Pointless.flip _∘_

    field
      ◅ssa : ∀ {w x y z} (p : y ◅ z) (q : x ◅ y) (r : w ◅ x) → p ⨾ (q ⨾ r) ≡ (p ⨾ q) ⨾ r

  _ᵒᵖ : ∀ {ℴ 𝓂} (C : Category ℴ 𝓂) → Category ℴ 𝓂
  _ᵒᵖ C = record
      { Obj  = C.Obj
      ; _▻_  = Pointless.flip C._▻_
      ; id   = C.id
      ; _∘_  = Pointless.flip C._∘_
      ; lid▻ = C.rid▻
      ; rid▻ = C.lid▻
      ; ass▻ = C.◅ssa
      ; ◅ssa = C.ass▻
      }
    where
      module C = Category C

  catSet : ∀ (𝓍 : Level) → Category (sucℓ 𝓍) 𝓍
  catSet 𝓍 = record
      { Obj  = Set 𝓍
      ; _▻_  = λ X Y → X → Y
      ; id   = λ x → x
      ; _∘_  = λ q p x → q (p x)
      ; lid▻ = λ _ → refl
      ; rid▻ = λ _ → refl
      ; ass▻ = λ _ _ _ → refl
      ; ◅ssa = λ _ _ _ → refl
      }

  catSet₀ : Category (sucℓ 0ℓ) 0ℓ
  catSet₀ = catSet 0ℓ

  record Functor {ℴ ℴ′ 𝓂 𝓂′} (C : Category ℴ 𝓂) (D : Category ℴ′ 𝓂′) : Set (ℴ ⊔ ℴ′ ⊔ 𝓂 ⊔ 𝓂′) where
    private
      module C = Category C
      module D = Category D

    field
      ƒObj : ∀ (x : C.Obj) → D.Obj
      ƒ    : ∀ {x y} (p : x C.▻ y) → ƒObj x D.▻ ƒObj y
      idƒ  : ∀ {x} → ƒ C.id ≡ D.id :> (ƒObj x D.▻ ƒObj x)
      _∘ƒ_ : ∀ {x y z} (q : y C.▻ z) (p : x C.▻ y) → ƒ (q C.∘ p) ≡ ƒ q D.∘ ƒ p

    op : Functor (C ᵒᵖ) (D ᵒᵖ)
    op = record
        { ƒObj = ƒObj
        ; ƒ    = ƒ
        ; idƒ  = idƒ
        ; _∘ƒ_ = Pointless.flip _∘ƒ_
        }

  Presheaf : ∀ {ℴ 𝓂} (C : Category ℴ 𝓂) (𝓍 : Level) → Set (ℴ ⊔ 𝓂 ⊔ sucℓ 𝓍)
  Presheaf C 𝓍 = Functor (C ᵒᵖ) (catSet 𝓍)


----------------------------------------------------------------------------------------------------

-- term variables, or untyped de Bruijn indices, or finite sets

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} (i : Fin n) → Fin (suc n)

-- numeric literals for term variables
module _ where
  data Fin⟨_>_⟩ : Nat → Nat → Set where
    instance
      zero : ∀ {k} → Fin⟨ suc k > zero ⟩
      suc  : ∀ {k n} {{i : Fin⟨ k > n ⟩}} → Fin⟨ suc k > suc n ⟩

  Fin◇→Fin : ∀ {k} (n : Nat) {{i : Fin⟨ k > n ⟩}} → Fin k
  Fin◇→Fin _       {{zero}} = zero
  Fin◇→Fin (suc n) {{suc}}  = suc (Fin◇→Fin n)

  instance
    literalFin : ∀ {k} → Number (Fin k)
    literalFin {k} = record
        { Constraint = Fin⟨ k >_⟩
        ; fromNat    = Fin◇→Fin
        }

-- order-preserving embeddings of term variables
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

renFin : ∀ {k k′} → k ≤ k′ → Fin k → Fin k′
renFin stop      i       = i
renFin (wk≤ η)   i       = suc (renFin η i)
renFin (lift≤ η) zero    = zero
renFin (lift≤ η) (suc i) = renFin (wk≤ η) i

module _ where
  open ≡

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

-- category of order-preserving embeddings of term variables
module ≤-Gan (funext : Funext) where
  open Gan funext

  cat≤ : Category 0ℓ 0ℓ
  cat≤ = record
      { Obj  = Nat
      ; _▻_  = _≤_
      ; id   = id≤
      ; _∘_  = _∘≤_
      ; lid▻ = lid≤
      ; rid▻ = rid≤
      ; ass▻ = ass≤
      ; ◅ssa = λ η η′ η″ → ass≤ η″ η′ η ⁻¹
      } ᵒᵖ

  pshrenFin : Presheaf cat≤ 0ℓ
  pshrenFin = record
      { ƒObj = λ k → Fin k
      ; ƒ    = renFin
      ; idƒ  = funext idrenFin
      ; _∘ƒ_ = λ η′ η → funext (comprenFin η′ η)
      }


----------------------------------------------------------------------------------------------------

-- leftist lists and vectors

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

-- derivation variables, or typed de Bruijn indices

module _ {𝓍} {X : Set 𝓍} where
  infix 3 _∋_
  data _∋_ : List X → X → Set 𝓍 where
    zero : ∀ {Γ A} → Γ , A ∋ A
    suc  : ∀ {Γ A C} (i : Γ ∋ A) → Γ , C ∋ A

  -- numeric literals for derivation variables
  module _ where
    infix 3 _∋⟨_⟩_
    data _∋⟨_⟩_ : List X → Nat → X → Set 𝓍 where
      instance
        zero : ∀ {Γ A} → Γ , A ∋⟨ zero ⟩ A
        suc  : ∀ {Γ A C n} {{i : Γ ∋⟨ n ⟩ A}} → Γ , C ∋⟨ suc n ⟩ A

    ∋◇→∋ : ∀ {Γ A} (n : Nat) {{i : Γ ∋⟨ n ⟩ A}} → Γ ∋ A
    ∋◇→∋ _       {{zero}} = zero
    ∋◇→∋ (suc n) {{suc}}  = suc (∋◇→∋ n)

    instance
      number∋ : ∀ {Γ A} → Number (Γ ∋ A)
      number∋ {Γ} {A} = record
          { Constraint = Γ ∋⟨_⟩ A
          ; fromNat    = ∋◇→∋
          }

  -- order-preserving embeddings of derivation variables
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

  ren∋ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ∋ A → Γ′ ∋ A
  ren∋ stop      i       = i
  ren∋ (wk⊆ η)   i       = suc (ren∋ η i)
  ren∋ (lift⊆ η) zero    = zero
  ren∋ (lift⊆ η) (suc i) = suc (ren∋ η i)

  module _ where
    open ≡

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

-- category of order-preserving embeddings of derivation variables
module ⊆-Gan (funext : Funext) {𝓍} (X : Set 𝓍) where
  open Gan funext

  cat⊆ : Category 𝓍 𝓍
  cat⊆ = record
      { Obj  = List X
      ; _▻_  = _⊆_
      ; id   = id⊆
      ; _∘_  = _∘⊆_
      ; lid▻ = lid⊆
      ; rid▻ = rid⊆
      ; ass▻ = ass⊆
      ; ◅ssa = λ η η′ η″ → ass⊆ η″ η′ η ⁻¹
      } ᵒᵖ

  pshren∋ : X → Presheaf cat⊆ 𝓍
  pshren∋ A = record
      { ƒObj = λ Γ → Γ ∋ A
      ; ƒ    = ren∋
      ; idƒ  = funext idren∋
      ; _∘ƒ_ = λ η′ η → funext (compren∋ η′ η)
      }


----------------------------------------------------------------------------------------------------

-- continuation/double negation monad/applicative/functor
-- TODO: laws?
module _ where
  return : ∀ {𝓍} {X : Set 𝓍} → X → ¬ ¬ X
  return x = λ k → k x

  infixl 1 _>>=_
  _>>=_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → ¬ ¬ X → (X → ¬ ¬ Y) → ¬ ¬ Y
  mx >>= f = (λ k → mx (λ x → f x k))

  join : ∀ {𝓍} {X : Set 𝓍} → ¬ ¬ ¬ ¬ X → ¬ ¬ X
  join mmx = mmx >>= (λ mx → mx)

  infixl 4 _⊛_
  _⊛_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → ¬ ¬ (X → Y) → ¬ ¬ X → ¬ ¬ Y
  mf ⊛ mx = mf >>= (λ f → mx >>= (λ x → return (f x)))

  infixl 4 _<$>_
  _<$>_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → (X → Y) → ¬ ¬ X → ¬ ¬ Y
  f <$> mx = return f ⊛ mx

  -- TODO: bug?
  -- dnem : ∀ {𝓍} {X : Set 𝓍} → ¬ ¬ (X ∨ ¬ X)
  -- dnem = λ k → k (right (λ k′ → k (left k′)))


----------------------------------------------------------------------------------------------------
