{-

A. Abel, J. Chapman (2014) “Normalization by evaluation in the delay monad”

-}

module AbelChapman where

open import Category.Monad public using (RawMonad)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (∃ ; _×_ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; _$_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; cong₂ ; subst)
open import Size using (Size ; Size<_ ; ∞)
import Relation.Binary.PreorderReasoning as PR




-- 2.  Delay monad


mutual
  data Delay (i : Size) (A : Set) : Set where
    now   : (a : A) → Delay i A
    later : (a∞ : ∞Delay i A) → Delay i A

  record ∞Delay (i : Size) (A : Set) : Set where
    coinductive
    field
      force : {j : Size< i} → Delay j A

open ∞Delay public


never : ∀ {i A} → ∞Delay i A
force never = later never


extract : ∀ {A} (n : ℕ) → Delay ∞ A → Maybe A
extract n       (now a)    = just a
extract zero    (later a∞) = nothing
extract (suc n) (later a∞) = extract n (force a∞)


module Bind where
  mutual
    _>>=_ : ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
    now a >>=    f = f a
    later a∞ >>= f = later (a∞ ∞>>= f)

    _∞>>=_ : ∀ {i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
    force (a∞ ∞>>= f) = force a∞ >>= f

  infixl 1 _>>=_ _∞>>=_

open Bind public using (_∞>>=_)


delayMonad : ∀ {i} → RawMonad (Delay i)
delayMonad {i} = record
  { return = now
  ; _>>=_  = _>>=_ {i}
  }
  where open Bind

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i}) public renaming (_⊛_ to _<*>_)


_∞<$>_ : ∀ {i A B} → (A → B) → ∞Delay i A → ∞Delay i B
f ∞<$> a∞ = a∞ ∞>>= λ a → now (f a)

_=<<₂_,_ : ∀ {i A B C} → (A → B → Delay i C) → Delay i A → Delay i B → Delay i C
f =<<₂ a? , b? = a? >>= λ a → b? >>= λ b → f a b


bind : ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
bind = _>>=_

∞bind : ∀ {i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
∞bind = _∞>>=_


syntax bind  a? (λ a → b?) = a ← a? ⁏ b?
syntax ∞bind a∞ (λ a → b?) = a ∞← a∞ ⁏ b?

infix 30 bind ∞bind


-- 2.1.  Strong bisimilarity


mutual
  data _≈_ {i A} : Delay ∞ A → Delay ∞ A → Set where
    ≈now   : (a : A) → now a ≈ now a
    ≈later : ∀ {a∞ a∞′} → (eq : a∞ ∞≈⟨ i ⟩≈ a∞′) → later a∞ ≈ later a∞′

  _≈⟨_⟩≈_ : ∀ {A} → Delay ∞ A → Size → Delay ∞ A → Set
  _≈⟨_⟩≈_ {A} a? i a?′ = _≈_ {i} {A} a? a?′

  record _∞≈⟨_⟩≈_ {A} (a∞ : ∞Delay ∞ A) (i : Size) (a∞′ : ∞Delay ∞ A) : Set where
    coinductive
    field
      ≈force : {j : Size< i} → force a∞ ≈⟨ j ⟩≈ force a∞′

_∞≈_ : ∀ {i A} → ∞Delay ∞ A → ∞Delay ∞ A → Set
_∞≈_ {i} {A} a∞ a∞′ = _∞≈⟨_⟩≈_ {A} a∞ i a∞′

infix 5 _≈⟨_⟩≈_ _∞≈⟨_⟩≈_ _∞≈_

open _∞≈⟨_⟩≈_ public


mutual
  ≈refl : ∀ {i A} (a? : Delay ∞ A) → a? ≈⟨ i ⟩≈ a?
  ≈refl (now a)    = ≈now a
  ≈refl (later a∞) = ≈later (∞≈refl a∞)

  ∞≈refl : ∀ {i A} (a∞ : ∞Delay ∞ A) → a∞ ∞≈⟨ i ⟩≈ a∞
  ≈force (∞≈refl a∞) = ≈refl (force a∞)


mutual
  ≈sym : ∀ {i A} {a? a?′ : Delay ∞ A} → a? ≈⟨ i ⟩≈ a?′ → a?′ ≈⟨ i ⟩≈ a?
  ≈sym (≈now a)    = ≈now a
  ≈sym (≈later eq) = ≈later (∞≈sym eq)

  ∞≈sym : ∀ {i A} {a∞ a∞′ : ∞Delay ∞ A} → a∞ ∞≈⟨ i ⟩≈ a∞′ → a∞′ ∞≈⟨ i ⟩≈ a∞
  ≈force (∞≈sym eq) = ≈sym (≈force eq)


mutual
  ≈trans : ∀ {i A} {a? a?′ a?″ : Delay ∞ A} →
           a? ≈⟨ i ⟩≈ a?′ → a?′ ≈⟨ i ⟩≈ a?″ → a? ≈⟨ i ⟩≈ a?″
  ≈trans (≈now a)    (≈now .a)    = ≈now a
  ≈trans (≈later eq) (≈later eq′) = ≈later (∞≈trans eq eq′)

  ∞≈trans : ∀ {i A} {a∞ a∞′ a∞″ : ∞Delay ∞ A} →
            a∞ ∞≈⟨ i ⟩≈ a∞′ → a∞′ ∞≈⟨ i ⟩≈ a∞″ → a∞ ∞≈⟨ i ⟩≈ a∞″
  ≈force (∞≈trans eq eq′) = ≈trans (≈force eq) (≈force eq′)


mutual
  bind-assoc : ∀ {i A B C} (a? : Delay ∞ A) →
               {f : A → Delay ∞ B} {g : B → Delay ∞ C} →
               ((a? >>= f) >>= g) ≈⟨ i ⟩≈ (a? >>= λ a → f a >>= g)
  bind-assoc (now a) {k} {l} = ≈refl (k a >>= l)
  bind-assoc (later a∞)      = ≈later (∞bind-assoc a∞)

  ∞bind-assoc : ∀ {i A B C} (a∞ : ∞Delay ∞ A) →
                {f : A → Delay ∞ B} {g : B → Delay ∞ C} →
                ((a∞ ∞>>= f) ∞>>= g) ∞≈⟨ i ⟩≈ (a∞ ∞>>= λ a → f a >>= g)
  ≈force (∞bind-assoc a∞) = bind-assoc (force a∞)


mutual
  bind-cong-l : ∀ {i A B} {a? a?′ : Delay ∞ A} →
                a? ≈⟨ i ⟩≈ a?′ → (f : A → Delay ∞ B) →
                (a? >>= f) ≈⟨ i ⟩≈ (a?′ >>= f)
  bind-cong-l (≈now a)    k = ≈refl (k a)
  bind-cong-l (≈later eq) k = ≈later (∞bind-cong-l eq k)

  ∞bind-cong-l : ∀ {i A B} {a∞ a∞′ : ∞Delay ∞ A} →
                 a∞ ∞≈⟨ i ⟩≈ a∞′ → (f : A → Delay ∞ B) →
                 (a∞ ∞>>= f) ∞≈⟨ i ⟩≈ (a∞′ ∞>>= f)
  ≈force (∞bind-cong-l eq k) = bind-cong-l (≈force eq) k


mutual
  bind-cong-r : ∀ {i A B} (a? : Delay ∞ A) {f g : A → Delay ∞ B} →
                (∀ a → (f a) ≈⟨ i ⟩≈ (g a)) →
                (a? >>= f) ≈⟨ i ⟩≈ (a? >>= g)
  bind-cong-r (now a)    h = h a
  bind-cong-r (later a∞) h = ≈later (∞bind-cong-r a∞ h)

  ∞bind-cong-r : ∀ {i A B} (a∞ : ∞Delay ∞ A) {f g : A → Delay ∞ B} →
                 (∀ a → (f a) ≈⟨ i ⟩≈ (g a)) →
                 (a∞ ∞>>= f) ∞≈⟨ i ⟩≈ (a∞ ∞>>= g)
  ≈force (∞bind-cong-r a∞ h) = bind-cong-r (force a∞) h


map-compose : ∀ {i A B C} (a? : Delay ∞ A) {f : A → B} {g : B → C} →
              (g <$> (f <$> a?)) ≈⟨ i ⟩≈ ((g ∘ f) <$> a?)
map-compose a? = bind-assoc a?


map-cong : ∀ {i A B} {a? a?′ : Delay ∞ A} (f : A → B) →
           a? ≈⟨ i ⟩≈ a?′ → (f <$> a?) ≈⟨ i ⟩≈ (f <$> a?′)
map-cong f eq = bind-cong-l eq (now ∘ f)


≈setoid : (i : Size) (A : Set) → Setoid _ _
≈setoid i A = record
  { Carrier       = Delay ∞ A
  ; _≈_           = _≈_ {i}
  ; isEquivalence = record
    { refl  = λ {a?} → ≈refl a?
    ; sym   = ≈sym
    ; trans = ≈trans
    }
  }

∞≈setoid : (i : Size) (A : Set) → Setoid _ _
∞≈setoid i A = record
  { Carrier       = ∞Delay ∞ A
  ; _≈_           = _∞≈_ {i}
  ; isEquivalence = record
    { refl  = λ {a?} → ∞≈refl a?
    ; sym   = ∞≈sym
    ; trans = ∞≈trans
    }
  }

module ≈-Reasoning {i A} where
  open PR (Setoid.preorder (≈setoid i A)) public
    using (_∎)
    renaming (_≈⟨⟩_ to _≡⟨⟩_ ; _≈⟨_⟩_ to _≡⟨_⟩_ ; _∼⟨_⟩_ to _≈⟨_⟩_ ; begin_ to proof_)

module ∞≈-Reasoning {i A} where
  open PR (Setoid.preorder (∞≈setoid i A)) public
    using (_∎)
    renaming (_≈⟨⟩_ to _≡⟨⟩_ ; _≈⟨_⟩_ to _≡⟨_⟩_ ; _∼⟨_⟩_ to _∞≈⟨_⟩_ ; begin_ to proof_)




-- 2.2.  Convergence


data _⇓_ {A} : Delay ∞ A → A → Set where
  now⇓   : ∀ {a} → now a ⇓ a
  later⇓ : ∀ {a} {a∞ : ∞Delay ∞ A} → force a∞ ⇓ a → later a∞ ⇓ a

_⇓ : ∀ {A} → Delay ∞ A → Set
x ⇓ = ∃ λ a → x ⇓ a


map⇓ : ∀ {A B a} {a? : Delay ∞ A} (f : A → B) → a? ⇓ a → (f <$> a?) ⇓ f a
map⇓ f now⇓        = now⇓
map⇓ f (later⇓ a⇓) = later⇓ (map⇓ f a⇓)

subst≈⇓ : ∀ {A a} {a? a?′ : Delay ∞ A} → a? ⇓ a → a? ≈ a?′ → a?′ ⇓ a
subst≈⇓ now⇓        (≈now a)    = now⇓
subst≈⇓ (later⇓ a⇓) (≈later eq) = later⇓ (subst≈⇓ a⇓ (≈force eq))

bind⇓ : ∀ {A B a b} (f : A → Delay ∞ B) {a? : Delay ∞ A} →
        a? ⇓ a → f a ⇓ b → (a? >>= f) ⇓ b
bind⇓ f now⇓        f⇓ = f⇓
bind⇓ f (later⇓ a⇓) f⇓ = later⇓ (bind⇓ f a⇓ f⇓)




-- 3.  Well-typed terms, values, and coinductive normalization


data Ty : Set where
  ★    : Ty
  _⇒_ : (a b : Ty) → Ty

infixr 5 _⇒_

data Cx : Set where
  ε   : Cx
  _,_ : (Γ : Cx) (a : Ty) → Cx

data Var : Cx → Ty → Set where
  top : ∀ {Γ a}                 → Var (Γ , a) a
  pop : ∀ {Γ a b} (x : Var Γ a) → Var (Γ , b) a

data Tm (Γ : Cx) : Ty → Set where
  var : ∀ {a}   (x : Var Γ a)                    → Tm Γ a
  lam : ∀ {a b} (t : Tm (Γ , a) b)               → Tm Γ (a ⇒ b)
  app : ∀ {a b} (t : Tm Γ (a ⇒ b)) (u : Tm Γ a) → Tm Γ b

data Ne (Ξ : Cx → Ty → Set) (Γ : Cx) : Ty → Set where
  var : ∀ {a}   (x : Var Γ a)                         → Ne Ξ Γ a
  app : ∀ {a b} (m∣w : Ne Ξ Γ (a ⇒ b)) (n∣v : Ξ Γ a) → Ne Ξ Γ b

data Nf (Δ : Cx) : Ty → Set where
  ne  : (m : Ne Nf Δ ★)             → Nf Δ ★
  lam : ∀ {a b} (n : Nf (Δ , a) b) → Nf Δ (a ⇒ b)

mutual
  data Val (Δ : Cx) : Ty → Set where
    ne  : ∀ {a}     (w : Ne Val Δ a)                 → Val Δ a
    lam : ∀ {Γ a b} (w : Tm (Γ , a) b) (v : Env Δ Γ) → Val Δ (a ⇒ b)

  data Env (Δ : Cx) : Cx → Set where
    ε   : Env Δ ε
    _,_ : ∀ {Γ a} (ρ : Env Δ Γ) (v : Val Δ a) → Env Δ (Γ , a)

lookup : ∀ {Γ Δ a} → Var Γ a → Env Δ Γ → Val Δ a
lookup top     (ρ , v) = v
lookup (pop x) (ρ , v) = lookup x ρ


mutual
  eval : ∀ {i Γ Δ b} → Tm Γ b → Env Δ Γ → Delay i (Val Δ b)
  eval (var x)   ρ = now (lookup x ρ)
  eval (lam t)   ρ = now (lam t ρ)
  eval (app t u) ρ = apply =<<₂ eval t ρ , eval u ρ

  apply : ∀ {i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → Delay i (Val Δ b)
  apply (ne w)    v = now (ne (app w v))
  apply (lam t ρ) v = later (beta t ρ v)

  beta : ∀ {i Γ Δ a b} → Tm (Γ , a) b → Env Δ Γ → Val Δ a → ∞Delay i (Val Δ b)
  force (beta t ρ v) = eval t (ρ , v)


-- Order-preserving embeddings

data _≤_ : (Γ Γ′ : Cx) → Set where
  id   : ∀ {Γ}      → Γ ≤ Γ
  weak : ∀ {Γ Γ′ a} → Γ ≤ Γ′ → (Γ , a) ≤ Γ′
  lift : ∀ {Γ Γ′ a} → Γ ≤ Γ′ → (Γ , a) ≤ (Γ′ , a)

_∙_ : ∀ {Γ Γ′ Γ″} → Γ ≤ Γ′ → Γ′ ≤ Γ″ → Γ ≤ Γ″
id     ∙ η′      = η′
weak η ∙ η′      = weak (η ∙ η′)
lift η ∙ id      = lift η
lift η ∙ weak η′ = weak (η ∙ η′)
lift η ∙ lift η′ = lift (η ∙ η′)


η∙id : ∀ {Γ Γ′} (η : Γ ≤ Γ′) → η ∙ id ≡ η
η∙id id       = refl
η∙id (weak η) = cong weak (η∙id η)
η∙id (lift η) = refl

id∙η : ∀ {Γ Γ′} (η : Γ ≤ Γ′) → id ∙ η ≡ η
id∙η id       = refl
id∙η (weak η) = refl
id∙η (lift η) = cong lift (id∙η η)

compose-assoc : ∀ {Γ Γ′ Γ″ Γ‴} (η : Γ ≤ Γ′) (η′ : Γ′ ≤ Γ″) (η″ : Γ″ ≤ Γ‴) →
                (η ∙ η′) ∙ η″ ≡ η ∙ (η′ ∙ η″)
compose-assoc id       η′        η″        = refl
compose-assoc (weak η) η′        η″        = cong weak (compose-assoc η η′ η″)
compose-assoc (lift η) id        η″        = refl
compose-assoc (lift η) (weak η′) η″        = cong weak (compose-assoc η η′ η″)
compose-assoc (lift η) (lift η′) id        = refl
compose-assoc (lift η) (lift η′) (weak η″) = cong weak (compose-assoc η η′ η″)
compose-assoc (lift η) (lift η′) (lift η″) = cong lift (compose-assoc η η′ η″)

compose-resp-≡ : ∀ {Γ Γ′ Γ″} {η η′ : Γ ≤ Γ′} {η″ η‴ : Γ′ ≤ Γ″} →
                 η ≡ η′ → η″ ≡ η‴ → (η ∙ η″) ≡ (η′ ∙ η‴)
compose-resp-≡ refl refl = refl

--module _ where
--  open import Categories.Category using (Category)
--  open import Function using (flip)
--  open import Relation.Binary.PropositionalEquality using (sym ; isEquivalence)
--
--  OPE : Category _ _ _
--  OPE = record
--    { Obj       = Cx
--    ; _⇒_      = _≤_
--    ; _≡_       = _≡_
--    ; _∘_       = flip _∙_
--    ; id        = id
--    ; assoc     = λ {_} {_} {_} {_} {η} {η′} {η″} → sym (compose-assoc η η′ η″)
--    ; identityˡ = λ {_} {_} {η} → η∙id η
--    ; identityʳ = λ {_} {_} {η} → id∙η η
--    ; equiv     = isEquivalence
--    ; ∘-resp-≡  = flip compose-resp-≡
--    }


mutual
  var≤ : ∀ {Γ Γ′ a} → Γ ≤ Γ′ → Var Γ′ a → Var Γ a
  var≤ id       x       = x
  var≤ (weak η) x       = pop (var≤ η x)
  var≤ (lift η) top     = top
  var≤ (lift η) (pop x) = pop (var≤ η x)

  nen≤ : ∀ {Δ Δ′ a} → Δ ≤ Δ′ → Ne Nf Δ′ a → Ne Nf Δ a
  nen≤ η (var x)   = var (var≤ η x)
  nen≤ η (app m n) = app (nen≤ η m) (nf≤ η n)

  nev≤ : ∀ {Δ Δ′ a} → Δ ≤ Δ′ → Ne Val Δ′ a → Ne Val Δ a
  nev≤ η (var x)   = var (var≤ η x)
  nev≤ η (app w v) = app (nev≤ η w) (val≤ η v)

  nf≤ : ∀ {Δ Δ′ a} → Δ ≤ Δ′ → Nf Δ′ a → Nf Δ a
  nf≤ η (ne m)  = ne (nen≤ η m)
  nf≤ η (lam n) = lam (nf≤ (lift η) n )

  val≤ : ∀ {Δ Δ′ a} → Δ ≤ Δ′ → Val Δ′ a → Val Δ a
  val≤ η (ne w)    = ne (nev≤ η w)
  val≤ η (lam t ρ) = lam t (env≤ η ρ)

  env≤ : ∀ {Δ Δ′ Γ} → Δ ≤ Δ′ → Env Δ′ Γ → Env Δ Γ
  env≤ η ε       = ε
  env≤ η (ρ , v) = env≤ η ρ , val≤ η v

wk : ∀ {Γ a} → (Γ , a) ≤ Γ
wk = weak id

weakVal : ∀ {Δ a c} → Val Δ c → Val (Δ , a) c
weakVal = val≤ wk


mutual
  readback : ∀ {i Δ a} → Val Δ a → Delay i (Nf Δ a)
  readback {a = ★}      (ne w) = ne <$> nereadback w
  readback {a = _ ⇒ _} v      = lam <$> later (eta v)

  nereadback : ∀ {i Δ a} → Ne Val Δ a → Delay i (Ne Nf Δ a)
  nereadback (var x)   = now (var x)
  nereadback (app w v) = m ← nereadback w ⁏
                         (app m <$> readback v)

  eta : ∀ {i Δ a b} → Val Δ (a ⇒ b) → ∞Delay i (Nf (Δ , a) b)
  force (eta v) = readback =<< apply (weakVal v) (ne (var top))


ide : (Γ : Cx) → Env Γ Γ
ide ε       = ε
ide (Γ , a) = env≤ wk (ide Γ) , ne (var top)


nf : ∀ {Γ a} → Tm Γ a → Delay ∞ (Nf Γ a)
nf {Γ} t = readback =<< eval t (ide Γ)




-- 4.  Termination proof


mutual
  V⟦_⟧_ : ∀ {Γ} (a : Ty) → Val Γ a → Set
  V⟦ ★ ⟧      ne w = nereadback w ⇓
  V⟦ a ⇒ b ⟧ f    = ∀ {Δ} (η : Δ ≤ _) (u : Val Δ a) →
                     V⟦ a ⟧ u → C⟦ b ⟧ (apply (val≤ η f) u)

  C⟦_⟧_ : ∀ {Γ} (a : Ty) → Delay ∞ (Val Γ a) → Set
  C⟦ a ⟧ v? = ∃ λ v → v? ⇓ v × V⟦ a ⟧ v


E⟦_⟧_ : ∀ {Δ} (Γ : Cx) → Env Δ Γ → Set
E⟦ ε ⟧     ε       = ⊤
E⟦ Γ , a ⟧ (ρ , v) = E⟦ Γ ⟧ ρ × V⟦ a ⟧ v


mutual
  var≤-id : ∀ {Δ a} (x : Var Δ a) → var≤ id x ≡ x
  var≤-id x = refl

  nev≤-id : ∀ {Δ a} (t : Ne Val Δ a) → nev≤ id t ≡ t
  nev≤-id (var x)   = refl
  nev≤-id (app t u) = cong₂ app (nev≤-id t) (val≤-id u)

  val≤-id : ∀ {Δ a} (v : Val Δ a) → val≤ id v ≡ v
  val≤-id (ne w)    = cong ne (nev≤-id w)
  val≤-id (lam t ρ) = cong (lam t) (env≤-id ρ)

  env≤-id : ∀ {Γ Δ} (ρ : Env Δ Γ) → env≤ id ρ ≡ ρ
  env≤-id ε       = refl
  env≤-id (ρ , v) = cong₂ _,_ (env≤-id ρ) (val≤-id v)


mutual
  var≤-∙ : ∀ {Δ Δ′ Δ″ a} (η : Δ ≤ Δ′) (η′ : Δ′ ≤ Δ″) (x : Var Δ″ a) →
           var≤ η (var≤ η′ x) ≡ var≤ (η ∙ η′) x
  var≤-∙ id       η′        x       = refl
  var≤-∙ (weak η) η′        x       = cong pop (var≤-∙ η η′ x)
  var≤-∙ (lift η) id        x       = refl
  var≤-∙ (lift η) (weak η′) x       = cong pop (var≤-∙ η η′ x)
  var≤-∙ (lift η) (lift η′) top     = refl
  var≤-∙ (lift η) (lift η′) (pop x) = cong pop (var≤-∙ η η′ x)

  nev≤-∙ : ∀ {Δ Δ′ Δ″ a} (η : Δ ≤ Δ′) (η′ : Δ′ ≤ Δ″) (t : Ne Val Δ″ a) →
           nev≤ η (nev≤ η′ t) ≡ nev≤ (η ∙ η′) t
  nev≤-∙ η η′ (var x)   = cong var (var≤-∙ η η′ x)
  nev≤-∙ η η′ (app w v) = cong₂ app (nev≤-∙ η η′ w) (val≤-∙ η η′ v)

  val≤-∙ : ∀ {Δ Δ′ Δ″ a} (η : Δ ≤ Δ′) (η′ : Δ′ ≤ Δ″) (v : Val Δ″ a) →
           val≤ η (val≤ η′ v) ≡ val≤ (η ∙ η′) v
  val≤-∙ η η′ (ne w)    = cong ne (nev≤-∙ η η′ w)
  val≤-∙ η η′ (lam t ρ) = cong (lam t) (env≤-∙ η η′ ρ)

  env≤-∙ : ∀ {Γ Δ Δ′ Δ″} (η : Δ ≤ Δ′) (η′ : Δ′ ≤ Δ″) (ρ : Env Δ″ Γ) →
           env≤ η (env≤ η′ ρ) ≡ env≤ (η ∙ η′) ρ
  env≤-∙ η η′ ε       = refl
  env≤-∙ η η′ (ρ , v) = cong₂ _,_ (env≤-∙ η η′ ρ) (val≤-∙ η η′ v)


mutual
  lookup≤ : ∀ {Γ Δ Δ′ a} (η : Δ′ ≤ Δ) (x : Var Γ a) (ρ : Env Δ Γ) →
            val≤ η (lookup x ρ) ≡ lookup x (env≤ η ρ)
  lookup≤ η top     (ρ , v) = refl
  lookup≤ η (pop x) (ρ , v) = lookup≤ η x ρ


  eval≤ : ∀ {i Γ Δ Δ′ a} (η : Δ′ ≤ Δ) (t : Tm Γ a) (ρ : Env Δ Γ) →
          (val≤ η <$> eval t ρ) ≈⟨ i ⟩≈ eval t (env≤ η ρ)
  eval≤ η (var x)   ρ rewrite lookup≤ η x ρ = ≈now (lookup x (env≤ η ρ))
  eval≤ η (lam t)   ρ = ≈now (lam t (env≤ η ρ))
  eval≤ η (app t u) ρ =
    proof
          x ← (w ← eval t ρ ⁏
                v ← eval u ρ ⁏
                apply w v) ⁏
          now (val≤ η x)
    ≈⟨ bind-assoc (eval t ρ) ⟩
          w ← eval t ρ ⁏
          x ← (v ← eval u ρ ⁏
                apply w v) ⁏
          now (val≤ η x)
    ≈⟨ bind-cong-r (eval t ρ)
                   (λ w → bind-assoc (eval u ρ)) ⟩
          w ← eval t ρ ⁏
          v ← eval u ρ ⁏
          x ← apply w v ⁏
          now (val≤ η x)
    ≈⟨ bind-cong-r (eval t ρ)
                   (λ w → bind-cong-r (eval u ρ)
                                       (λ v → apply≤ η w v )) ⟩
          w ← eval t ρ ⁏
          v ← eval u ρ ⁏
          apply (val≤ η w) (val≤ η v)
    ≡⟨⟩
          w  ← eval t ρ ⁏
          v  ← eval u ρ ⁏
          v′ ← now (val≤ η v) ⁏
          apply (val≤ η w) v′
    ≈⟨ bind-cong-r (eval t ρ)
                   (λ w → ≈sym (bind-assoc (eval u ρ))) ⟩
          w  ← eval t ρ ⁏
          v′ ← (v ← eval u ρ ⁏
                 now (val≤ η v)) ⁏
          apply (val≤ η w) v′
    ≈⟨ bind-cong-r (eval t ρ)
                   (λ w → bind-cong-l (eval≤ η u ρ) (λ v′ → _)) ⟩
          w  ← eval t ρ ⁏
          v′ ← eval u (env≤ η ρ) ⁏
          apply (val≤ η w) v′
    ≡⟨⟩
          w  ← eval t ρ ⁏
          w′ ← now (val≤ η w) ⁏
          v′ ← eval u (env≤ η ρ) ⁏
          apply w′ v′
    ≈⟨ ≈sym (bind-assoc (eval t ρ)) ⟩
          w′ ← (w ← eval t ρ ⁏
                 now (val≤ η w)) ⁏
          v′ ← eval u (env≤ η ρ) ⁏
          apply w′ v′
    ≈⟨ bind-cong-l (eval≤ η t ρ) (λ w′ → _) ⟩
          w′ ← eval t (env≤ η ρ) ⁏
          v′ ← eval u (env≤ η ρ) ⁏
          apply w′ v′
    ∎
    where open ≈-Reasoning


  apply≤ : ∀ {i Δ Δ′ a b} (η : Δ′ ≤ Δ)
           (f : Val Δ (a ⇒ b)) (v : Val Δ a) →
           (val≤ η <$> apply f v) ≈⟨ i ⟩≈ apply (val≤ η f) (val≤ η v)
  apply≤ η (ne w)    v = ≈refl _
  apply≤ η (lam t ρ) v = ≈later (beta≤ η t ρ v)


  beta≤ : ∀ {i Γ Δ Δ′ a b} (η : Δ′ ≤ Δ)
           (t : Tm (Γ , a) b) → (ρ : Env Δ Γ) (v : Val Δ a) →
           (val≤ η ∞<$> beta t ρ v) ∞≈⟨ i ⟩≈ beta t (env≤ η ρ) (val≤ η v)
  ≈force (beta≤ η t ρ v) = eval≤ η t (ρ , v)


  nereadback≤ : ∀ {i Δ Δ′ a} (η : Δ′ ≤ Δ) (t : Ne Val Δ a) →
                (nen≤ η <$> nereadback t) ≈⟨ i ⟩≈ nereadback (nev≤ η t)
  nereadback≤ η (var x)   = ≈now _
  nereadback≤ η (app t u) =
    proof
          x ← (m ← nereadback t ⁏
                n ← readback u ⁏
                now (app m n)) ⁏
          now (nen≤ η x)
    ≈⟨ bind-assoc (nereadback t) ⟩
          m ← nereadback t ⁏
          x ← (n ← readback u ⁏
                now (app m n)) ⁏
          now (nen≤ η x)
    ≈⟨ bind-cong-r (nereadback t)
                   (λ m → bind-assoc (readback u)) ⟩
          m ← nereadback t ⁏
          n ← readback u ⁏
          x ← now (app m n) ⁏
          now (nen≤ η x)
    ≡⟨⟩
          m ← nereadback t ⁏
          n ← readback u ⁏
          now (app (nen≤ η m) (nf≤ η n))
    ≡⟨⟩
          m  ← nereadback t ⁏
          n  ← readback u ⁏
          n′ ← now (nf≤ η n) ⁏
          now (app (nen≤ η m) n′)
    ≈⟨ bind-cong-r (nereadback t)
                   (λ m → ≈sym (bind-assoc (readback u))) ⟩
          m  ← nereadback t ⁏
          n′ ← (n ← readback u ⁏
                 now (nf≤ η n)) ⁏
          now (app (nen≤ η m) n′)
    ≡⟨⟩
          m  ← nereadback t ⁏
          m′ ← now (nen≤ η m) ⁏
          n′ ← (n ← readback u ⁏
                 now (nf≤ η n)) ⁏
          now (app m′ n′)
    ≈⟨ ≈sym (bind-assoc (nereadback t)) ⟩
          m′ ← (m ← nereadback t ⁏
                 now (nen≤ η m)) ⁏
          n′ ← (n ← readback u ⁏
                 now (nf≤ η n)) ⁏
          now (app m′ n′)
    ≡⟨⟩
          m′ ← nen≤ η <$> nereadback t ⁏
          n′ ← nf≤ η <$> readback u ⁏
          now (app m′ n′)
    ≈⟨ bind-cong-r (nen≤ η <$> nereadback t)
                   (λ m′ → bind-cong-l (readback≤ _ η u)
                                        (λ n → _)) ⟩
          m′ ← nen≤ η <$> nereadback t ⁏
          n′ ← readback (val≤ η u) ⁏
          now (app m′ n′)
    ≈⟨ bind-cong-l (nereadback≤ η t) (λ _ → _) ⟩
          m′ ← nereadback (nev≤ η t) ⁏
          n′ ← readback (val≤ η u) ⁏
          now (app m′ n′)
    ∎
    where open ≈-Reasoning


  readback≤ : ∀ {i Δ Δ′} (a : Ty) (η : Δ′ ≤ Δ) (v : Val Δ a) →
              (nf≤ η <$> readback v) ≈⟨ i ⟩≈ readback (val≤ η v)
  readback≤ ★ η (ne w) =
    proof
          nf≤ η <$> (ne <$> nereadback w)
    ≈⟨ map-compose (nereadback w) ⟩
          (nf≤ η ∘ ne) <$> nereadback w
    ≡⟨⟩
          (ne ∘ nen≤ η) <$> nereadback w
    ≈⟨ ≈sym (map-compose (nereadback w)) ⟩
          ne <$> (nen≤ η <$> nereadback w)
    ≈⟨ map-cong ne (nereadback≤ η w) ⟩
          ne <$> nereadback (nev≤ η w)
    ∎
    where open ≈-Reasoning
  readback≤ (a ⇒ b) η v = ≈later $
    proof
          n′ ∞← (n ∞← eta v ⁏
                  now (lam n)) ⁏
          now (nf≤ η n′)
    ∞≈⟨ ∞bind-assoc (eta v) ⟩
          n ∞← eta v ⁏
          n′ ← now (lam n) ⁏
          now (nf≤ η n′)
    ≡⟨⟩
          n ∞← eta v ⁏
          now (lam (nf≤ (lift η) n))
    ≡⟨⟩
          n ∞← eta v ⁏
          n′ ← now (nf≤ (lift η) n) ⁏
          now (lam n′)
    ∞≈⟨ ∞≈sym (∞bind-assoc (eta v)) ⟩
          n′ ∞← n ∞← eta v ⁏
                 now (nf≤ (lift η) n) ⁏
          now (lam n′)
    ∞≈⟨ ∞bind-cong-l (eta≤ η v) (λ n → now (lam n)) ⟩
          n′ ∞← eta (val≤ η v) ⁏
          now (lam n′)
    ∎
    where open ∞≈-Reasoning


  eta≤ : ∀ {i Δ Δ′ a b} (η : Δ′ ≤ Δ) (v : Val Δ (a ⇒ b)) →
         (nf≤ (lift η) ∞<$> eta v) ∞≈⟨ i ⟩≈ eta (val≤ η v)
  ≈force (eta≤ η v) =
    proof
          n′ ← apply (weakVal v) (ne (var top)) >>= readback ⁏
          now (nf≤ (lift η) n′)
    ≈⟨ bind-assoc (apply (weakVal v) (ne (var top))) ⟩
          n ← apply (weakVal v) (ne (var top)) ⁏
          n′ ← readback n ⁏
          now (nf≤ (lift η) n′)
    ≈⟨ bind-cong-r (apply (weakVal v) (ne (var top)))
                   (λ n → readback≤ _ (lift η) n) ⟩
          n ← apply (weakVal v) (ne (var top)) ⁏
          readback (val≤ (lift η) n)
    ≡⟨⟩
          n ← apply (weakVal v) (ne (var top)) ⁏
          (now (val≤ (lift η) n) >>= readback)
    ≈⟨ ≈sym (bind-assoc (apply (weakVal v) (ne (var top)))) ⟩
          ((n ← apply (weakVal v) (ne (var top)) ⁏
            now (val≤ (lift η) n)) >>= readback)
    ≈⟨ bind-cong-l (apply≤ (lift η) (weakVal v) (ne (var top))) readback ⟩
          (apply (val≤ (lift η) (val≤ wk v)) (ne (var top)) >>= readback)
    ≡⟨ cong (λ v′ → apply v′ (ne (var top)) >>= readback)
            (val≤-∙ (lift η) wk v) ⟩
          (apply (val≤ (weak (η ∙ id)) v) (ne (var top)) >>= readback)
    ≡⟨ cong (λ η′ → apply (val≤ (weak η′) v) (ne (var top)) >>= readback)
            (η∙id η) ⟩
          (apply (val≤ (weak η) v) (ne (var top)) >>= readback)
    ≡⟨ cong (λ v′ → apply v′ (ne (var top)) >>= readback)
            (sym (val≤-∙ wk η v)) ⟩
          (apply (weakVal (val≤ η v)) (ne (var top)) >>= readback)
    ∎
    where open ≈-Reasoning




nereadback≤⇓ : ∀ {Δ Δ′ a} (η : Δ′ ≤ Δ) (v : Ne Val Δ a) {n : Ne Nf Δ a} →
               nereadback v ⇓ n → nereadback (nev≤ η v) ⇓ nen≤ η n
nereadback≤⇓ η v p = subst≈⇓ (map⇓ (nen≤ η) p) (nereadback≤ η v)


V⟦⟧≤ : ∀ {Δ Δ′} (a : Ty) (η : Δ′ ≤ Δ) (v : Val Δ a) → V⟦ a ⟧ v → V⟦ a ⟧ (val≤ η v)
V⟦⟧≤ ★        η (ne w) = λ { (n , p) → nen≤ η n , nereadback≤⇓ η w p }
V⟦⟧≤ (a ⇒ b) η f      = λ c η′ u u⇓ →
     let v , v⇓ , ⟦v⟧ = c (η′ ∙ η) u u⇓
     in  v , subst (λ f′ → apply f′ u ⇓ v) (sym (val≤-∙ η′ η f)) v⇓ , ⟦v⟧


E⟦⟧≤ : ∀ {Γ Δ Δ′} (η : Δ′ ≤ Δ) (ρ : Env Δ Γ) → E⟦ Γ ⟧ ρ → E⟦ Γ ⟧ (env≤ η ρ)
E⟦⟧≤ η ε       tt          = tt
E⟦⟧≤ η (ρ , v) (⟦ρ⟧ , ⟦v⟧) = E⟦⟧≤ η ρ ⟦ρ⟧ , V⟦⟧≤ _ η v ⟦v⟧


⟦var⟧ : ∀ {Γ Δ a} (x : Var Γ a) (ρ : Env Δ Γ) → E⟦ Γ ⟧ ρ → C⟦ a ⟧ (now (lookup x ρ))
⟦var⟧ top     (_ , v) (_ , ⟦v⟧) = v , now⇓ , ⟦v⟧
⟦var⟧ (pop x) (ρ , _) (θ , _)   = ⟦var⟧ x ρ θ


sound-β : ∀ {Γ Δ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (u : Val Δ a) →
          C⟦ b ⟧ (eval t (ρ , u)) → C⟦ b ⟧ (apply (lam t ρ) u)
sound-β t ρ u (v , v⇓ , ⟦v⟧) = v , later⇓ v⇓ , ⟦v⟧


⟦lam⟧ : ∀ {Γ Δ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) →
        (∀ {Δ′} (η : Δ′ ≤ Δ) (u : Val Δ′ a) (u⇓ : V⟦ a ⟧ u) → C⟦ b ⟧ (eval t (env≤ η ρ , u))) →
        C⟦ a ⇒ b ⟧ (now (lam t ρ))
⟦lam⟧ t ρ θ ih = lam t ρ , now⇓ , (λ η u p → sound-β t (env≤ η ρ) u (ih η u p))


⟦app⟧ : ∀ {Δ a b} {f? : Delay _ (Val Δ (a ⇒ b))} {u? : Delay _ (Val Δ a)} →
        C⟦ a ⇒ b ⟧ f? → C⟦ a ⟧ u? → C⟦ b ⟧ (f? >>= λ f → u? >>= apply f)
⟦app⟧ {u? = u?} (f , f⇓ , ⟦f⟧) (u , u⇓ , ⟦u⟧) =
      let v , v⇓ , ⟦v⟧ = ⟦f⟧ id u ⟦u⟧
          v⇓′          = bind⇓ (λ f′ → u? >>= apply f′)
                               f⇓
                               (bind⇓ (apply f)
                                      u⇓
                                      (subst (λ f′ → apply f′ u ⇓ v)
                                             (val≤-id f)
                                             v⇓))
      in  v , v⇓′ , ⟦v⟧


term : ∀ {Γ Δ a} (t : Tm Γ a) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) → C⟦ a ⟧ (eval t ρ)
term (var x)   ρ θ = ⟦var⟧ x ρ θ
term (lam t)   ρ θ = ⟦lam⟧ t ρ θ (λ η u p → term t (env≤ η ρ , u) (E⟦⟧≤ η ρ θ , p))
term (app t u) ρ θ = ⟦app⟧ (term t ρ θ) (term u ρ θ)


mutual
  reify : ∀ {Γ} (a : Ty) (v : Val Γ a) → V⟦ a ⟧ v → readback v ⇓
  reify ★        (ne w) (m , ⇓m) = ne m , map⇓ ne ⇓m
  reify (a ⇒ b) f      ⟦f⟧      =
        let u            = ne (var top)
            ⟦u⟧          = reflect a (var top) (var top , now⇓)
            v , v⇓ , ⟦v⟧ = ⟦f⟧ wk u ⟦u⟧
            n , ⇓n       = reify b v ⟦v⟧
            ⇓λn          = later⇓ (bind⇓ (λ f′ → now (lam f′))
                                         (bind⇓ readback v⇓ ⇓n)
                                         now⇓)
        in  lam n , ⇓λn

  reflect : ∀ {Γ} (a : Ty) (w : Ne Val Γ a) → nereadback w ⇓ → V⟦ a ⟧ (ne w)
  reflect ★        w w⇓        = w⇓
  reflect (a ⇒ b) w (m , w⇓m) = λ η u ⟦u⟧ →
          let n , ⇓n = reify a u ⟦u⟧
              m′     = nen≤ η m
              ⇓m     = nereadback≤⇓ η w w⇓m
              wu     = app (nev≤ η w) u
              ⟦wu⟧   = reflect b wu (app m′ n ,
                                     bind⇓ (λ m → app m <$> readback u)
                                           ⇓m
                                           (bind⇓ (λ n → now (app m′ n)) ⇓n now⇓))
          in  ne wu , now⇓ , ⟦wu⟧


var↑ : ∀ {Γ a} (x : Var Γ a) → V⟦ a ⟧ ne (var x)
var↑ {a = a} x = reflect a (var x) (var x , now⇓)


⟦ide⟧ : (Γ : Cx) → E⟦ Γ ⟧ (ide Γ)
⟦ide⟧ ε       = tt
⟦ide⟧ (Γ , a) = E⟦⟧≤ wk (ide Γ) (⟦ide⟧ Γ) , var↑ top


normalize : (Γ : Cx) (a : Ty) (t : Tm Γ a) → ∃ λ n → nf t ⇓ n
normalize Γ a t = let v , v⇓ , ⟦v⟧ = term t (ide Γ) (⟦ide⟧ Γ)
                      n , ⇓n       = reify a v ⟦v⟧
                  in  n , bind⇓ readback v⇓ ⇓n
