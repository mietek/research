{-# OPTIONS --allow-unsolved-metas --sized-types #-}

module A201605.AbelChapmanPlus where

open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Function using (_∘_ ; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)
open import Relation.Nullary using (Dec ; yes ; no)
open import Size using (Size ; Size<_ ; ∞)

open import A201605.Prelude




-- 2.  Delay monad


mutual
  data Delay (i : Size) (A : Set) : Set where
    now   : (a : A)           → Delay i A
    later : (a∞ : ∞Delay i A) → Delay i A

  record ∞Delay (i : Size) (A : Set) : Set where
    coinductive
    field
      force : {j : Size< i} → Delay j A

open ∞Delay


never : ∀{i A} → ∞Delay i A
force (never {i}) {j} = later (never {j})


mutual
  _>>=_ : ∀{i A B} → Delay i A → (A → Delay i B) → Delay i B
  now   a  >>= f = f a
  later a∞ >>= f = later (a∞ ∞>>= f)

  _∞>>=_ : ∀{i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
  force (a∞ ∞>>= f) = force a∞ >>= f


bind : ∀{i A B} → Delay i A → (A → Delay i B) → Delay i B
bind = _>>=_

∞bind : ∀{i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
∞bind = _∞>>=_

syntax bind  a? (λ a → b?) = a ← a? ⁏ b?
syntax ∞bind a∞ (λ a → b?) = a ∞← a∞ ⁏ b?

infix 0 bind ∞bind


_<*>_ : ∀{i A B} → Delay i (A → B) → Delay i A → Delay i B
f? <*> a? = f ← f? ⁏
            a ← a? ⁏
            now (f a)

_<$>_ : ∀{i A B} → (A → B) → Delay i A → Delay i B
f <$> a? = now f <*> a?

_∞<$>_ : ∀{i A B} → (A → B) → ∞Delay i A → ∞Delay i B
f ∞<$> a∞ = a ∞← a∞ ⁏
            now (f a)



-- 2.1.  Strong bisimilarity


mutual
  data _≈_ {i : Size}{A : Set} : (a? b? : Delay ∞ A) → Set where
    ≈now   : (a : A)                            → now a ≈ now a
    ≈later : ∀{a∞ b∞} → (eq : a∞ ∞≈[ i ]≈ b∞) → later a∞ ≈ later b∞

  _≈[_]≈_ : {A : Set} (a? : Delay ∞ A) (i : Size) (b? : Delay ∞ A) → Set
  _≈[_]≈_ {A} a? i b? = _≈_ {i} {A} a? b?

  record _∞≈[_]≈_ {A} (a∞ : ∞Delay ∞ A) (i : Size) (b∞ : ∞Delay ∞ A) : Set where
    coinductive
    field
      ≈force : {j : Size< i} → force a∞ ≈[ j ]≈ force b∞

_∞≈_ : {i : Size}{A : Set} (a∞ b∞ : ∞Delay ∞ A) → Set
_∞≈_ {i} {A} a∞ b∞ = _∞≈[_]≈_ {A} a∞ i b∞

open _∞≈[_]≈_


mutual
  ≈refl : ∀{i A} (a? : Delay ∞ A) → a? ≈[ i ]≈ a?
  ≈refl (now a)    = ≈now a
  ≈refl (later a∞) = ≈later (∞≈refl a∞)

  ∞≈refl : ∀{i A} (a∞ : ∞Delay ∞ A) → a∞ ∞≈[ i ]≈ a∞
  ≈force (∞≈refl a∞) = ≈refl (force a∞)


mutual
  ≈sym : ∀{i A}{a? b? : Delay ∞ A} → a? ≈[ i ]≈ b? → b? ≈[ i ]≈ a?
  ≈sym (≈now a)    = ≈now a
  ≈sym (≈later eq) = ≈later (∞≈sym eq)

  ∞≈sym : ∀{i A}{a∞ b∞ : ∞Delay ∞ A} → a∞ ∞≈[ i ]≈ b∞ → b∞ ∞≈[ i ]≈ a∞
  ≈force (∞≈sym eq) = ≈sym (≈force eq)


mutual
  ≈trans : ∀{i A}{a? b? c? : Delay ∞ A} → a? ≈[ i ]≈ b? → b? ≈[ i ]≈ c? → a? ≈[ i ]≈ c?
  ≈trans (≈now a)    (≈now .a)    = ≈now a
  ≈trans (≈later eq) (≈later eq′) = ≈later (∞≈trans eq eq′)

  ∞≈trans : ∀{i A}{a∞ b∞ c∞ : ∞Delay ∞ A} → a∞ ∞≈[ i ]≈ b∞ → b∞ ∞≈[ i ]≈ c∞ → a∞ ∞≈[ i ]≈ c∞
  ≈force (∞≈trans eq eq′) = ≈trans (≈force eq) (≈force eq′)


mutual
  bind-assoc : ∀{i A B C} (a? : Delay ∞ A)
               {k : A → Delay ∞ B}{l : B → Delay ∞ C} →
               ((a? >>= k) >>= l) ≈[ i ]≈ (a? >>= λ a → (k a >>= l))
  bind-assoc (now a) {k} {l} = ≈refl (k a >>= l)
  bind-assoc (later a∞)      = ≈later (∞bind-assoc a∞)

  ∞bind-assoc : ∀{i A B C} (a∞ : ∞Delay ∞ A)
                {k : A → Delay ∞ B}{l : B → Delay ∞ C} →
                ((a∞ ∞>>= k) ∞>>= l) ∞≈[ i ]≈ (a∞ ∞>>= λ a → (k a >>= l))
  ≈force (∞bind-assoc a∞) = bind-assoc (force a∞)


mutual
  bind-cong-l : ∀{i A B}{a? b? : Delay ∞ A} → a? ≈[ i ]≈ b? →
                (k : A → Delay ∞ B) → (a? >>= k) ≈[ i ]≈ (b? >>= k)
  bind-cong-l (≈now a)    k = ≈refl (k a)
  bind-cong-l (≈later eq) k = ≈later (∞bind-cong-l eq k)

  ∞bind-cong-l : ∀{i A B}{a∞ b∞ : ∞Delay ∞ A} → a∞ ∞≈[ i ]≈ b∞ →
                 (k : A → Delay ∞ B) → (a∞ ∞>>= k) ∞≈[ i ]≈ (b∞ ∞>>= k)
  ≈force (∞bind-cong-l eq k) = bind-cong-l (≈force eq) k


mutual
  bind-cong-r : ∀{i A B} (a? : Delay ∞ A) {k l : A → Delay ∞ B} →
                (∀ a → (k a) ≈[ i ]≈ (l a)) → (a? >>= k) ≈[ i ]≈ (a? >>= l)
  bind-cong-r (now a)    h = h a
  bind-cong-r (later a∞) h = ≈later (∞bind-cong-r a∞ h)

  ∞bind-cong-r : ∀{i A B} (a∞ : ∞Delay ∞ A) {k l : A → Delay ∞ B} →
                 (∀ a → (k a) ≈[ i ]≈ (l a)) → (a∞ ∞>>= k) ∞≈[ i ]≈ (a∞ ∞>>= l)
  ≈force (∞bind-cong-r a∞ h) = bind-cong-r (force a∞) h


map-compose : ∀{i A B C} (a? : Delay ∞ A) {f : A → B}{g : B → C} →
              (g <$> (f <$> a?)) ≈[ i ]≈ ((g ∘ f) <$> a?)
map-compose a? = bind-assoc a?

map-cong : ∀{i A B}{a? b? : Delay ∞ A} (f : A → B) →
           a? ≈[ i ]≈ b? → (f <$> a?) ≈[ i ]≈ (f <$> b?)
map-cong f eq = bind-cong-l eq (now ∘ f)




-- 2.2.  Convergence


data _⇓_ {A : Set} : (a? : Delay ∞ A) (a : A) → Set where
  now⇓   : ∀{a}                                      → now a ⇓ a
  later⇓ : ∀{a}{a∞ : ∞Delay ∞ A} (a⇓ : force a∞ ⇓ a) → later a∞ ⇓ a

_⇓ : {A : Set} (x : Delay ∞ A) → Set
x ⇓ = ∃ λ a → x ⇓ a


map⇓ : ∀{A B}{a : A}{a? : Delay ∞ A} (f : A → B) → a? ⇓ a → (f <$> a?) ⇓ f a
map⇓ f now⇓        = now⇓
map⇓ f (later⇓ a⇓) = later⇓ (map⇓ f a⇓)

subst≈⇓ : ∀{A}{a? a?′ : Delay ∞ A}{a : A} → a? ⇓ a → a? ≈ a?′ → a?′ ⇓ a
subst≈⇓ now⇓        (≈now a)    = now⇓
subst≈⇓ (later⇓ a⇓) (≈later eq) = later⇓ (subst≈⇓ a⇓ (≈force eq))

bind⇓ : ∀{A B} (f : A → Delay ∞ B) {a? : Delay ∞ A}{a : A}{b : B} →
        a? ⇓ a → f a ⇓ b → (a? >>= f) ⇓ b
bind⇓ f now⇓        f⇓ = f⇓
bind⇓ f (later⇓ a⇓) f⇓ = later⇓ (bind⇓ f a⇓ f⇓)




-- 3.  Well-typed terms, values, and coinductive normalization


data Ty : Set where
  ⋆    : Ty
  _⇒_ : (a b : Ty) → Ty
  ⊤   : Ty
  _∧_  : (a b : Ty) → Ty
  _∨_  : (a b : Ty) → Ty
  ⊥   : Ty

infixr 5 _⇒_

data Cx : Set where
  ε   : Cx
  _,_ : (Γ : Cx) (a : Ty) → Cx

data Var : (Γ : Cx) (a : Ty) → Set where
  top : ∀{Γ a}                 → Var (Γ , a) a
  pop : ∀{Γ a b} (x : Var Γ a) → Var (Γ , b) a


data _≤_ : (Γ Δ : Cx) → Set where
  id   : ∀{Γ}     → Γ ≤ Γ
  weak : ∀{Γ Δ a} → Γ ≤ Δ → (Γ , a) ≤ Δ
  lift : ∀{Γ Δ a} → Γ ≤ Δ → (Γ , a) ≤ (Δ , a)

_∙_ : ∀{Γ Δ Δ′} (η : Γ ≤ Δ) (η′ : Δ ≤ Δ′) → Γ ≤ Δ′
id     ∙ η′      = η′
weak η ∙ η′      = weak (η ∙ η′)
lift η ∙ id      = lift η
lift η ∙ weak η′ = weak (η ∙ η′)
lift η ∙ lift η′ = lift (η ∙ η′)

η∙id : ∀{Γ Δ} (η : Γ ≤ Δ) → η ∙ id ≡ η
η∙id id       = refl
η∙id (weak η) = cong weak (η∙id η)
η∙id (lift η) = refl

id∙η : ∀{Γ Δ} (η : Γ ≤ Δ) → id ∙ η ≡ η
id∙η id       = refl
id∙η (weak η) = refl
id∙η (lift η) = cong lift (id∙η η)


weak-inv : ∀{Γ Δ a}{p : Γ ≤ Δ}{p′ : Γ ≤ Δ} → weak {a = a} p ≡ weak p′ → p ≡ p′
weak-inv refl = refl

lift-inv : ∀{Γ Δ a}{p : Γ ≤ Δ}{p′ : Γ ≤ Δ} → lift {a = a} p ≡ lift p′ → p ≡ p′
lift-inv refl = refl

infixl 4 _≟_
_≟_ : ∀{Γ Δ} → (η η′ : Γ ≤ Δ) → Dec (η ≡ η′)
id     ≟ id      = yes refl
id     ≟ weak η′ = no λ ()
id     ≟ lift η′ = no λ ()
weak η ≟ id      = no λ ()
weak η ≟ weak η′ with η ≟ η′
weak η ≟ weak .η | yes refl = yes refl
weak η ≟ weak η′ | no  η≢η′ = no (η≢η′ ∘ weak-inv)
weak η ≟ lift η′ = no λ ()
lift η ≟ id      = no λ ()
lift η ≟ weak η′ = no λ ()
lift η ≟ lift η′ with η ≟ η′
lift η ≟ lift .η | yes refl = yes refl
lift η ≟ lift η′ | no  η≢η′ = no (η≢η′ ∘ lift-inv)


compose-assoc : ∀{Γ Δ Δ′ Δ″} (η : Γ ≤ Δ) (η′ : Δ ≤ Δ′) (η″ : Δ′ ≤ Δ″) →
                (η ∙ η′) ∙ η″ ≡ η ∙ (η′ ∙ η″)
compose-assoc id       η′        η″        = refl
compose-assoc (weak η) η′        η″        = cong weak (compose-assoc η η′ η″)
compose-assoc (lift η) id        η″        = refl
compose-assoc (lift η) (weak η′) η″        = cong weak (compose-assoc η η′ η″)
compose-assoc (lift η) (lift η′) id        = refl
compose-assoc (lift η) (lift η′) (weak η″) = cong weak (compose-assoc η η′ η″)
compose-assoc (lift η) (lift η′) (lift η″) = cong lift (compose-assoc η η′ η″)


data Tm (Γ : Cx) : (a : Ty) → Set where
  var  : ∀{a}   (x : Var Γ a)                    → Tm Γ a
  lam  : ∀{a b} (t : Tm (Γ , a) b)               → Tm Γ (a ⇒ b)
  app  : ∀{a b} (t : Tm Γ (a ⇒ b)) (u : Tm Γ a) → Tm Γ b
  unit :                                             Tm Γ ⊤
  pair : ∀{a b} (t : Tm Γ a) (u : Tm Γ b)        → Tm Γ (a ∧ b)
  fst  : ∀{a b} (t : Tm Γ (a ∧ b))               → Tm Γ a
  snd  : ∀{a b} (t : Tm Γ (a ∧ b))               → Tm Γ b
  inl  : ∀{a b} (t : Tm Γ a)                     → Tm Γ (a ∨ b)
  inr  : ∀{a b} (t : Tm Γ b)                     → Tm Γ (a ∨ b)
  when : ∀{a b c} (t : Tm Γ (a ∨ b)) (u : Tm (Γ , a) c) (u′ : Tm (Γ , b) c) → Tm Γ c
  loop : ∀{a}   (t : Tm Γ ⊥)                    → Tm Γ a

data Ne (Ξ : Cx → Ty → Set) (Γ : Cx) : Ty → Set where
  var  : ∀{a}   → Var Γ a                  → Ne Ξ Γ a
  app  : ∀{a b} → Ne Ξ Γ (a ⇒ b) → Ξ Γ a → Ne Ξ Γ b
  fst  : ∀{a b} → Ne Ξ Γ (a ∧ b)           → Ne Ξ Γ a
  snd  : ∀{a b} → Ne Ξ Γ (a ∧ b)           → Ne Ξ Γ b
  when : ∀{a b c} → Ne Ξ Γ (a ∨ b) → Tm (Γ , a) c → Tm (Γ , b) c → Ne Ξ Γ c
  loop : ∀{a}   → Ne Ξ Γ ⊥                → Ne Ξ Γ a

data Nf (Γ : Cx) : (a : Ty) → Set where
  ne   : (m : Ne Nf Γ ⋆)                   → Nf Γ ⋆
  lam  : ∀{a b} (n : Nf (Γ , a) b)        → Nf Γ (a ⇒ b)
  unit :                                      Nf Γ ⊤
  pair : ∀{a b} (n : Nf Γ a) (m : Nf Γ b) → Nf Γ (a ∧ b)
  inl  : ∀{a b} (n : Nf Γ a)              → Nf Γ (a ∨ b)
  inr  : ∀{a b} (n : Nf Γ b)              → Nf Γ (a ∨ b)

mutual
  data Val (Δ : Cx) : (a : Ty) → Set where
    ne   : ∀{a}     (w : Ne Val Δ a)                 → Val Δ a
    lam  : ∀{Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) → Val Δ (a ⇒ b)
    unit :                                               Val Δ ⊤
    pair : ∀{a b}   (v : Val Δ a) (w : Val Δ b)      → Val Δ (a ∧ b)
    inl  : ∀{a b}   (v : Val Δ a)                    → Val Δ (a ∨ b)
    inr  : ∀{a b}   (v : Val Δ b)                    → Val Δ (a ∨ b)

  data Env (Δ : Cx) : (Γ : Cx) → Set where
    ε   : Env Δ ε
    _,_ : ∀{Γ a} (ρ : Env Δ Γ) (v : Val Δ a) → Env Δ (Γ , a)

lookup : ∀ {Γ Δ a} → Var Γ a → Env Δ Γ → Val Δ a
lookup top     (ρ , v) = v
lookup (pop x) (ρ , v) = lookup x ρ


mutual
  eval : ∀{i Γ Δ b} → Tm Γ b → Env Δ Γ → Delay i (Val Δ b)
  eval (var x)    ρ = now (lookup x ρ)
  eval (lam t)    ρ = now (lam t ρ)
  eval (app t u)  ρ = f ← eval t ρ ⁏
                      v ← eval u ρ ⁏
                      reduce-app f v
  eval unit       ρ = now unit
  eval (pair t u) ρ = v ← eval t ρ ⁏
                      w ← eval u ρ ⁏
                      now (pair v w)
  eval (fst t)    ρ = v ← eval t ρ ⁏
                      reduce-fst v
  eval (snd t)    ρ = v ← eval t ρ ⁏
                      reduce-snd v
  eval (inl t)    ρ = v ← eval t ρ ⁏
                      now (inl v)
  eval (inr t)    ρ = v ← eval t ρ ⁏
                      now (inr v)
  eval (when t u u′) ρ = v ← eval t ρ ⁏
                         reduce-when v u u′ ρ
  eval (loop t)   ρ = v ← eval t ρ ⁏
                      reduce-loop v

  reduce-app : ∀{i Δ a b} → Val Δ (a ⇒ b) → Val Δ a → Delay i (Val Δ b)
  reduce-app (ne w)    v = now (ne (app w v))
  reduce-app (lam t ρ) v = later (∞subst t ρ v)

  reduce-fst : ∀{i Δ a b} → Val Δ (a ∧ b) → Delay i (Val Δ a)
  reduce-fst (ne w)     = now (ne (fst w))
  reduce-fst (pair t u) = now t

  reduce-snd : ∀{i Δ a b} → Val Δ (a ∧ b) → Delay i (Val Δ b)
  reduce-snd (ne w)     = now (ne (snd w))
  reduce-snd (pair t u) = now u

  -- TODO: unfinished
  reduce-when : ∀{i Γ Δ a b c} → Val Δ (a ∨ b) → Tm (Γ , a) c → Tm (Γ , b) c → Env Δ Γ → Delay i (Val Δ c)
  reduce-when (ne w)  u u′ ρ = now (ne (when w {!u!} {!u′!}))
  reduce-when (inl t) u u′ ρ = later (∞subst u ρ t)
  reduce-when (inr t) u u′ ρ = later (∞subst u′ ρ t)

  reduce-loop : ∀{i Δ a} → Val Δ ⊥ → Delay i (Val Δ a)
  reduce-loop (ne w) = now (ne (loop w))

  ∞subst : ∀{i Γ Δ a b} → Tm (Γ , a) b → Env Δ Γ → Val Δ a → ∞Delay i (Val Δ b)
  force (∞subst t ρ a) = eval t (ρ , a)


mutual
  tm≤ : ∀{Γ Δ a} → Γ ≤ Δ → Tm Δ a → Tm Γ a
  tm≤ η (var x)    = var (var≤ η x)
  tm≤ η (lam t)    = lam (tm≤ (lift η) t)
  tm≤ η (app t u)  = app (tm≤ η t) (tm≤ η u)
  tm≤ η unit       = unit
  tm≤ η (pair t u) = pair (tm≤ η t) (tm≤ η u)
  tm≤ η (fst t)    = fst (tm≤ η t)
  tm≤ η (snd t)    = snd (tm≤ η t)
  tm≤ η (inl t)    = inl (tm≤ η t)
  tm≤ η (inr t)    = inr (tm≤ η t)
  tm≤ η (when t u u′) = when (tm≤ η t) (tm≤ (lift η) u) (tm≤ (lift η) u′)
  tm≤ η (loop t)   = loop (tm≤ η t)

  var≤ : ∀{Γ Δ a} → Γ ≤ Δ → Var Δ a → Var Γ a
  var≤ id       x       = x
  var≤ (weak η) x       = pop (var≤ η x)
  var≤ (lift η) top     = top
  var≤ (lift η) (pop x) = pop (var≤ η x)

  val≤ : ∀{Γ Δ a} → Γ ≤ Δ → Val Δ a → Val Γ a
  val≤ η (ne w)     = ne (nev≤ η w)
  val≤ η (lam t ρ)  = lam t (env≤ η ρ)
  val≤ η unit       = unit
  val≤ η (pair t u) = pair (val≤ η t) (val≤ η u)
  val≤ η (inl t)    = inl (val≤ η t)
  val≤ η (inr t)    = inr (val≤ η t)

  env≤ : ∀{Γ Δ E} → Γ ≤ Δ → Env Δ E → Env Γ E
  env≤ η ε       = ε
  env≤ η (ρ , v) = env≤ η ρ , val≤ η v

  nev≤ : ∀{Γ Δ a} → Γ ≤ Δ → Ne Val Δ a → Ne Val Γ a
  nev≤ η (var x)   = var (var≤ η x)
  nev≤ η (app w v) = app (nev≤ η w) (val≤ η v)
  nev≤ η (fst w)   = fst (nev≤ η w)
  nev≤ η (snd w)   = snd (nev≤ η w)
  nev≤ η (when w v v′) = when (nev≤ η w) (tm≤ (lift η) v) (tm≤ (lift η) v′)
  nev≤ η (loop w)  = loop (nev≤ η w)

  nf≤ : ∀{Γ Δ a} → Γ ≤ Δ → Nf Δ a → Nf Γ a
  nf≤ η (ne m)     = ne (nen≤ η m)
  nf≤ η (lam n)    = lam (nf≤ (lift η) n)
  nf≤ η unit       = unit
  nf≤ η (pair n m) = pair (nf≤ η n) (nf≤ η m)
  nf≤ η (inl n)    = inl (nf≤ η n)
  nf≤ η (inr n)    = inr (nf≤ η n)
--  nf≤ η (loop n)   = loop (nf≤ η n)

  nen≤ : ∀{Γ Δ a} → Γ ≤ Δ → Ne Nf Δ a → Ne Nf Γ a
  nen≤ η (var x)   = var (var≤ η x)
  nen≤ η (app m n) = app (nen≤ η m) (nf≤ η n)
  nen≤ η (fst m)   = fst (nen≤ η m)
  nen≤ η (snd m)   = snd (nen≤ η m)
  nen≤ η (when m n n′) = when (nen≤ η m) (tm≤ (lift η) n) (tm≤ (lift η) n′)
  nen≤ η (loop m)  = loop (nen≤ η m)

wk : ∀{Γ a} → (Γ , a) ≤ Γ
wk = weak id

weakVal : ∀{Δ a c} → Val Δ c → Val (Δ , a) c
weakVal = val≤ wk


-- TODO: unfinished
mutual
  readback : ∀{i Γ a} → Val Γ a → Delay i (Nf Γ a)
  readback {a = ⋆}      (ne w) = m ← nereadback w ⁏
                                 now (ne m)
  readback {a = _ ⇒ _} v      = m ← later (∞expand-lam v) ⁏
                                 now (lam m)
  readback {a = ⊤}     v      = now unit
  readback {a = _ ∧ _}  v      = p ← later (∞expand-pair v) ⁏
                                 now (pair (proj₁ p) (proj₂ p))
  readback {a = _ ∨ _}  v      = {!!}
  readback {a = ⊥}     v      = later ∞never

  ∞expand-lam : ∀{i Γ a b} → Val Γ (a ⇒ b) → ∞Delay i (Nf (Γ , a) b)
  force (∞expand-lam v) = b ← reduce-app (weakVal v) (ne (var top)) ⁏
                          readback b

  ∞expand-pair : ∀{i Γ a b} → Val Γ (a ∧ b) → ∞Delay i (Nf Γ a × Nf Γ b)
  force (∞expand-pair v) = a ← reduce-fst v ⁏
                           b ← reduce-snd v ⁏
                           x ← readback a ⁏
                           y ← readback b ⁏
                           now (x , y)

  ∞expand-when : ∀{i Γ a b c} → Val Γ (a ∨ b) → ∞Delay i (Nf Γ (a ∨ b) × Nf (Γ , a) c × Nf (Γ , b) c)
  ∞expand-when (ne w)  = {!!}
  ∞expand-when (inl v) = {!!}
  ∞expand-when (inr v) = {!!}

  ∞never : ∀{i Γ} → ∞Delay i (Nf Γ ⊥)
  force ∞never = later ∞never

  nereadback : ∀{i Γ a} → Ne Val Γ a → Delay i (Ne Nf Γ a)
  nereadback (var x)   = now (var x)
  nereadback (app w v) = m ← nereadback w ⁏
                         n ← readback v ⁏
                         now (app m n)
  nereadback (fst w)   = m ← nereadback w ⁏
                         now (fst m)
  nereadback (snd w)   = m ← nereadback w ⁏
                         now (snd m)
  nereadback (when w v v′) = {!!}
  nereadback (loop w)  = m ← nereadback w ⁏
                         now (loop m)


ide : (Γ : Cx) → Env Γ Γ
ide ε       = ε
ide (Γ , a) = env≤ wk (ide Γ) , ne (var top)


nf : ∀ {Γ a} (t : Tm Γ a) → Delay ∞ (Nf Γ a)
nf {Γ} t = v ← eval t (ide Γ) ⁏
           readback v




extract : ∀{A} (n : ℕ) → Delay ∞ A → Maybe A
extract n       (now a)    = just a
extract zero    (later a∞) = nothing
extract (suc n) (later a∞) = extract n (force a∞)

I : ∀{Γ a} → Tm Γ (a ⇒ a)
I = lam (var top)
-- (readback
--  (ne (var top))
--  >>= (λ m → now (lam m)))

K : ∀{Γ a b} → Tm Γ (a ⇒ b ⇒ a)
K = lam (lam (var (pop top)))
-- ((readback
--   (ne (var (pop top)))
--   >>= (λ m → now (lam m)))
--  >>= (λ m → now (lam m)))

S : ∀{Γ a b c} → Tm Γ ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
S = lam (lam (lam (app (app (var (pop (pop top))) (var top)) (app (var (pop top)) (var top)))))
-- (((readback
--    (ne (app (app (var (pop (pop top))) (ne (var top)))
--             (ne (app (var (pop top)) (ne (var top))))))
--    >>= (λ m → now (lam m)))
--   >>= (λ m → now (lam m)))
--  >>= (λ m → now (lam m)))

II : ∀ {Γ a} → Tm Γ (a ⇒ a)
II = app I I
-- (readback
--  (ne (var top))
--  >>= (λ m → now (lam m)))

SKK : ∀ {Γ a} → Tm Γ (a ⇒ a)
SKK = app (app S K) (K {b = ⋆})
-- (readback
--  (ne (var top))
--  >>= (λ m → now (lam m)))

SKSK : ∀ {Γ a b} → Tm Γ (a ⇒ b ⇒ a)
SKSK = app (app (app S K) S) K
-- ((readback
--   (ne (var (pop top)))
--   >>= (λ m → now (lam m)))
--  >>= (λ m → now (lam m)))

flip : ∀{Γ a b c} → Tm Γ ((a ⇒ b ⇒ c) ⇒ b ⇒ a ⇒ c)
flip = lam (lam (lam (app (app (var (pop (pop top))) (var top)) (var (pop top)))))
-- (((readback
--    (ne
--     (app (app (var (pop (pop top))) (ne (var top)))
--      (ne (var (pop top)))))
--    >>= (λ m → now (lam m)))
--   >>= (λ m → now (lam m)))
--  >>= (λ m → now (lam m)))

xfst : ∀{Γ a b} → Tm Γ (a ∧ b ⇒ a)
xfst = lam (fst (var top))
-- (readback
--  (ne (fst (var top)))
--  >>= (λ m → now (lam m)))

xsnd : ∀{Γ a b} → Tm Γ (a ∧ b ⇒ b)
xsnd = lam (snd (var top))
-- (readback
--  (ne (snd (var top)))
--  >>= (λ m → now (lam m)))

xpair : ∀{Γ a b} → Tm Γ (a ⇒ b ⇒ a ∧ b)
xpair = lam (lam (pair (var (pop top)) (var top)))
-- ((((readback (ne (var (pop top))) >>=
--     (λ x → readback (ne (var top)) >>= (λ y → now (x , y))))
--    >>= (λ p → now (pair (proj₁ p) (proj₂ p))))
--   >>= (λ m → now (lam m)))
--  >>= (λ m → now (lam m)))
