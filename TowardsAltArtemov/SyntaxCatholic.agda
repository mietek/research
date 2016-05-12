module TowardsAltArtemov.SyntaxCatholic where

open import Data.Nat using (ℕ ; zero ; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong₂)
open import Relation.Nullary using (Dec ; yes ; no)


-- PARTIAL ORDERS
-- A partial order on the natural numbers is a forgetful projection of
-- order-preserving embeddings.
data _≥_ : ℕ → ℕ → Set where
  id   : ∀ {n}              → n ≥ n
  weak : ∀ {n′ n} → n′ ≥ n → suc n′ ≥ n
  lift : ∀ {n′ n} → n′ ≥ n → suc n′ ≥ suc n

-- Partial orders are transitive.
_○_ : ∀ {n″ n′ n} (p′ : n″ ≥ n′) (p : n′ ≥ n) → n″ ≥ n
id      ○ p      = p
weak p′ ○ p      = weak (p′ ○ p)
lift p′ ○ id     = lift p′
lift p′ ○ weak p = weak (p′ ○ p)
lift p′ ○ lift p = lift (p′ ○ p)

°to : ∀ n → n ≥ zero
°to zero    = id
°to (suc n) = weak (°to n)

°str : ∀ {n n′} → n′ ≥ suc n → n′ ≥ n
°str id       = weak id
°str (weak p) = weak (°str p)
°str (lift p) = weak p

°low : ∀ {n n′} → suc n′ ≥ suc n → n′ ≥ n
°low id       = id
°low (weak p) = °str p
°low (lift p) = p


-- VARIABLE REPRESENTATIONS
-- The representation of a variable is a forgetful projection of typed de Bruijn
-- indices; a finite natural number; an encoding of a reference to an assumption.
-- n is the size of the smallest context in which the variable is valid.
data °Var : ℕ → Set where
  top : ∀ {n}           → °Var (suc n)
  pop : ∀ {n} → °Var n → °Var (suc n)

-- Any variable which is valid in a certain context is valid in a greater context.
↑°var : ∀ {n′ n} (p : n′ ≥ n) → °Var n → °Var n′
↑°var id       x       = x
↑°var (weak p) x       = pop (↑°var p x)
↑°var (lift p) top     = top
↑°var (lift p) (pop x) = pop (↑°var p x)

-- No variables are valid in the empty context.
↥°var : ∀ n → °Var 0 → °Var n
↥°var n ()


-- TERM REPRESENTATIONS
-- The representation of a term is a forgetful projection of typed terms; an
-- untyped term; an encoding of a program.  n is the size of the smallest
-- context in which all variables that could appear in the term are valid, and
-- so, in which the term is valid.  When n is 0, the term is closed; valid under
-- no assumptions.
data °Tm (n : ℕ) : Set where
  var : °Var n         → °Tm n
  lam : °Tm (suc n)    → °Tm n
  app : °Tm n → °Tm n → °Tm n

-- Any term which is valid in a certain context is valid in a greater context.
↑°tm : ∀ {n′ n} (p : n′ ≥ n) → °Tm n → °Tm n′
↑°tm p (var x)   = var (↑°var p x)
↑°tm p (lam t)   = lam (↑°tm (lift p) t)
↑°tm p (app t u) = app (↑°tm p t) (↑°tm p u)

-- Any term which is valid in the empty context is valid in any context.
↥°tm : ∀ n → °Tm 0 → °Tm n
↥°tm n = ↑°tm (°to n)


-- TYPES
-- A type is a proposition.  n is the size of the smallest context in which all
-- term representations that could appear in the type are valid, and so, in
-- which the type is valid.  When n is 0, the type is closed; valid under no
-- assumptions.
data Ty (n : ℕ) : Set where
  ★   : Ty n
  _⊃_ : Ty n → Ty n → Ty n

infixr 5 _⊃_

-- Any type which is valid in a certain context is valid in a greater context.
↑ty : ∀ {n′ n} (p : n′ ≥ n) → Ty n → Ty n′
↑ty p ★       = ★
↑ty p (A ⊃ B) = ↑ty p A ⊃ ↑ty p B

-- Any type which is valid in the empty context is valid in any context.
↥ty : ∀ n → Ty 0 → Ty n
↥ty n = ↑ty (°to n)

↑ty-dist-≥-≥ : ∀ {n″ n′ n} (p′ : n″ ≥ n′) (p : n′ ≥ n) (A : Ty n) →
               ↑ty (p′ ○ p) A ≡ ↑ty p′ (↑ty p A)
↑ty-dist-≥-≥ p′ p ★       = refl
↑ty-dist-≥-≥ p′ p (A ⊃ B) = cong₂ _⊃_ (↑ty-dist-≥-≥ p′ p A) (↑ty-dist-≥-≥ p′ p B)

↥ty-dist-≥ : ∀ {n′ n} (p : n′ ≥ n) (A : Ty 0) →
             ↥ty n′ A ≡ ↑ty p (↥ty n A)
↥ty-dist-≥ {n = n} p = ↑ty-dist-≥-≥ p (°to n)

↑ty-pres-★ : ∀ {n′ n} {p : n′ ≥ n} {A : Ty n} → A ≡ ★ → ↑ty p A ≡ ★
↑ty-pres-★ refl = refl

↑ty-pres-⊃ : ∀ {n′ n} {p : n′ ≥ n} {A B A⊃B : Ty n} → A⊃B ≡ A ⊃ B → ↑ty p A⊃B ≡ ↑ty p A ⊃ ↑ty p B
↑ty-pres-⊃ refl = refl

⊃⁻ᴬ : ∀ {n} {A A′ B B′ : Ty n} → (A ⊃ B) ≡ (A′ ⊃ B′) → A ≡ A′
⊃⁻ᴬ refl = refl

⊃⁻ᴮ : ∀ {n} {A A′ B B′ : Ty n} → (A ⊃ B) ≡ (A′ ⊃ B′) → B ≡ B′
⊃⁻ᴮ refl = refl

_≟_ : ∀ {g} → (A A′ : Ty g) → Dec (A ≡ A′)
★       ≟ ★         = yes refl
★       ≟ (A ⊃ B)   = no λ ()
(A ⊃ B) ≟ ★         = no λ ()
(A ⊃ B) ≟ (A′ ⊃ B′) with A ≟ A′ | B ≟ B′
(A ⊃ B) ≟ (.A ⊃ .B) | yes refl | yes refl = yes refl
...                 | no  A≢A′ | _        = no (A≢A′ ∘ ⊃⁻ᴬ)
...                 | _        | no  B≢B′ = no (B≢B′ ∘ ⊃⁻ᴮ)


-- CONTEXTS
-- A context is a list of types; a collection of assumptions.  Only types which
-- are closed can be taken as assumptions.
-- An alternative definition could allow assuming types which are open, but
-- which only refer to types that have been assumed previously; i.e.:
--       _,_ : (Γ : Cx) → Ty ℕ⌊ Γ ⌋ → Cx
-- This appears to introduce too much dependency; indeed, a related definition
-- is given by both McBride and Chapman, separately, as part of their
-- formalisations of dependent types:
--       _,_ : (Γ : Cx) → Ty Γ → Cx
data Cx : Set where
  ∅   : Cx
  _,_ : Cx → Ty 0 → Cx

-- The forgetful projection of a context is its size; a natural number.
ⁿ⌊_⌋ : (Γ : Cx) → ℕ
ⁿ⌊ ∅ ⌋     = zero
ⁿ⌊ Γ , A ⌋ = suc ⁿ⌊ Γ ⌋


-- ORDER-PRESERVING EMBEDDINGS (OPEs)
data _⊇_ : Cx → Cx → Set where
  id   : ∀ {Γ}                         → Γ ⊇ Γ
  weak : ∀ {Γ Γ′} (A : Ty 0) → Γ′ ⊇ Γ → (Γ′ , A) ⊇ Γ
  lift : ∀ {Γ Γ′} (A : Ty 0) → Γ′ ⊇ Γ → (Γ′ , A) ⊇ (Γ , A)

-- The forgetful projection of an OPE is a partial order.
ᵖ⌊_⌋ : ∀ {Γ′ Γ} (η : Γ ⊇ Γ′) → ⁿ⌊ Γ ⌋ ≥ ⁿ⌊ Γ′ ⌋
ᵖ⌊ id ⌋       = id
ᵖ⌊ weak A η ⌋ = weak ᵖ⌊ η ⌋
ᵖ⌊ lift A η ⌋ = lift ᵖ⌊ η ⌋

to : ∀ Γ → Γ ⊇ ∅
to ∅       = id
to (Γ , A) = weak A (to Γ)

str : ∀ {Γ′ Γ} (A : Ty 0) → Γ′ ⊇ (Γ , A) → Γ′ ⊇ Γ
str A id          = weak A id
str A (weak B  η) = weak B (str A η)
str A (lift .A η) = weak A η

low : ∀ {Γ′ Γ} (A : Ty 0) → (Γ′ , A) ⊇ (Γ , A) → Γ′ ⊇ Γ
low A id          = id
low A (weak .A η) = str A η
low A (lift .A η) = η

↑ty-dist-≥-⊇ : ∀ {Δ″ Δ′ Δ} (p′ : ⁿ⌊ Δ″ ⌋ ≥ ⁿ⌊ Δ′ ⌋) (η : Δ′ ⊇ Δ) (A : Ty ⁿ⌊ Δ ⌋) →
               ↑ty (p′ ○ ᵖ⌊ η ⌋) A ≡ ↑ty p′ (↑ty ᵖ⌊ η ⌋ A)
↑ty-dist-≥-⊇ p′ η = ↑ty-dist-≥-≥ p′ ᵖ⌊ η ⌋

↑ty-dist-⊇-≥ : ∀ {Δ″ Δ′ Δ} (η′ : Δ″ ⊇ Δ′) (p : ⁿ⌊ Δ′ ⌋ ≥ ⁿ⌊ Δ ⌋) (A : Ty ⁿ⌊ Δ ⌋) →
               ↑ty (ᵖ⌊ η′ ⌋ ○ p) A ≡ ↑ty ᵖ⌊ η′ ⌋ (↑ty p A)
↑ty-dist-⊇-≥ η′ p = ↑ty-dist-≥-≥ ᵖ⌊ η′ ⌋ p

↑ty-dist-⊇-⊇ : ∀ {Δ″ Δ′ Δ} (η′ : Δ″ ⊇ Δ′) (η : Δ′ ⊇ Δ) (A : Ty ⁿ⌊ Δ ⌋) →
               ↑ty (ᵖ⌊ η′ ⌋ ○ ᵖ⌊ η ⌋) A ≡ ↑ty ᵖ⌊ η′ ⌋ (↑ty ᵖ⌊ η ⌋ A)
↑ty-dist-⊇-⊇ η′ η = ↑ty-dist-≥-≥ ᵖ⌊ η′ ⌋ ᵖ⌊ η ⌋

↥ty-dist-⊇ : ∀ {Δ′ Δ} (η : Δ′ ⊇ Δ) (A : Ty 0) →
                ↥ty ⁿ⌊ Δ′ ⌋ A ≡ ↑ty ᵖ⌊ η ⌋ (↥ty ⁿ⌊ Δ ⌋ A)
↥ty-dist-⊇ η = ↥ty-dist-≥ ᵖ⌊ η ⌋


-- VARIABLES
-- A variable is a typed de Bruijn index; a reference to an assumption.  Γ is
-- the smallest context in which the variable is valid.
data Var : Cx → Ty 0 → Set where
  top : ∀ {Γ} (A : Ty 0)                       → Var (Γ , A) A
  pop : ∀ {Γ} {A : Ty 0} (B : Ty 0) → Var Γ A → Var (Γ , B) A

-- Any variable which is valid in a certain context is valid in a greater context.
↑var : ∀ {Γ′ Γ} {A : Ty 0} (η : Γ′ ⊇ Γ) → Var Γ A → Var Γ′ A
↑var id         x          = x
↑var (weak B η) x          = pop B (↑var η x)
↑var (lift A η) (top .A)   = top A
↑var (lift B η) (pop .B x) = pop B (↑var η x)

-- No variables are valid in the empty context.
↥var : ∀ Γ {A : Ty 0} → Var ∅ A → Var Γ A
↥var Γ ()


-- TERMS
-- A term is a program.  Γ is the smallest context in which the term is valid.
data Tm (Γ : Cx) : Ty ⁿ⌊ Γ ⌋ → Set where
  var : ∀ {A : Ty 0} →
        Var Γ A →
        {A′ : Ty ⁿ⌊ Γ ⌋} {{_ : A′ ≡ ↥ty ⁿ⌊ Γ ⌋ A}} →
        Tm Γ A′
  lam : ∀ (A : Ty 0) {B : Ty 0} →
        Tm (Γ , A) (↥ty ⁿ⌊ Γ , A ⌋ B) →
        {A⊃B′ : Ty ⁿ⌊ Γ ⌋} {{_ : A⊃B′ ≡ ↥ty ⁿ⌊ Γ ⌋ (A ⊃ B)}} →
        Tm Γ A⊃B′
  app : ∀ {A B : Ty 0} →
        Tm Γ (↥ty ⁿ⌊ Γ ⌋ (A ⊃ B)) → Tm Γ (↥ty ⁿ⌊ Γ ⌋ A) →
        {B′ : Ty ⁿ⌊ Γ ⌋} {{_ : B′ ≡ ↥ty ⁿ⌊ Γ ⌋ B}} →
        Tm Γ B′

≪tm : ∀ {Δ′ Δ} {A : Ty 0} (η : Δ′ ⊇ Δ) →
       Tm Δ′ (↑ty ᵖ⌊ η ⌋ (↥ty ⁿ⌊ Δ ⌋ A)) →
       Tm Δ′ (↥ty ⁿ⌊ Δ′ ⌋ A)
≪tm {A = A} η x rewrite ↥ty-dist-⊇ η A = x

≫tm : ∀ {Δ′ Δ} {A : Ty 0} (η : Δ′ ⊇ Δ) →
      Tm Δ′ (↥ty ⁿ⌊ Δ′ ⌋ A) →
      Tm Δ′ (↑ty ᵖ⌊ η ⌋ (↥ty ⁿ⌊ Δ ⌋ A))
≫tm {A = A} η x rewrite ↥ty-dist-⊇ η A = x

-- Any term which is valid in a certain context is valid in a greater context.
↑tm : ∀ {Γ′ Γ} {A : Ty ⁿ⌊ Γ ⌋} (η : Γ′ ⊇ Γ) → Tm Γ A → Tm Γ′ (↑ty ᵖ⌊ η ⌋ A)
↑tm η (var x {{refl}})   = ≫tm η (var (↑var η x))
↑tm η (lam A t {{refl}}) = ≫tm η (lam A (≪tm (lift A η) (↑tm (lift A η) t)))
↑tm η (app t u {{refl}}) = ≫tm η (app (≪tm η (↑tm η t)) (≪tm η (↑tm η u)))

-- Any term which is valid in the empty context is valid in any context.
↥tm : ∀ Γ {A : Ty 0} → Tm ∅ A → Tm Γ (↥ty ⁿ⌊ Γ ⌋ A)
↥tm Γ = ↑tm (to Γ)


-- GENERALISED NEUTRAL TERMS
data Ne (Ξ : (Δ : Cx) → Ty ⁿ⌊ Δ ⌋ → Set) (Γ : Cx) : Ty ⁿ⌊ Γ ⌋ → Set where
  var : ∀ {A : Ty 0} →
        Var Γ A →
        {A′ : Ty ⁿ⌊ Γ ⌋} {{_ : A′ ≡ ↥ty ⁿ⌊ Γ ⌋ A}} →
        Ne Ξ Γ A′
  app : ∀ {A B : Ty 0} →
        Ne Ξ Γ (↥ty ⁿ⌊ Γ ⌋ (A ⊃ B)) → Ξ Γ (↥ty ⁿ⌊ Γ ⌋ A) →
        {B′ : Ty ⁿ⌊ Γ ⌋} {{_ : B′ ≡ ↥ty ⁿ⌊ Γ ⌋ B}} →
        Ne Ξ Γ B′

-- NORMAL FORMS
data Nf (Δ : Cx) : Ty ⁿ⌊ Δ ⌋ → Set where
  ne  : Ne Nf Δ ★ → Nf Δ ★
  lam : ∀ (A : Ty 0) {B : Ty 0} →
        Nf (Δ , A) (↥ty ⁿ⌊ Δ , A ⌋ B) →
        {A⊃B′ : Ty ⁿ⌊ Δ ⌋} {{_ : A⊃B′ ≡ ↥ty ⁿ⌊ Δ ⌋ (A ⊃ B)}} →
        Nf Δ A⊃B′

mutual
  -- VALUES (WEAK HEAD NORMAL FORMS)
  data Val (Δ : Cx) : Ty ⁿ⌊ Δ ⌋ → Set where
    ne  : ∀ {A : Ty ⁿ⌊ Δ ⌋} → Ne Val Δ A → Val Δ A
    lam : ∀ {Γ} (A : Ty 0) {B : Ty 0} →
          Tm (Γ , A) (↥ty ⁿ⌊ Γ , A ⌋ B) → Env Δ Γ →
          {A⊃B′ : Ty ⁿ⌊ Δ ⌋} {{_ : A⊃B′ ≡ ↥ty ⁿ⌊ Δ ⌋ (A ⊃ B)}} →
          Val Δ A⊃B′

  -- ENVIRONMENTS
  data Env (Δ : Cx) : Cx → Set where
    ∅   : Env Δ ∅
    _,_ : ∀ {Γ} {A : Ty 0} →
          Env Δ Γ → Val Δ (↥ty ⁿ⌊ Δ ⌋ A) →
          Env Δ (Γ , A)


≪nen : ∀ {Δ′ Δ} {A : Ty 0} (η : Δ′ ⊇ Δ) →
       Ne Nf Δ′ (↑ty ᵖ⌊ η ⌋ (↥ty ⁿ⌊ Δ ⌋ A)) →
       Ne Nf Δ′ (↥ty ⁿ⌊ Δ′ ⌋ A)
≪nen {A = A} η x rewrite ↥ty-dist-⊇ η A = x

≫nen : ∀ {Δ′ Δ} {A : Ty 0} (η : Δ′ ⊇ Δ) →
       Ne Nf Δ′ (↥ty ⁿ⌊ Δ′ ⌋ A) →
       Ne Nf Δ′ (↑ty ᵖ⌊ η ⌋ (↥ty ⁿ⌊ Δ ⌋ A))
≫nen {A = A} η x rewrite ↥ty-dist-⊇ η A = x

≪nev : ∀ {Δ′ Δ} {A : Ty 0} (η : Δ′ ⊇ Δ) →
       Ne Val Δ′ (↑ty ᵖ⌊ η ⌋ (↥ty ⁿ⌊ Δ ⌋ A)) →
       Ne Val Δ′ (↥ty ⁿ⌊ Δ′ ⌋ A)
≪nev {A = A} η x rewrite ↥ty-dist-⊇ η A = x

≫nev : ∀ {Δ′ Δ} {A : Ty 0} (η : Δ′ ⊇ Δ) →
       Ne Val Δ′ (↥ty ⁿ⌊ Δ′ ⌋ A) →
       Ne Val Δ′ (↑ty ᵖ⌊ η ⌋ (↥ty ⁿ⌊ Δ ⌋ A))
≫nev {A = A} η x rewrite ↥ty-dist-⊇ η A = x

≪nf : ∀ {Δ′ Δ} {A : Ty 0} (η : Δ′ ⊇ Δ) →
      Nf Δ′ (↑ty ᵖ⌊ η ⌋ (↥ty ⁿ⌊ Δ ⌋ A)) →
      Nf Δ′ (↥ty ⁿ⌊ Δ′ ⌋ A)
≪nf {A = A} η x rewrite ↥ty-dist-⊇ η A = x

≫nf : ∀ {Δ′ Δ} {A : Ty 0} (η : Δ′ ⊇ Δ) →
      Nf Δ′ (↥ty ⁿ⌊ Δ′ ⌋ A) →
      Nf Δ′ (↑ty ᵖ⌊ η ⌋ (↥ty ⁿ⌊ Δ ⌋ A))
≫nf {A = A} η x rewrite ↥ty-dist-⊇ η A = x

≪val : ∀ {Δ′ Δ} {A : Ty 0} (η : Δ′ ⊇ Δ) →
       Val Δ′ (↑ty ᵖ⌊ η ⌋ (↥ty ⁿ⌊ Δ ⌋ A)) →
       Val Δ′ (↥ty ⁿ⌊ Δ′ ⌋ A)
≪val {A = A} η x rewrite ↥ty-dist-⊇ η A = x

≫val : ∀ {Δ′ Δ} {A : Ty 0} (η : Δ′ ⊇ Δ) →
       Val Δ′ (↥ty ⁿ⌊ Δ′ ⌋ A) →
       Val Δ′ (↑ty ᵖ⌊ η ⌋ (↥ty ⁿ⌊ Δ ⌋ A))
≫val {A = A} η x rewrite ↥ty-dist-⊇ η A = x


-- Anything which is valid in a certain context is valid in a greater context.
mutual
  ↑nen : ∀ {Δ′ Δ} {A : Ty ⁿ⌊ Δ ⌋} (η : Δ′ ⊇ Δ) →
         Ne Nf Δ A →
         Ne Nf Δ′ (↑ty ᵖ⌊ η ⌋ A)
  ↑nen η (var x {{refl}})   = ≫nen η (var (↑var η x))
  ↑nen η (app t u {{refl}}) = ≫nen η (app (≪nen η (↑nen η t)) (≪nf η (↑nf η u)))

  ↑nev : ∀ {Δ′ Δ} {A : Ty ⁿ⌊ Δ ⌋} (η : Δ′ ⊇ Δ) →
         Ne Val Δ A →
         Ne Val Δ′ (↑ty ᵖ⌊ η ⌋ A)
  ↑nev η (var x {{refl}})   = ≫nev η (var (↑var η x))
  ↑nev η (app t u {{refl}}) = ≫nev η (app (≪nev η (↑nev η t)) (≪val η (↑val η u)))

  ↑nf : ∀ {Δ′ Δ} {A : Ty ⁿ⌊ Δ ⌋} (η : Δ′ ⊇ Δ) →
        Nf Δ A →
        Nf Δ′ (↑ty ᵖ⌊ η ⌋ A)
  ↑nf η (ne n)             = ne (↑nen η n)
  ↑nf η (lam A t {{refl}}) = ≫nf η (lam A (≪nf (lift A η) (↑nf (lift A η) t)))

  ↑val : ∀ {Δ′ Δ} {A : Ty ⁿ⌊ Δ ⌋} (η : Δ′ ⊇ Δ) →
         Val Δ A →
         Val Δ′ (↑ty ᵖ⌊ η ⌋ A)
  ↑val η (ne n)               = ne (↑nev η n)
  ↑val η (lam A t γ {{refl}}) = ≫val η (lam A t (↑env η γ))

  ↑env : ∀ {Δ′ Δ Γ} (η : Δ′ ⊇ Δ) →
         Env Δ Γ →
         Env Δ′ Γ
  ↑env η ∅       = ∅
  ↑env η (γ , v) = (↑env η γ , ≪val η (↑val η v))


-- Anything which is valid in the empty context is valid in any context.
↥nen : ∀ Δ {A : Ty 0} → Ne Nf ∅ A → Ne Nf Δ (↥ty ⁿ⌊ Δ ⌋ A)
↥nen Δ = ↑nen (to Δ)

↥nev : ∀ Δ {A : Ty 0} → Ne Val ∅ A → Ne Val Δ (↥ty ⁿ⌊ Δ ⌋ A)
↥nev Δ = ↑nev (to Δ)

↥nf : ∀ Δ {A : Ty 0} → Nf ∅ A → Nf Δ (↥ty ⁿ⌊ Δ ⌋ A)
↥nf Δ = ↑nf (to Δ)

↥val : ∀ Δ {A : Ty 0} → Val ∅ A → Val Δ (↥ty ⁿ⌊ Δ ⌋ A)
↥val Δ = ↑val (to Δ)

↥env : ∀ Δ {Γ} → Env ∅ Γ → Env Δ Γ
↥env Δ = ↑env (to Δ)
