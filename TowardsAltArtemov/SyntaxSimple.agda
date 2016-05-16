module TowardsAltArtemov.SyntaxSimple where

open import Data.Nat using (ℕ ; zero ; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂)
open import Relation.Nullary using (Dec ; yes ; no)


data _≥_ : ℕ → ℕ → Set where
  id   : ∀ {n}              → n ≥ n
  weak : ∀ {n′ n} → n′ ≥ n → suc n′ ≥ n
  lift : ∀ {n′ n} → n′ ≥ n → suc n′ ≥ suc n

_○_ : ∀ {n″ n′ n} → n″ ≥ n′ → n′ ≥ n → n″ ≥ n
id      ○ p      = p
weak p′ ○ p      = weak (p′ ○ p)
lift p′ ○ id     = lift p′
lift p′ ○ weak p = weak (p′ ○ p)
lift p′ ○ lift p = lift (p′ ○ p)


data °Var : Set where
  °top : °Var
  °pop : °Var → °Var


data °Tm : Set where
  °var⟨_⟩  : ℕ → °Var → °Tm
  °lam⟨_⟩  : ℕ → °Tm → °Tm
  °app⟨_⟩  : ℕ → °Tm → °Tm → °Tm
  °pair⟨_⟩ : ℕ → °Tm → °Tm → °Tm
  °fst⟨_⟩  : ℕ → °Tm → °Tm
  °snd⟨_⟩  : ℕ → °Tm → °Tm
  °up⟨_⟩   : ℕ → °Tm → °Tm
  °down⟨_⟩ : ℕ → °Tm → °Tm
  !_       : °Tm → °Tm


data Ty : Set where
  ★   : Ty
  _⊃_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty
  _∶_ : °Tm → Ty → Ty

infixr 15 _∶_
infixr 5 _⊃_


data Cx : Set where
  ∅   : Cx
  _,_ : Cx → Ty → Cx

ⁿ⌊_⌋ : (Γ : Cx) → ℕ
ⁿ⌊ ∅ ⌋     = zero
ⁿ⌊ Γ , A ⌋ = suc ⁿ⌊ Γ ⌋


data _⊇_ : Cx → Cx → Set where
  id   : ∀ {Γ}                → Γ ⊇ Γ
  weak : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → (Γ′ , A) ⊇ Γ
  lift : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → (Γ′ , A) ⊇ (Γ , A)

ᵖ⌊_⌋ : ∀ {Γ′ Γ} → Γ ⊇ Γ′ → ⁿ⌊ Γ ⌋ ≥ ⁿ⌊ Γ′ ⌋
ᵖ⌊ id ⌋       = id
ᵖ⌊ weak η ⌋ = weak ᵖ⌊ η ⌋
ᵖ⌊ lift η ⌋ = lift ᵖ⌊ η ⌋

_●_ : ∀ {Γ″ Γ′ Γ} → Γ″ ⊇ Γ′ → Γ′ ⊇ Γ → Γ″ ⊇ Γ
id      ● η      = η
weak η′ ● η      = weak (η′ ● η)
lift η′ ● id     = lift η′
lift η′ ● weak η = weak (η′ ● η)
lift η′ ● lift η = lift (η′ ● η)

to : ∀ Γ → Γ ⊇ ∅
to ∅       = id
to (Γ , A) = weak (to Γ)

str : ∀ {Γ′ Γ A} → Γ′ ⊇ (Γ , A) → Γ′ ⊇ Γ
str id       = weak id
str (weak η) = weak (str η)
str (lift η) = weak η

low : ∀ {Γ′ Γ A} → (Γ′ , A) ⊇ (Γ , A) → Γ′ ⊇ Γ
low id       = id
low (weak η) = str η
low (lift η) = η


data Var : Cx → Ty → Set where
  top : ∀ {Γ A}              → Var (Γ , A) A
  pop : ∀ {Γ A B} → Var Γ A → Var (Γ , B) A

ⁱ⌊_⌋ : ∀ {Γ A} → Var Γ A → °Var
ⁱ⌊ top ⌋   = °top
ⁱ⌊ pop x ⌋ = °pop ⁱ⌊ x ⌋

↑var : ∀ {Γ′ Γ A} (η : Γ′ ⊇ Γ) → Var Γ A → Var Γ′ A
↑var id       x       = x
↑var (weak η) x       = pop (↑var η x)
↑var (lift η) top     = top
↑var (lift η) (pop x) = pop (↑var η x)

↥var : ∀ Γ {A} → Var ∅ A → Var Γ A
↥var Γ ()


data Vec : ℕ → Set where
  []  : Vec 0
  _∷_ : ∀ {n} → °Tm → Vec n → Vec (suc n)


_∴_ : ∀ {n} → Vec n → Ty → Ty
[]       ∴ A = A
(t ∷ ts) ∴ A = t ∶ (ts ∴ A)

infixr 15 _∴_


°lams⟨_⟩ : ∀ n → Vec n → Vec n
°lams⟨ zero ⟩  []       = []
°lams⟨ suc n ⟩ (t ∷ ts) = °lam⟨ n ⟩ t ∷ °lams⟨ n ⟩ ts

°apps⟨_⟩ : ∀ n → Vec n → Vec n → Vec n
°apps⟨ zero ⟩  []       []       = []
°apps⟨ suc n ⟩ (t ∷ ts) (u ∷ us) = °app⟨ n ⟩ t u ∷ °apps⟨ n ⟩ ts us

°pairs⟨_⟩ : ∀ n → Vec n → Vec n → Vec n
°pairs⟨ zero ⟩  []       []       = []
°pairs⟨ suc n ⟩ (t ∷ ts) (u ∷ us) = °pair⟨ n ⟩ t u ∷ °pairs⟨ n ⟩ ts us

°fsts⟨_⟩ : ∀ n → Vec n → Vec n
°fsts⟨ zero ⟩  []       = []
°fsts⟨ suc n ⟩ (t ∷ ts) = °fst⟨ n ⟩ t ∷ °fsts⟨ n ⟩ ts

°snds⟨_⟩ : ∀ n → Vec n → Vec n
°snds⟨ zero ⟩  []       = []
°snds⟨ suc n ⟩ (t ∷ ts) = °snd⟨ n ⟩ t ∷ °snds⟨ n ⟩ ts

°ups⟨_⟩ : ∀ n → Vec n → Vec n
°ups⟨ zero ⟩  []       = []
°ups⟨ suc n ⟩ (t ∷ ts) = °up⟨ n ⟩ t ∷ °ups⟨ n ⟩ ts

°downs⟨_⟩ : ∀ n → Vec n → Vec n
°downs⟨ zero ⟩  []       = []
°downs⟨ suc n ⟩ (t ∷ ts) = °down⟨ n ⟩ t ∷ °downs⟨ n ⟩ ts


data Tm (Γ : Cx) : Ty → Set where
  var     : ∀ {A} → Var Γ A → Tm Γ A
  lam⟨_⟩  : ∀ n {ts : Vec n} {A B} → Tm (Γ , A) (ts ∴ B) → Tm Γ (°lams⟨ n ⟩ ts ∴ (A ⊃ B))
  app⟨_⟩  : ∀ n {ts us : Vec n} {A B} → Tm Γ (ts ∴ (A ⊃ B)) → Tm Γ (us ∴ A) → Tm Γ (°apps⟨ n ⟩ ts us ∴ B)
  pair⟨_⟩ : ∀ n {ts us : Vec n} {A B} → Tm Γ (ts ∴ A) → Tm Γ (us ∴ B) → Tm Γ (°pairs⟨ n ⟩ ts us ∴ (A ∧ B))
  fst⟨_⟩  : ∀ n {ts : Vec n} {A B} → Tm Γ (ts ∴ (A ∧ B)) → Tm Γ (°fsts⟨ n ⟩ ts ∴ A)
  snd⟨_⟩  : ∀ n {ts : Vec n} {A B} → Tm Γ (ts ∴ (A ∧ B)) → Tm Γ (°snds⟨ n ⟩ ts ∴ B)
  up⟨_⟩   : ∀ n {ts : Vec n} {u : °Tm} {A} → Tm Γ (ts ∴ u ∶ A) → Tm Γ (°ups⟨ n ⟩ ts ∴ ! u ∶ u ∶ A)
  down⟨_⟩ : ∀ n {ts : Vec n} {u : °Tm} {A} → Tm Γ (ts ∴ u ∶ A) → Tm Γ (°downs⟨ n ⟩ ts ∴ A)

↑tm : ∀ {Γ′ Γ A} (η : Γ′ ⊇ Γ) → Tm Γ A → Tm Γ′ A
↑tm η (var x)                  = var (↑var η x)
↑tm η (lam⟨ n ⟩ t)    = lam⟨ n ⟩ (↑tm (lift η) t)
↑tm η (app⟨ n ⟩ t u)  = app⟨ n ⟩ (↑tm η t) (↑tm η u)
↑tm η (pair⟨ n ⟩ t u) = pair⟨ n ⟩ (↑tm η t) (↑tm η u)
↑tm η (fst⟨ n ⟩ t)    = fst⟨ n ⟩ (↑tm η t)
↑tm η (snd⟨ n ⟩ t)    = snd⟨ n ⟩ (↑tm η t)
↑tm η (up⟨ n ⟩ t)     = up⟨ n ⟩ (↑tm η t)
↑tm η (down⟨ n ⟩ t)   = down⟨ n ⟩ (↑tm η t)

↥tm : ∀ Γ {A} → Tm ∅ A → Tm Γ A
↥tm Γ = ↑tm (to Γ)


data Ne (Ξ : Cx → Ty → Set) (Γ : Cx) : Ty → Set where
  var     : ∀ {A} → Var Γ A → Ne Ξ Γ A
  app⟨_⟩  : ∀ n {ts us : Vec n} {A B} → Ne Ξ Γ (ts ∴ (A ⊃ B)) → Ξ Γ (us ∴ A) → Ne Ξ Γ (°apps⟨ n ⟩ ts us ∴ B)
  fst⟨_⟩  : ∀ n {ts : Vec n} {A B} → Ne Ξ Γ (ts ∴ (A ∧ B)) → Ne Ξ Γ (°fsts⟨ n ⟩ ts ∴ A)
  snd⟨_⟩  : ∀ n {ts : Vec n} {A B} → Ne Ξ Γ (ts ∴ (A ∧ B)) → Ne Ξ Γ (°snds⟨ n ⟩ ts ∴ B)
  down⟨_⟩ : ∀ n {ts : Vec n} {u : °Tm} {A} → Ne Ξ Γ (ts ∴ u ∶ A) → Ne Ξ Γ (°downs⟨ n ⟩ ts ∴ A)

data Nf (Δ : Cx) : Ty → Set where
  ne      : Ne Nf Δ ★ → Nf Δ ★
  lam⟨_⟩  : ∀ n {ts : Vec n} {A B} → Nf (Δ , A) (ts ∴ B) → Nf Δ (°lams⟨ n ⟩ ts ∴ (A ⊃ B))
  pair⟨_⟩ : ∀ n {ts us : Vec n} {A B} → Nf Δ (ts ∴ A) → Nf Δ (us ∴ B) → Nf Δ (°pairs⟨ n ⟩ ts us ∴ (A ∧ B))
  up⟨_⟩   : ∀ n {ts : Vec n} {u : °Tm} {A} → Nf Δ (ts ∴ u ∶ A) → Nf Δ (°ups⟨ n ⟩ ts ∴ ! u ∶ u ∶ A)

mutual
  data Val (Δ : Cx) : Ty → Set where
    ne      : ∀ {A} → Ne Val Δ A → Val Δ A
    lam⟨_⟩  : ∀ n {ts : Vec n} {Γ A B} → Tm (Γ , A) (ts ∴ B) → Env Δ Γ → Val Δ (°lams⟨ n ⟩ ts ∴ (A ⊃ B))
    pair⟨_⟩ : ∀ n {ts us : Vec n} {A B} → Val Δ (ts ∴ A) → Val Δ (us ∴ B) → Val Δ (°pairs⟨ n ⟩ ts us ∴ (A ∧ B))
    up⟨_⟩   : ∀ n {ts : Vec n} {u : °Tm} {A} → Val Δ (ts ∴ u ∶ A) → Val Δ (°ups⟨ n ⟩ ts ∴ ! u ∶ u ∶ A)

  data Env (Δ : Cx) : Cx → Set where
    ∅   : Env Δ ∅
    _,_ : ∀ {Γ A} → Env Δ Γ → Val Δ A → Env Δ (Γ , A)


mutual
  ↑nen : ∀ {Δ′ Δ A} (η : Δ′ ⊇ Δ) → Ne Nf Δ A → Ne Nf Δ′ A
  ↑nen η (var x)        = var (↑var η x)
  ↑nen η (app⟨ n ⟩ t u) = app⟨ n ⟩ (↑nen η t) (↑nf η u)
  ↑nen η (fst⟨ n ⟩ t)   = fst⟨ n ⟩ (↑nen η t)
  ↑nen η (snd⟨ n ⟩ t)   = snd⟨ n ⟩ (↑nen η t)
  ↑nen η (down⟨ n ⟩ t)  = down⟨ n ⟩ (↑nen η t)

  ↑nev : ∀ {Δ′ Δ A} (η : Δ′ ⊇ Δ) → Ne Val Δ A → Ne Val Δ′ A
  ↑nev η (var x)        = var (↑var η x)
  ↑nev η (app⟨ n ⟩ t u) = app⟨ n ⟩ (↑nev η t) (↑val η u)
  ↑nev η (fst⟨ n ⟩ t)   = fst⟨ n ⟩ (↑nev η t)
  ↑nev η (snd⟨ n ⟩ t)   = snd⟨ n ⟩ (↑nev η t)
  ↑nev η (down⟨ n ⟩ t)  = down⟨ n ⟩ (↑nev η t)

  ↑nf : ∀ {Δ′ Δ A} (η : Δ′ ⊇ Δ) → Nf Δ A → Nf Δ′ A
  ↑nf η (ne n)          = ne (↑nen η n)
  ↑nf η (lam⟨ n ⟩ t)    = lam⟨ n ⟩ (↑nf (lift η) t)
  ↑nf η (pair⟨ n ⟩ t u) = pair⟨ n ⟩ (↑nf η t) (↑nf η u)
  ↑nf η (up⟨ n ⟩ t)     = up⟨ n ⟩ (↑nf η t)

  ↑val : ∀ {Δ′ Δ A} (η : Δ′ ⊇ Δ) → Val Δ A → Val Δ′ A
  ↑val η (ne n)          = ne (↑nev η n)
  ↑val η (lam⟨ n ⟩ t γ)  = lam⟨ n ⟩ t (↑env η γ)
  ↑val η (pair⟨ n ⟩ t u) = pair⟨ n ⟩ (↑val η t) (↑val η u)
  ↑val η (up⟨ n ⟩ t)     = up⟨ n ⟩ (↑val η t)

  ↑env : ∀ {Δ′ Δ Γ} (η : Δ′ ⊇ Δ) → Env Δ Γ → Env Δ′ Γ
  ↑env η ∅       = ∅
  ↑env η (γ , t) = (↑env η γ , ↑val η t)
