module A201605.TowardsAltArtemov.SyntaxSimpleCatholic where

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
  lam⟨_⟩  : ∀ n {ts : Vec n} {A B Z} → Tm (Γ , A) (ts ∴ B) → {{_ : Z ≡ °lams⟨ n ⟩ ts ∴ (A ⊃ B)}} → Tm Γ Z
  app⟨_⟩  : ∀ n {ts us : Vec n} {A B Z} → Tm Γ (ts ∴ (A ⊃ B)) → Tm Γ (us ∴ A) → {{_ : Z ≡ °apps⟨ n ⟩ ts us ∴ B}} → Tm Γ Z
  pair⟨_⟩ : ∀ n {ts us : Vec n} {A B Z} → Tm Γ (ts ∴ A) → Tm Γ (us ∴ B) → {{_ : Z ≡ °pairs⟨ n ⟩ ts us ∴ (A ∧ B)}} → Tm Γ Z
  fst⟨_⟩  : ∀ n {ts : Vec n} {A B Z} → Tm Γ (ts ∴ (A ∧ B)) → {{_ : Z ≡ °fsts⟨ n ⟩ ts ∴ A}} → Tm Γ Z
  snd⟨_⟩  : ∀ n {ts : Vec n} {A B Z} → Tm Γ (ts ∴ (A ∧ B)) → {{_ : Z ≡ °snds⟨ n ⟩ ts ∴ B}} → Tm Γ Z
  up⟨_⟩   : ∀ n {ts : Vec n} {u : °Tm} {A Z} → Tm Γ (ts ∴ u ∶ A) → {{_ : Z ≡ °ups⟨ n ⟩ ts ∴ ! u ∶ u ∶ A}} → Tm Γ Z
  down⟨_⟩ : ∀ n {ts : Vec n} {u : °Tm} {A Z} → Tm Γ (ts ∴ u ∶ A) → {{_ : Z ≡ °downs⟨ n ⟩ ts ∴ A}} → Tm Γ Z

↑tm : ∀ {Γ′ Γ A} (η : Γ′ ⊇ Γ) → Tm Γ A → Tm Γ′ A
↑tm η (var x)                  = var (↑var η x)
↑tm η (lam⟨ n ⟩ t {{refl}})    = lam⟨ n ⟩ (↑tm (lift η) t) {{refl}}
↑tm η (app⟨ n ⟩ t u {{refl}})  = app⟨ n ⟩ (↑tm η t) (↑tm η u) {{refl}}
↑tm η (pair⟨ n ⟩ t u {{refl}}) = pair⟨ n ⟩ (↑tm η t) (↑tm η u) {{refl}}
↑tm η (fst⟨ n ⟩ t {{refl}})    = fst⟨ n ⟩ (↑tm η t) {{refl}}
↑tm η (snd⟨ n ⟩ t {{refl}})    = snd⟨ n ⟩ (↑tm η t) {{refl}}
↑tm η (up⟨ n ⟩ t {{refl}})     = up⟨ n ⟩ (↑tm η t) {{refl}}
↑tm η (down⟨ n ⟩ t {{refl}})   = down⟨ n ⟩ (↑tm η t) {{refl}}

↥tm : ∀ Γ {A} → Tm ∅ A → Tm Γ A
↥tm Γ = ↑tm (to Γ)


data Ne (Ξ : Cx → Ty → Set) (Γ : Cx) : Ty → Set where
  var     : ∀ {A} → Var Γ A → Ne Ξ Γ A
  app⟨_⟩  : ∀ n {ts us : Vec n} {A B Z} → Ne Ξ Γ (ts ∴ (A ⊃ B)) → Ξ Γ (us ∴ A) → {{_ : Z ≡ °apps⟨ n ⟩ ts us ∴ B}} → Ne Ξ Γ Z
  fst⟨_⟩  : ∀ n {ts : Vec n} {A B Z} → Ne Ξ Γ (ts ∴ (A ∧ B)) → {{_ : Z ≡ °fsts⟨ n ⟩ ts ∴ A}} → Ne Ξ Γ Z
  snd⟨_⟩  : ∀ n {ts : Vec n} {A B Z} → Ne Ξ Γ (ts ∴ (A ∧ B)) → {{_ : Z ≡ °snds⟨ n ⟩ ts ∴ B}} → Ne Ξ Γ Z
  down⟨_⟩ : ∀ n {ts : Vec n} {u : °Tm} {A Z} → Ne Ξ Γ (ts ∴ u ∶ A) → {{_ : Z ≡ °downs⟨ n ⟩ ts ∴ A}} → Ne Ξ Γ Z

data Nf (Δ : Cx) : Ty → Set where
  ne      : Ne Nf Δ ★ → Nf Δ ★
  lam⟨_⟩  : ∀ n {ts : Vec n} {A B Z} → Nf (Δ , A) (ts ∴ B) → {{_ : Z ≡ °lams⟨ n ⟩ ts ∴ (A ⊃ B)}} → Nf Δ Z
  pair⟨_⟩ : ∀ n {ts us : Vec n} {A B Z} → Nf Δ (ts ∴ A) → Nf Δ (us ∴ B) → {{_ : Z ≡ °pairs⟨ n ⟩ ts us ∴ (A ∧ B)}} → Nf Δ Z
  up⟨_⟩   : ∀ n {ts : Vec n} {u : °Tm} {A Z} → Nf Δ (ts ∴ u ∶ A) → {{_ : Z ≡ °ups⟨ n ⟩ ts ∴ ! u ∶ u ∶ A}} → Nf Δ Z

mutual
  data Val (Δ : Cx) : Ty → Set where
    ne      : ∀ {A} → Ne Val Δ A → Val Δ A
    lam⟨_⟩  : ∀ n {ts : Vec n} {Γ A B Z} → Tm (Γ , A) (ts ∴ B) → Env Δ Γ → {{_ : Z ≡ °lams⟨ n ⟩ ts ∴ (A ⊃ B)}} → Val Δ Z
    pair⟨_⟩ : ∀ n {ts us : Vec n} {A B Z} → Val Δ (ts ∴ A) → Val Δ (us ∴ B) → {{_ : Z ≡ °pairs⟨ n ⟩ ts us ∴ (A ∧ B)}} → Val Δ Z
    up⟨_⟩   : ∀ n {ts : Vec n} {u : °Tm} {A Z} → Val Δ (ts ∴ u ∶ A) → {{_ : Z ≡ °ups⟨ n ⟩ ts ∴ ! u ∶ u ∶ A}} → Val Δ Z

  data Env (Δ : Cx) : Cx → Set where
    ∅   : Env Δ ∅
    _,_ : ∀ {Γ A} → Env Δ Γ → Val Δ A → Env Δ (Γ , A)


mutual
  ↑nen : ∀ {Δ′ Δ A} (η : Δ′ ⊇ Δ) → Ne Nf Δ A → Ne Nf Δ′ A
  ↑nen η (var x)                 = var (↑var η x)
  ↑nen η (app⟨ n ⟩ t u {{refl}}) = app⟨ n ⟩ (↑nen η t) (↑nf η u) {{refl}}
  ↑nen η (fst⟨ n ⟩ t {{refl}})   = fst⟨ n ⟩ (↑nen η t) {{refl}}
  ↑nen η (snd⟨ n ⟩ t {{refl}})   = snd⟨ n ⟩ (↑nen η t) {{refl}}
  ↑nen η (down⟨ n ⟩ t {{refl}})  = down⟨ n ⟩ (↑nen η t) {{refl}}

  ↑nev : ∀ {Δ′ Δ A} (η : Δ′ ⊇ Δ) → Ne Val Δ A → Ne Val Δ′ A
  ↑nev η (var x)                 = var (↑var η x)
  ↑nev η (app⟨ n ⟩ t u {{refl}}) = app⟨ n ⟩ (↑nev η t) (↑val η u) {{refl}}
  ↑nev η (fst⟨ n ⟩ t {{refl}})   = fst⟨ n ⟩ (↑nev η t) {{refl}}
  ↑nev η (snd⟨ n ⟩ t {{refl}})   = snd⟨ n ⟩ (↑nev η t) {{refl}}
  ↑nev η (down⟨ n ⟩ t {{refl}})  = down⟨ n ⟩ (↑nev η t) {{refl}}

  ↑nf : ∀ {Δ′ Δ A} (η : Δ′ ⊇ Δ) → Nf Δ A → Nf Δ′ A
  ↑nf η (ne n)                   = ne (↑nen η n)
  ↑nf η (lam⟨ n ⟩ t {{refl}})    = lam⟨ n ⟩ (↑nf (lift η) t) {{refl}}
  ↑nf η (pair⟨ n ⟩ t u {{refl}}) = pair⟨ n ⟩ (↑nf η t) (↑nf η u) {{refl}}
  ↑nf η (up⟨ n ⟩ t {{refl}})     = up⟨ n ⟩ (↑nf η t) {{refl}}

  ↑val : ∀ {Δ′ Δ A} (η : Δ′ ⊇ Δ) → Val Δ A → Val Δ′ A
  ↑val η (ne n)                   = ne (↑nev η n)
  ↑val η (lam⟨ n ⟩ t γ {{refl}})  = lam⟨ n ⟩ t (↑env η γ) {{refl}}
  ↑val η (pair⟨ n ⟩ t u {{refl}}) = pair⟨ n ⟩ (↑val η t) (↑val η u) {{refl}}
  ↑val η (up⟨ n ⟩ t {{refl}})     = up⟨ n ⟩ (↑val η t) {{refl}}

  ↑env : ∀ {Δ′ Δ Γ} (η : Δ′ ⊇ Δ) → Env Δ Γ → Env Δ′ Γ
  ↑env η ∅       = ∅
  ↑env η (γ , t) = (↑env η γ , ↑val η t)
