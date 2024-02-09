----------------------------------------------------------------------------------------------------

-- simply typed lambda calculus with natural numbers
-- with a separate syntactic category of constants
-- after Abel

module STLC-Naturals2 where

open import Kit1 public


----------------------------------------------------------------------------------------------------

infixr 18 _⌜⊃⌝_
data Ty : Set where
  _⌜⊃⌝_ : ∀ (A B : Ty) → Ty
  ⌜ℕ⌝   : Ty

open TyKit Ty public

data Con : Ty → Set where
  ⌜zero⌝ : Con ⌜ℕ⌝
  ⌜suc⌝  : Con (⌜ℕ⌝ ⌜⊃⌝ ⌜ℕ⌝)
  ⌜rec⌝  : ∀ {A} → Con (⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ (⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A) ⌜⊃⌝ A)

infix 3 _⊢_
infixl 18 _⌜$⌝_
data _⊢_ (Γ : Ctx) : Ty → Set where
  con   : ∀ {A} (k : Con A) → Γ ⊢ A
  var   : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  ⌜λ⌝   : ∀ {A B} (t : A ∷ Γ ⊢ B) → Γ ⊢ A ⌜⊃⌝ B
  _⌜$⌝_ : ∀ {A B} (t₁ : Γ ⊢ A ⌜⊃⌝ B) (t₂ : Γ ⊢ A) → Γ ⊢ B

open TmKit (kit _⊢_) public


----------------------------------------------------------------------------------------------------

ren : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
ren e (con k)     = con k
ren e (var i)     = var (ren∋ e i)
ren e (⌜λ⌝ t)     = ⌜λ⌝ (ren (lift⊆ e) t)
ren e (t₁ ⌜$⌝ t₂) = ren e t₁ ⌜$⌝ ren e t₂

open RenKit (kit var ren) public

sub : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ⊢ A → Ξ ⊢ A
sub ss (con k)     = con k
sub ss (var i)     = sub∋ ss i
sub ss (⌜λ⌝ t)     = ⌜λ⌝ (sub (lift* ss) t)
sub ss (t₁ ⌜$⌝ t₂) = sub ss t₁ ⌜$⌝ sub ss t₂

open SubKit (kit renkit sub) public


----------------------------------------------------------------------------------------------------

-- definitional equality
module BetaShortDefEq where
  infix 4 _≝_
  data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    refl≝   : ∀ {A} {t : Γ ⊢ A} → t ≝ t
    sym≝    : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
    trans≝  : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
    congλ   : ∀ {A B} {t t′ : A ∷ Γ ⊢ B} (eq : t ≝ t′) → ⌜λ⌝ t ≝ ⌜λ⌝ t′
    cong$   : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
              t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
    congsuc : ∀ {t t′ : Γ ⊢ ⌜ℕ⌝} (eq : t ≝ t′) → con ⌜suc⌝ ⌜$⌝ t ≝ con ⌜suc⌝ ⌜$⌝ t′
    congrec : ∀ {A} {tₙ tₙ′ : Γ ⊢ ⌜ℕ⌝} {t₀ t₀′ : Γ ⊢ A} {tₛ tₛ′ : Γ ⊢ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A}
                (eqₙ : tₙ ≝ tₙ′) (eq₀ : t₀ ≝ t₀′) (eqₛ : tₛ ≝ tₛ′) →
              con ⌜rec⌝ ⌜$⌝ tₙ ⌜$⌝ t₀ ⌜$⌝ tₛ ≝ con ⌜rec⌝ ⌜$⌝ tₙ′ ⌜$⌝ t₀′ ⌜$⌝ tₛ′
    βred⊃   : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) →
              ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
    βredℕ₀  : ∀ {A} {t₀ : Γ ⊢ A} {tₛ : Γ ⊢ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A} →
              con ⌜rec⌝ ⌜$⌝ con ⌜zero⌝ ⌜$⌝ t₀ ⌜$⌝ tₛ ≝ t₀
    βredℕₛ  : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ : Γ ⊢ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A} →
              con ⌜rec⌝ ⌜$⌝ (con ⌜suc⌝ ⌜$⌝ tₙ) ⌜$⌝ t₀ ⌜$⌝ tₛ ≝
                tₛ ⌜$⌝ tₙ ⌜$⌝ (con ⌜rec⌝ ⌜$⌝ tₙ ⌜$⌝ t₀ ⌜$⌝ tₛ)

  open DefEqKit (kit tmkit (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝) public

module BetaShortEtaLongDefEq where
  infix 4 _≝_
  data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    refl≝   : ∀ {A} {t : Γ ⊢ A} → t ≝ t
    sym≝    : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
    trans≝  : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
    congλ   : ∀ {A B} {t t′ : A ∷ Γ ⊢ B} (eq : t ≝ t′) → ⌜λ⌝ t ≝ ⌜λ⌝ t′
    cong$   : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
              t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
    congsuc : ∀ {t t′ : Γ ⊢ ⌜ℕ⌝} (eq : t ≝ t′) → con ⌜suc⌝ ⌜$⌝ t ≝ con ⌜suc⌝ ⌜$⌝ t′
    congrec : ∀ {A} {tₙ tₙ′ : Γ ⊢ ⌜ℕ⌝} {t₀ t₀′ : Γ ⊢ A} {tₛ tₛ′ : Γ ⊢ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A}
                (eqₙ : tₙ ≝ tₙ′) (eq₀ : t₀ ≝ t₀′) (eqₛ : tₛ ≝ tₛ′) →
              con ⌜rec⌝ ⌜$⌝ tₙ ⌜$⌝ t₀ ⌜$⌝ tₛ ≝ con ⌜rec⌝ ⌜$⌝ tₙ′ ⌜$⌝ t₀′ ⌜$⌝ tₛ′
    βred⊃   : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) →
              ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
    βredℕ₀  : ∀ {A} {t₀ : Γ ⊢ A} {tₛ : Γ ⊢ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A} →
              con ⌜rec⌝ ⌜$⌝ con ⌜zero⌝ ⌜$⌝ t₀ ⌜$⌝ tₛ ≝ t₀
    βredℕₛ  : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ : Γ ⊢ ⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A} →
              con ⌜rec⌝ ⌜$⌝ (con ⌜suc⌝ ⌜$⌝ tₙ) ⌜$⌝ t₀ ⌜$⌝ tₛ ≝
                tₛ ⌜$⌝ tₙ ⌜$⌝ (con ⌜rec⌝ ⌜$⌝ tₙ ⌜$⌝ t₀ ⌜$⌝ tₛ)
    ηexp⊃   : ∀ {A B} {t : Γ ⊢ A ⌜⊃⌝ B} {t′} (eq : t′ ≡ wk t) → t ≝ ⌜λ⌝ (t′ ⌜$⌝ var zero)
    ηexpℕ   : ∀ {tₙ : Γ ⊢ ⌜ℕ⌝} →
              tₙ ≝ con ⌜rec⌝ ⌜$⌝ tₙ ⌜$⌝ con ⌜zero⌝ ⌜$⌝ ⌜λ⌝ (⌜λ⌝ (con ⌜suc⌝ ⌜$⌝ var (suc zero)))

  open DefEqKit (kit tmkit (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝) public


----------------------------------------------------------------------------------------------------

infix 4 _≟Ty_
_≟Ty_ : ∀ (A A′ : Ty) → Dec (A ≡ A′)
⌜ℕ⌝     ≟Ty A′ ⌜⊃⌝ B      = no λ ()
⌜ℕ⌝     ≟Ty ⌜ℕ⌝           = yes refl
A ⌜⊃⌝ B ≟Ty ⌜ℕ⌝           = no λ ()
A ⌜⊃⌝ B ≟Ty A′ ⌜⊃⌝ B′     with A ≟Ty A′ | B ≟Ty B′
... | no ¬eq₁  | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂    = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl   = yes refl

infix 4 _≟Con_
_≟Con_ : ∀ {A} (k k′ : Con A) → Dec (k ≡ k′)
⌜zero⌝ ≟Con ⌜zero⌝ = yes refl
⌜suc⌝  ≟Con ⌜suc⌝  = yes refl
⌜rec⌝  ≟Con ⌜rec⌝  = yes refl

infix 4 _≟_
_≟_ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Dec (t ≡ t′)
con k     ≟ con k′          with k ≟Con k′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
con k     ≟ var i             = no λ ()
con k     ≟ ⌜λ⌝ t′            = no λ ()
con k     ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
var i     ≟ con k             = no λ ()
var i     ≟ var i′          with i ≟∋ i′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
var i     ≟ ⌜λ⌝ t′            = no λ ()
var i     ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
⌜λ⌝ t     ≟ con k             = no λ ()
⌜λ⌝ t     ≟ var i′            = no λ ()
⌜λ⌝ t     ≟ ⌜λ⌝ t′          with t ≟ t′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
⌜λ⌝ t     ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
t₁ ⌜$⌝ t₂ ≟ con k             = no λ ()
t₁ ⌜$⌝ t₂ ≟ var i′            = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜λ⌝ t′            = no λ ()
t₁ ⌜$⌝ t₂ ≟ t₁′ ⌜$⌝ t₂′     with ty t₁ ≟Ty ty t₁′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                with t₁ ≟ t₁′ | t₂ ≟ t₂′
...   | no ¬eq₁  | _            = no λ { refl → refl ↯ ¬eq₁ }
...   | yes refl | no ¬eq₂      = no λ { refl → refl ↯ ¬eq₂ }
...   | yes refl | yes refl     = yes refl


----------------------------------------------------------------------------------------------------
