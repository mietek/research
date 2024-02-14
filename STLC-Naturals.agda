----------------------------------------------------------------------------------------------------

-- simply typed lambda calculus with natural numbers

module STLC-Naturals where

open import Kit1 public


----------------------------------------------------------------------------------------------------

infixr 18 _⌜⊃⌝_
data Ty : Set where
  _⌜⊃⌝_ : ∀ (A B : Ty) → Ty
  ⌜ℕ⌝   : Ty

open TyKit Ty public

infix 3 _⊢_
infixl 18 _⌜$⌝_
data _⊢_ (Γ : Ctx) : Ty → Set where
  var    : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  ⌜λ⌝    : ∀ {A B} (t : A ∷ Γ ⊢ B) → Γ ⊢ A ⌜⊃⌝ B
  _⌜$⌝_  : ∀ {A B} (t₁ : Γ ⊢ A ⌜⊃⌝ B) (t₂ : Γ ⊢ A) → Γ ⊢ B
  ⌜zero⌝ : Γ ⊢ ⌜ℕ⌝
  ⌜suc⌝  : ∀ (t : Γ ⊢ ⌜ℕ⌝) → Γ ⊢ ⌜ℕ⌝
  ⌜rec⌝  : ∀ {A} (tₙ : Γ ⊢ ⌜ℕ⌝) (t₀ : Γ ⊢ A) (tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A) → Γ ⊢ A

open TmKit (kit _⊢_) public


----------------------------------------------------------------------------------------------------

ren : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
ren e (var i)          = var (ren∋ e i)
ren e (⌜λ⌝ t)          = ⌜λ⌝ (ren (lift⊆ e) t)
ren e (t₁ ⌜$⌝ t₂)      = ren e t₁ ⌜$⌝ ren e t₂
ren e ⌜zero⌝           = ⌜zero⌝
ren e (⌜suc⌝ t)        = ⌜suc⌝ (ren e t)
ren e (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ (ren e tₙ) (ren e t₀) (ren (lift⊆ (lift⊆ e)) tₛ)

open RenKit (kit var ren) public

sub : ∀ {Γ Ξ A} → Ξ ⊢§ Γ → Γ ⊢ A → Ξ ⊢ A
sub ss (var i)          = sub∋ ss i
sub ss (⌜λ⌝ t)          = ⌜λ⌝ (sub (lift§ ss) t)
sub ss (t₁ ⌜$⌝ t₂)      = sub ss t₁ ⌜$⌝ sub ss t₂
sub ss ⌜zero⌝           = ⌜zero⌝
sub ss (⌜suc⌝ t)        = ⌜suc⌝ (sub ss t)
sub ss (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ (sub ss tₙ) (sub ss t₀) (sub (lift§ (lift§ ss)) tₛ)

open SubKit (kit renkit sub) public


----------------------------------------------------------------------------------------------------

module BetaShortDefEq where
  infix 4 _≝_
  data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    refl≝   : ∀ {A} {t : Γ ⊢ A} → t ≝ t
    sym≝    : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
    trans≝  : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
    congλ   : ∀ {A B} {t t′ : A ∷ Γ ⊢ B} (eq : t ≝ t′) → ⌜λ⌝ t ≝ ⌜λ⌝ t′
    cong$   : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
              t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
    congsuc : ∀ {t t′ : Γ ⊢ ⌜ℕ⌝} (eq : t ≝ t′) → ⌜suc⌝ t ≝ ⌜suc⌝ t′
    congrec : ∀ {A} {tₙ tₙ′ : Γ ⊢ ⌜ℕ⌝} {t₀ t₀′ : Γ ⊢ A} {tₛ tₛ′ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A}
                (eqₙ : tₙ ≝ tₙ′) (eq₀ : t₀ ≝ t₀′) (eqₛ : tₛ ≝ tₛ′) →
              ⌜rec⌝ tₙ t₀ tₛ ≝ ⌜rec⌝ tₙ′ t₀′ tₛ′
    βred⊃   : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) →
              ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
    βredℕ₀  : ∀ {A} {t₀ : Γ ⊢ A} {tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} → ⌜rec⌝ ⌜zero⌝ t₀ tₛ ≝ t₀
    βredℕₛ  : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} {t′}
                (eq : t′ ≡ tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ] [ tₙ ]) →
              ⌜rec⌝ (⌜suc⌝ tₙ) t₀ tₛ ≝ t′

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
    congsuc : ∀ {t t′ : Γ ⊢ ⌜ℕ⌝} (eq : t ≝ t′) → ⌜suc⌝ t ≝ ⌜suc⌝ t′
    congrec : ∀ {A} {tₙ tₙ′ : Γ ⊢ ⌜ℕ⌝} {t₀ t₀′ : Γ ⊢ A} {tₛ tₛ′ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A}
                (eqₙ : tₙ ≝ tₙ′) (eq₀ : t₀ ≝ t₀′) (eqₛ : tₛ ≝ tₛ′) →
              ⌜rec⌝ tₙ t₀ tₛ ≝ ⌜rec⌝ tₙ′ t₀′ tₛ′
    βred⊃   : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) →
              ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
    βredℕ₀  : ∀ {A} {t₀ : Γ ⊢ A} {tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} → ⌜rec⌝ ⌜zero⌝ t₀ tₛ ≝ t₀
    βredℕₛ  : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} {t′}
                (eq : t′ ≡ tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ] [ tₙ ]) →
              ⌜rec⌝ (⌜suc⌝ tₙ) t₀ tₛ ≝ t′
    ηexp⊃   : ∀ {A B} {t : Γ ⊢ A ⌜⊃⌝ B} {t′} (eq : t′ ≡ wk t) → t ≝ ⌜λ⌝ (t′ ⌜$⌝ var zero)
    ηexpℕ   : ∀ {tₙ : Γ ⊢ ⌜ℕ⌝} → tₙ ≝ ⌜rec⌝ tₙ ⌜zero⌝ (⌜suc⌝ (var (suc zero)))

  open DefEqKit (kit tmkit (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝) public


----------------------------------------------------------------------------------------------------

infix 4 _≟Ty_
_≟Ty_ : ∀ (A A′ : Ty) → Dec (A ≡ A′)
A ⌜⊃⌝ B ≟Ty A′ ⌜⊃⌝ B′     with A ≟Ty A′ | B ≟Ty B′
... | no ¬eq₁  | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂    = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl   = yes refl
A ⌜⊃⌝ B ≟Ty ⌜ℕ⌝           = no λ ()
⌜ℕ⌝     ≟Ty A′ ⌜⊃⌝ B      = no λ ()
⌜ℕ⌝     ≟Ty ⌜ℕ⌝           = yes refl

infix 4 _≟_
_≟_ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Dec (t ≡ t′)
var i          ≟ var i′              with i ≟∋ i′
... | no ¬eq                           = no λ { refl → refl ↯ ¬eq }
... | yes refl                         = yes refl
var i          ≟ ⌜λ⌝ t′                = no λ ()
var i          ≟ t₁′ ⌜$⌝ t₂′           = no λ ()
var i          ≟ ⌜zero⌝                = no λ ()
var i          ≟ ⌜suc⌝ t′              = no λ ()
var i          ≟ ⌜rec⌝ tₙ′ t₀′ tₛ′     = no λ ()
⌜λ⌝ t          ≟ var i′                = no λ ()
⌜λ⌝ t          ≟ ⌜λ⌝ t′              with t ≟ t′
... | no ¬eq                           = no λ { refl → refl ↯ ¬eq }
... | yes refl                         = yes refl
⌜λ⌝ t          ≟ t₁′ ⌜$⌝ t₂′           = no λ ()
⌜λ⌝ t          ≟ ⌜rec⌝ tₙ′ t₀′ tₛ′     = no λ ()
t₁ ⌜$⌝ t₂      ≟ var i′                = no λ ()
t₁ ⌜$⌝ t₂      ≟ ⌜λ⌝ t′                = no λ ()
t₁ ⌜$⌝ t₂      ≟ t₁′ ⌜$⌝ t₂′         with ty t₁ ≟Ty ty t₁′
... | no ¬eq                           = no λ { refl → refl ↯ ¬eq }
... | yes refl                         with t₁ ≟ t₁′ | t₂ ≟ t₂′
...   | no ¬eq₁  | _                     = no λ { refl → refl ↯ ¬eq₁ }
...   | yes refl | no ¬eq₂               = no λ { refl → refl ↯ ¬eq₂ }
...   | yes refl | yes refl              = yes refl
t₁ ⌜$⌝ t₂      ≟ ⌜zero⌝                = no λ ()
t₁ ⌜$⌝ t₂      ≟ ⌜suc⌝ t′              = no λ ()
t₁ ⌜$⌝ t₂      ≟ ⌜rec⌝ tₙ′ t₀′ tₛ′     = no λ ()
⌜zero⌝         ≟ var i                 = no λ ()
⌜zero⌝         ≟ t₁′ ⌜$⌝ t₂′           = no λ ()
⌜zero⌝         ≟ ⌜zero⌝                = yes refl
⌜zero⌝         ≟ ⌜suc⌝ t′              = no λ ()
⌜zero⌝         ≟ ⌜rec⌝ tₙ′ t₀′ tₛ′     = no λ ()
⌜suc⌝ t        ≟ var i                 = no λ ()
⌜suc⌝ t        ≟ t₁′ ⌜$⌝ t₂′           = no λ ()
⌜suc⌝ t        ≟ ⌜zero⌝                = no λ ()
⌜suc⌝ t        ≟ ⌜suc⌝ t′            with t ≟ t′
... | no ¬eq                           = no λ { refl → refl ↯ ¬eq }
... | yes refl                         = yes refl
⌜suc⌝ t        ≟ ⌜rec⌝ tₙ′ t₀′ tₛ′     = no λ ()
⌜rec⌝ tₙ t₀ tₛ ≟ var i                 = no λ ()
⌜rec⌝ tₙ t₀ tₛ ≟ ⌜λ⌝ t′                = no λ ()
⌜rec⌝ tₙ t₀ tₛ ≟ t₁′ ⌜$⌝ t₂′           = no λ ()
⌜rec⌝ tₙ t₀ tₛ ≟ ⌜zero⌝                = no λ ()
⌜rec⌝ tₙ t₀ tₛ ≟ ⌜suc⌝ t′              = no λ ()
⌜rec⌝ tₙ t₀ tₛ ≟ ⌜rec⌝ tₙ′ t₀′ tₛ′   with tₙ ≟ tₙ′ | t₀ ≟ t₀′ | tₛ ≟ tₛ′
... | no ¬eqₙ  | _        | _          = no λ { refl → refl ↯ ¬eqₙ }
... | yes refl | no ¬eq₀  | _          = no λ { refl → refl ↯ ¬eq₀ }
... | yes refl | yes refl | no ¬eqₛ    = no λ { refl → refl ↯ ¬eqₛ }
... | yes refl | yes refl | yes refl   = yes refl


----------------------------------------------------------------------------------------------------
