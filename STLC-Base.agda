module STLC-Base where

open import Kit1 public


----------------------------------------------------------------------------------------------------

infixr 18 _⌜⊃⌝_
data Ty : Set where
  ⌜◦⌝   : Ty
  _⌜⊃⌝_ : ∀ (A B : Ty) → Ty

open TyKit Ty public

infix 3 _⊢_
infixl 18 _⌜$⌝_
data _⊢_ (Γ : Ctx) : Ty → Set where
  var   : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  ⌜λ⌝   : ∀ {A B} (t : A ∷ Γ ⊢ B) → Γ ⊢ A ⌜⊃⌝ B
  _⌜$⌝_ : ∀ {A B} (t₁ : Γ ⊢ A ⌜⊃⌝ B) (t₂ : Γ ⊢ A) → Γ ⊢ B

tk! = tmkit _⊢_
open TmKit tk! public


----------------------------------------------------------------------------------------------------

ren : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
ren e (var i)     = var (ren∋ e i)
ren e (⌜λ⌝ t)     = ⌜λ⌝ (ren (keep e) t)
ren e (t₁ ⌜$⌝ t₂) = ren e t₁ ⌜$⌝ ren e t₂

rk! = renkit var ren
open RenKit rk! public

sub : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ⊢ A → Ξ ⊢ A
sub ss (var i)     = sub∋ ss i
sub ss (⌜λ⌝ t)     = ⌜λ⌝ (sub (lifts ss) t)
sub ss (t₁ ⌜$⌝ t₂) = sub ss t₁ ⌜$⌝ sub ss t₂

sk! = subkit rk! sub
open SubKit sk! public


----------------------------------------------------------------------------------------------------

-- definitional equality
module BetaShort where
  infix 4 _≝_
  data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    refl≝  : ∀ {A} {t : Γ ⊢ A} → t ≝ t
    sym≝   : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
    trans≝ : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
    congλ  : ∀ {A B} {t t′ : A ∷ Γ ⊢ B} (eq : t ≝ t′) → ⌜λ⌝ t ≝ ⌜λ⌝ t′
    cong$  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
             t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
    βred⊃  : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) →
             ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′

  dek! = defeqkit tk! (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝
  open DefEqKit dek! public

module BetaShortEtaLong where
  infix 4 _≝_
  data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    refl≝  : ∀ {A} {t : Γ ⊢ A} → t ≝ t
    sym≝   : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
    trans≝ : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
    congλ  : ∀ {A B} {t t′ : A ∷ Γ ⊢ B} (eq : t ≝ t′) → ⌜λ⌝ t ≝ ⌜λ⌝ t′
    cong$  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
             t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
    βred⊃  : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) →
             ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
    ηexp⊃  : ∀ {A B} {t : Γ ⊢ A ⌜⊃⌝ B} {t′} (eq : t′ ≡ wk t) → t ≝ ⌜λ⌝ (t′ ⌜$⌝ var zero)

  dek! = defeqkit tk! (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝
  open DefEqKit dek! public


----------------------------------------------------------------------------------------------------

infix 4 _≟Ty_
_≟Ty_ : ∀ (A A′ : Ty) → Dec (A ≡ A′)
⌜◦⌝     ≟Ty ⌜◦⌝           = yes refl
⌜◦⌝     ≟Ty A′ ⌜⊃⌝ B′     = no λ ()
A ⌜⊃⌝ B ≟Ty ⌜◦⌝           = no λ ()
A ⌜⊃⌝ B ≟Ty A′ ⌜⊃⌝ B′     with A ≟Ty A′ | B ≟Ty B′
... | no ¬eq₁  | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂    = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl   = yes refl

infix 4 _≟_
_≟_ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Dec (t ≡ t′)
var i     ≟ var i′          with i ≟∋ i′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
var i     ≟ ⌜λ⌝ t′          = no λ ()
var i     ≟ t₁′ ⌜$⌝ t₂′     = no λ ()
⌜λ⌝ t     ≟ var i′          = no λ ()
⌜λ⌝ t     ≟ ⌜λ⌝ t′          with t ≟ t′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
⌜λ⌝ t     ≟ t₁′ ⌜$⌝ t₂′     = no λ ()
t₁ ⌜$⌝ t₂ ≟ var i′          = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜λ⌝ t′          = no λ ()
t₁ ⌜$⌝ t₂ ≟ t₁′ ⌜$⌝ t₂′     with ty t₁ ≟Ty ty t₁′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                with t₁ ≟ t₁′ | t₂ ≟ t₂′
...   | no ¬eq₁  | _            = no λ { refl → refl ↯ ¬eq₁ }
...   | yes refl | no ¬eq₂      = no λ { refl → refl ↯ ¬eq₂ }
...   | yes refl | yes refl     = yes refl


----------------------------------------------------------------------------------------------------

injv : ∀ {Γ A} {i i′ : Γ ∋ A} → var i ≡ var i′ → i ≡ i′
injv refl = refl

injλ : ∀ {Γ A B} {t t′ : A ∷ Γ ⊢ B} → ⌜λ⌝ t ≡ ⌜λ⌝ t′ → t ≡ t′
injλ refl = refl

inj$₁ : ∀ {Γ A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} → t₁ ⌜$⌝ t₂ ≡ t₁′ ⌜$⌝ t₂′ → t₁ ≡ t₁′
inj$₁ refl = refl

inj$₂ : ∀ {Γ A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} → t₁ ⌜$⌝ t₂ ≡ t₁′ ⌜$⌝ t₂′ → t₂ ≡ t₂′
inj$₂ refl = refl

inj$₁′ : ∀ {Γ A A′ B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} {t₁′ : Γ ⊢ A′ ⌜⊃⌝ B} {t₂′ : Γ ⊢ A′} →
         t₁ ⌜$⌝ t₂ ≡ t₁′ ⌜$⌝ t₂′ → Σ (A ≡ A′) λ { refl → t₁ ≡ t₁′ }
inj$₁′ refl = refl , refl

inj$₂′ : ∀ {Γ A A′ B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} {t₁′ : Γ ⊢ A′ ⌜⊃⌝ B} {t₂′ : Γ ⊢ A′} →
         t₁ ⌜$⌝ t₂ ≡ t₁′ ⌜$⌝ t₂′ → Σ (A ≡ A′) λ { refl → t₂ ≡ t₂′ }
inj$₂′ refl = refl , refl

injren : ∀ {Γ Γ′ A} {e : Γ ⊆ Γ′} {t t′ : Γ ⊢ A} → ren e t ≡ ren e t′ → t ≡ t′
injren {t = var i}     {var i′}      eq = var & injren∋ (injv eq)
injren {t = ⌜λ⌝ t}     {⌜λ⌝ t′}      eq = ⌜λ⌝ & injren (injλ eq)
injren {t = t₁ ⌜$⌝ t₂} {t₁′ ⌜$⌝ t₂′} eq with inj$₁′ eq
... | refl , eq₁                          = _⌜$⌝_ & injren eq₁ ⊗ injren (inj$₂ eq)


----------------------------------------------------------------------------------------------------

-- TODO: delete?
unren : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (t′ : Γ′ ⊢ A) → Dec (Σ (Γ ⊢ A) λ t → t′ ≡ ren e t)
unren e (var i′)                        with unren∋ e i′
... | no ¬p                               = no λ { (var i , refl) → (i , refl) ↯ ¬p }
... | yes (i , refl)                      = yes (var i , refl)
unren e (⌜λ⌝ t′)                        with unren (keep e) t′
... | no ¬p                               = no λ { (⌜λ⌝ t , refl) → (t , refl) ↯ ¬p }
... | yes (t , refl)                      = yes (⌜λ⌝ t , refl)
unren e (t₁′ ⌜$⌝ t₂′)                   with unren e t₁′ | unren e t₂′
... | no ¬p₁          | _                 = no λ { (t₁ ⌜$⌝ t₂ , refl) → (t₁ , refl) ↯ ¬p₁ }
... | yes (t₁ , eq₁)  | no ¬p₂            = no λ { (t₁ ⌜$⌝ t₂ , refl) → (t₂ , refl) ↯ ¬p₂ }
... | yes (t₁ , refl) | yes (t₂ , refl)   = yes (t₁ ⌜$⌝ t₂ , refl)


----------------------------------------------------------------------------------------------------
