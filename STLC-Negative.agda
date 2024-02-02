module STLC-Negative where

open import Kit1 public


----------------------------------------------------------------------------------------------------

infixr 18 _⌜⊃⌝_
infixl 19 _⌜∧⌝_
data Ty : Set where
  _⌜⊃⌝_ : ∀ (A B : Ty) → Ty
  _⌜∧⌝_ : ∀ (A B : Ty) → Ty
  ⌜𝟙⌝   : Ty

infixr 18 _`⫗_
_`⫗_ : ∀ (A B : Ty) → Ty
A `⫗ B = (A ⌜⊃⌝ B) ⌜∧⌝ (B ⌜⊃⌝ A)

open TyKit Ty public

infix 3 _⊢_
infixl 18 _⌜$⌝_
data _⊢_ (Γ : Ctx) : Ty → Set where
  var     : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  ⌜λ⌝     : ∀ {A B} (t : A ∷ Γ ⊢ B) → Γ ⊢ A ⌜⊃⌝ B
  _⌜$⌝_   : ∀ {A B} (t₁ : Γ ⊢ A ⌜⊃⌝ B) (t₂ : Γ ⊢ A) → Γ ⊢ B
  _⌜,⌝_   : ∀ {A B} (t₁ : Γ ⊢ A) (t₂ : Γ ⊢ B) → Γ ⊢ A ⌜∧⌝ B
  ⌜proj₁⌝ : ∀ {A B} (t : Γ ⊢ A ⌜∧⌝ B) → Γ ⊢ A
  ⌜proj₂⌝ : ∀ {A B} (t : Γ ⊢ A ⌜∧⌝ B) → Γ ⊢ B
  ⌜unit⌝  : Γ ⊢ ⌜𝟙⌝

tk! = tmkit _⊢_
open TmKit tk! public


----------------------------------------------------------------------------------------------------

ren : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
ren e (var i)     = var (ren∋ e i)
ren e (⌜λ⌝ t)     = ⌜λ⌝ (ren (keep e) t)
ren e (t₁ ⌜$⌝ t₂) = ren e t₁ ⌜$⌝ ren e t₂
ren e (t₁ ⌜,⌝ t₂) = ren e t₁ ⌜,⌝ ren e t₂
ren e (⌜proj₁⌝ t) = ⌜proj₁⌝ (ren e t)
ren e (⌜proj₂⌝ t) = ⌜proj₂⌝ (ren e t)
ren e ⌜unit⌝      = ⌜unit⌝

rk! = renkit var ren
open RenKit rk! public

sub : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ⊢ A → Ξ ⊢ A
sub ss (var i)     = sub∋ ss i
sub ss (⌜λ⌝ t)     = ⌜λ⌝ (sub (lifts ss) t)
sub ss (t₁ ⌜$⌝ t₂) = sub ss t₁ ⌜$⌝ sub ss t₂
sub ss (t₁ ⌜,⌝ t₂) = sub ss t₁ ⌜,⌝ sub ss t₂
sub ss (⌜proj₁⌝ t) = ⌜proj₁⌝ (sub ss t)
sub ss (⌜proj₂⌝ t) = ⌜proj₂⌝ (sub ss t)
sub ss ⌜unit⌝      = ⌜unit⌝

sk! = subkit rk! sub
open SubKit sk! public


----------------------------------------------------------------------------------------------------

-- definitional equality
module BetaShort where
  infix 4 _≝_
  data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    refl≝     : ∀ {A} {t : Γ ⊢ A} → t ≝ t
    sym≝      : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
    trans≝    : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
    congλ     : ∀ {A B} {t t′ : A ∷ Γ ⊢ B} (eq : t ≝ t′) → ⌜λ⌝ t ≝ ⌜λ⌝ t′
    cong$     : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
                t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
    cong,     : ∀ {A B} {t₁ t₁′ : Γ ⊢ A} {t₂ t₂′ : Γ ⊢ B} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
                t₁ ⌜,⌝ t₂ ≝ t₁′ ⌜,⌝ t₂′
    congproj₁ : ∀ {A B} {t t′ : Γ ⊢ A ⌜∧⌝ B} (eq : t ≝ t′) → ⌜proj₁⌝ t ≝ ⌜proj₁⌝ t′
    congproj₂ : ∀ {A B} {t t′ : Γ ⊢ A ⌜∧⌝ B} (eq : t ≝ t′) → ⌜proj₂⌝ t ≝ ⌜proj₂⌝ t′
    βred⊃     : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) →
                ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
    βred∧₁    : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → ⌜proj₁⌝ (t₁ ⌜,⌝ t₂) ≝ t₁
    βred∧₂    : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → ⌜proj₂⌝ (t₁ ⌜,⌝ t₂) ≝ t₂

  dek! = defeqkit tk! (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝
  open DefEqKit dek! public

module BetaShortEtaLong where
  infix 4 _≝_
  data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    refl≝     : ∀ {A} {t : Γ ⊢ A} → t ≝ t
    sym≝      : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
    trans≝    : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
    congλ     : ∀ {A B} {t t′ : A ∷ Γ ⊢ B} (eq : t ≝ t′) → ⌜λ⌝ t ≝ ⌜λ⌝ t′
    cong$     : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
                t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
    cong,     : ∀ {A B} {t₁ t₁′ : Γ ⊢ A} {t₂ t₂′ : Γ ⊢ B} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
                t₁ ⌜,⌝ t₂ ≝ t₁′ ⌜,⌝ t₂′
    congproj₁ : ∀ {A B} {t t′ : Γ ⊢ A ⌜∧⌝ B} (eq : t ≝ t′) → ⌜proj₁⌝ t ≝ ⌜proj₁⌝ t′
    congproj₂ : ∀ {A B} {t t′ : Γ ⊢ A ⌜∧⌝ B} (eq : t ≝ t′) → ⌜proj₂⌝ t ≝ ⌜proj₂⌝ t′
    βred⊃     : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) →
                ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
    βred∧₁    : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → ⌜proj₁⌝ (t₁ ⌜,⌝ t₂) ≝ t₁
    βred∧₂    : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → ⌜proj₂⌝ (t₁ ⌜,⌝ t₂) ≝ t₂
    ηexp⊃     : ∀ {A B} {t : Γ ⊢ A ⌜⊃⌝ B} {t′} (eq : t′ ≡ wk t) → t ≝ ⌜λ⌝ (t′ ⌜$⌝ var zero)
    ηexp,     : ∀ {A B} {t : Γ ⊢ A ⌜∧⌝ B} → t ≝ (⌜proj₁⌝ t) ⌜,⌝ (⌜proj₂⌝ t)
    ηexp𝟙     : ∀ {t : Γ ⊢ ⌜𝟙⌝} → t ≝ ⌜unit⌝

  dek! = defeqkit tk! (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝
  open DefEqKit dek! public


----------------------------------------------------------------------------------------------------

infix 4 _≟Ty_
_≟Ty_ : ∀ (A A′ : Ty) → Dec (A ≡ A′)
A ⌜⊃⌝ B ≟Ty A′ ⌜⊃⌝ B′     with A ≟Ty A′ | B ≟Ty B′
... | no ¬eq₁  | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂    = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl   = yes refl
A ⌜⊃⌝ B ≟Ty A′ ⌜∧⌝ B′     = no λ ()
A ⌜⊃⌝ B ≟Ty ⌜𝟙⌝           = no λ ()
A ⌜∧⌝ B ≟Ty A′ ⌜⊃⌝ B′     = no λ ()
A ⌜∧⌝ B ≟Ty A′ ⌜∧⌝ B′     with A ≟Ty A′ | B ≟Ty B′
... | no ¬eq₁  | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂    = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl   = yes refl
A ⌜∧⌝ B ≟Ty ⌜𝟙⌝           = no λ ()
⌜𝟙⌝     ≟Ty A′ ⌜⊃⌝ B′     = no λ ()
⌜𝟙⌝     ≟Ty A′ ⌜∧⌝ B′     = no λ ()
⌜𝟙⌝     ≟Ty ⌜𝟙⌝           = yes refl

infix 4 _≟_
_≟_ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Dec (t ≡ t′)
var i     ≟ var i′          with i ≟∋ i′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
var i     ≟ ⌜λ⌝ t′            = no λ ()
var i     ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
var i     ≟ t₁′ ⌜,⌝ t₂′       = no λ ()
var i     ≟ ⌜proj₁⌝ t′        = no λ ()
var i     ≟ ⌜proj₂⌝ t′        = no λ ()
var i     ≟ ⌜unit⌝            = no λ ()
⌜λ⌝ t     ≟ var i′            = no λ ()
⌜λ⌝ t     ≟ ⌜λ⌝ t′          with t ≟ t′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
⌜λ⌝ t     ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
⌜λ⌝ t     ≟ ⌜proj₁⌝ t′        = no λ ()
⌜λ⌝ t     ≟ ⌜proj₂⌝ t′        = no λ ()
t₁ ⌜$⌝ t₂ ≟ var i′            = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜λ⌝ t′            = no λ ()
t₁ ⌜$⌝ t₂ ≟ t₁′ ⌜$⌝ t₂′     with ty t₁ ≟Ty ty t₁′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                with t₁ ≟ t₁′ | t₂ ≟ t₂′
...   | no ¬eq₁  | _            = no λ { refl → refl ↯ ¬eq₁ }
...   | yes refl | no ¬eq₂      = no λ { refl → refl ↯ ¬eq₂ }
...   | yes refl | yes refl     = yes refl
t₁ ⌜$⌝ t₂ ≟ t₁′ ⌜,⌝ t₂′       = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜proj₁⌝ t′        = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜proj₂⌝ t′        = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜unit⌝            = no λ ()
t₁ ⌜,⌝ t₂ ≟ var i′            = no λ ()
t₁ ⌜,⌝ t₂ ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
t₁ ⌜,⌝ t₂ ≟ t₁′ ⌜,⌝ t₂′     with t₁ ≟ t₁′ | t₂ ≟ t₂′
... | no ¬eq₁  | _            = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂      = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl     = yes refl
t₁ ⌜,⌝ t₂ ≟ ⌜proj₁⌝ t′        = no λ ()
t₁ ⌜,⌝ t₂ ≟ ⌜proj₂⌝ t′        = no λ ()
⌜proj₁⌝ t ≟ var i′            = no λ ()
⌜proj₁⌝ t ≟ ⌜λ⌝ t′            = no λ ()
⌜proj₁⌝ t ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
⌜proj₁⌝ t ≟ t₁′ ⌜,⌝ t₂′       = no λ ()
⌜proj₁⌝ t ≟ ⌜proj₁⌝ t′      with ty t ≟Ty ty t′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                with t ≟ t′
...   | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
...   | yes refl                = yes refl
⌜proj₁⌝ t ≟ ⌜proj₂⌝ t′        = no λ ()
⌜proj₁⌝ t ≟ ⌜unit⌝            = no λ ()
⌜proj₂⌝ t ≟ var i′            = no λ ()
⌜proj₂⌝ t ≟ ⌜λ⌝ t′            = no λ ()
⌜proj₂⌝ t ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
⌜proj₂⌝ t ≟ t₁′ ⌜,⌝ t₂′       = no λ ()
⌜proj₂⌝ t ≟ ⌜proj₁⌝ t′        = no λ ()
⌜proj₂⌝ t ≟ ⌜proj₂⌝ t′      with ty t ≟Ty ty t′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                with t ≟ t′
...   | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
...   | yes refl                = yes refl
⌜proj₂⌝ t ≟ ⌜unit⌝            = no λ ()
⌜unit⌝    ≟ var i′            = no λ ()
⌜unit⌝    ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
⌜unit⌝    ≟ ⌜proj₁⌝ t′        = no λ ()
⌜unit⌝    ≟ ⌜proj₂⌝ t′        = no λ ()
⌜unit⌝    ≟ ⌜unit⌝            = yes refl


----------------------------------------------------------------------------------------------------
