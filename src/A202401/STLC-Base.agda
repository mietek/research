----------------------------------------------------------------------------------------------------

-- simply typed lambda calculus with base type only

module A202401.STLC-Base where

open import A202401.Kit1 public


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
  ⌜λ⌝   : ∀ {A B} (t : Γ , A ⊢ B) → Γ ⊢ A ⌜⊃⌝ B
  _⌜$⌝_ : ∀ {A B} (t₁ : Γ ⊢ A ⌜⊃⌝ B) (t₂ : Γ ⊢ A) → Γ ⊢ B

open TmKit (kit _⊢_) public


----------------------------------------------------------------------------------------------------

ren : ∀ {Γ Γ′ A} → Γ ⊑ Γ′ → Γ ⊢ A → Γ′ ⊢ A
ren ϱ (var i)     = var (ren∋ ϱ i)
ren ϱ (⌜λ⌝ t)     = ⌜λ⌝ (ren (lift⊑ ϱ) t)
ren ϱ (t₁ ⌜$⌝ t₂) = ren ϱ t₁ ⌜$⌝ ren ϱ t₂

open RenKit (kit var ren) public

sub : ∀ {Γ Ξ A} → Ξ ⊢§ Γ → Γ ⊢ A → Ξ ⊢ A
sub σ (var i)     = sub∋ σ i
sub σ (⌜λ⌝ t)     = ⌜λ⌝ (sub (lift§ σ) t)
sub σ (t₁ ⌜$⌝ t₂) = sub σ t₁ ⌜$⌝ sub σ t₂

open SubKit (kit renkit sub) public


----------------------------------------------------------------------------------------------------

module BetaShortDefEq where
  infix 4 _≝_
  data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    refl≝  : ∀ {A} {t : Γ ⊢ A} → t ≝ t
    sym≝   : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
    trans≝ : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
    congλ  : ∀ {A B} {t t′ : Γ , A ⊢ B} (eq : t ≝ t′) → ⌜λ⌝ t ≝ ⌜λ⌝ t′
    cong$  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
             t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
    βred⊃  : ∀ {A B} {t₁ : Γ , A ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) →
             ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′

  open DefEqKit (kit tmkit (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝) public

module BetaShortEtaLongDefEq where
  infix 4 _≝_
  data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    refl≝  : ∀ {A} {t : Γ ⊢ A} → t ≝ t
    sym≝   : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
    trans≝ : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
    congλ  : ∀ {A B} {t t′ : Γ , A ⊢ B} (eq : t ≝ t′) → ⌜λ⌝ t ≝ ⌜λ⌝ t′
    cong$  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
             t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
    βred⊃  : ∀ {A B} {t₁ : Γ , A ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) →
             ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
    ηexp⊃  : ∀ {A B} {t : Γ ⊢ A ⌜⊃⌝ B} {t′} (eq : t′ ≡ wk t) → t ≝ ⌜λ⌝ (t′ ⌜$⌝ var zero)

  open DefEqKit (kit tmkit (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝) public


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

-- TODO: delete?

injv : ∀ {Γ A} {i i′ : Γ ∋ A} → var i ≡ var i′ → i ≡ i′
injv refl = refl

injλ : ∀ {Γ A B} {t t′ : Γ , A ⊢ B} → ⌜λ⌝ t ≡ ⌜λ⌝ t′ → t ≡ t′
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

injren : ∀ {Γ Γ′ A} {ϱ : Γ ⊑ Γ′} {t t′ : Γ ⊢ A} → ren ϱ t ≡ ren ϱ t′ → t ≡ t′
injren {t = var i}     {var i′}      eq = var & injren∋ (injvar eq)
injren {t = ⌜λ⌝ t}     {⌜λ⌝ t′}      eq = ⌜λ⌝ & injren (injλ eq)
injren {t = t₁ ⌜$⌝ t₂} {t₁′ ⌜$⌝ t₂′} eq with inj$₁′ eq
... | refl , eq₁                          = _⌜$⌝_ & injren eq₁ ⊗ injren (inj$₂ eq)

unren : ∀ {Γ Γ′ A} (ϱ : Γ ⊑ Γ′) (t′ : Γ′ ⊢ A) → Dec (Σ (Γ ⊢ A) λ t → t′ ≡ ren ϱ t)
unren ϱ (var i′)                        with unren∋ ϱ i′
... | no ¬p                               = no λ { (var i , refl) → (i , refl) ↯ ¬p }
... | yes (i , refl)                      = yes (var i , refl)
unren ϱ (⌜λ⌝ t′)                        with unren (lift⊑ ϱ) t′
... | no ¬p                               = no λ { (⌜λ⌝ t , refl) → (t , refl) ↯ ¬p }
... | yes (t , refl)                      = yes (⌜λ⌝ t , refl)
unren ϱ (t₁′ ⌜$⌝ t₂′)                   with unren ϱ t₁′ | unren ϱ t₂′
... | no ¬p₁          | _                 = no λ { (t₁ ⌜$⌝ t₂ , refl) → (t₁ , refl) ↯ ¬p₁ }
... | yes (t₁ , eq₁)  | no ¬p₂            = no λ { (t₁ ⌜$⌝ t₂ , refl) → (t₂ , refl) ↯ ¬p₂ }
... | yes (t₁ , refl) | yes (t₂ , refl)   = yes (t₁ ⌜$⌝ t₂ , refl)


----------------------------------------------------------------------------------------------------
