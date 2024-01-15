module STLC-Negative where

open import Common public


----------------------------------------------------------------------------------------------------

infixr 18 _`⊃_
infixl 19 _`∧_
data Ty : Set where
  _`⊃_ : ∀ (A B : Ty) → Ty
  _`∧_ : ∀ (A B : Ty) → Ty
  `𝟙   : Ty

infixr 18 _`⫗_
_`⫗_ : ∀ (A B : Ty) → Ty
A `⫗ B = (A `⊃ B) `∧ (B `⊃ A)

open CtxKit Ty public

-- intrinsically well-typed terms
infix 3 _⊢_
infixl 18 _`$_
data _⊢_ (Γ : Ctx) : ∀ (A : Ty) → Set where
  `v     : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  `λ     : ∀ {A B} (d : A ∷ Γ ⊢ B) → Γ ⊢ A `⊃ B
  _`$_   : ∀ {A B} (d₁ : Γ ⊢ A `⊃ B) (d₂ : Γ ⊢ A) → Γ ⊢ B
  _`,_   : ∀ {A B} (d₁ : Γ ⊢ A) (d₂ : Γ ⊢ B) → Γ ⊢ A `∧ B
  `proj₁ : ∀ {A B} (d : Γ ⊢ A `∧ B) → Γ ⊢ A
  `proj₂ : ∀ {A B} (d : Γ ⊢ A `∧ B) → Γ ⊢ B
  `unit  : Γ ⊢ `𝟙

open ⊢*Kit _⊢_ public

-- renaming
ren : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (d : Γ ⊢ A) → Γ′ ⊢ A
ren e (`v i)     = `v (ren∋ e i)
ren e (`λ d)     = `λ (ren (keep e) d)
ren e (d₁ `$ d₂) = ren e d₁ `$ ren e d₂
ren e (d₁ `, d₂) = ren e d₁ `, ren e d₂
ren e (`proj₁ d) = `proj₁ (ren e d)
ren e (`proj₂ d) = `proj₂ (ren e d)
ren e `unit      = `unit

open RenKit `v ren public

-- substitution
sub : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (d : Γ ⊢ A) → Ξ ⊢ A
sub ss (`v i)     = sub∋ ss i
sub ss (`λ d)     = `λ (sub (lift* ss) d)
sub ss (d₁ `$ d₂) = sub ss d₁ `$ sub ss d₂
sub ss (d₁ `, d₂) = sub ss d₁ `, sub ss d₂
sub ss (`proj₁ d) = `proj₁ (sub ss d)
sub ss (`proj₂ d) = `proj₂ (sub ss d)
sub ss `unit      = `unit

open SubKit sub public


----------------------------------------------------------------------------------------------------

infix 4 _≟T_
_≟T_ : ∀ (A A′ : Ty) → Dec (A ≡ A′)
A `⊃ B ≟T A′ `⊃ B′        with A ≟T A′ | B ≟T B′
... | no ¬eq₁  | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂    = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl   = yes refl
A `⊃ B ≟T A′ `∧ B′        = no λ ()
A `⊃ B ≟T `𝟙              = no λ ()
A `∧ B ≟T A′ `⊃ B′        = no λ ()
A `∧ B ≟T A′ `∧ B′        with A ≟T A′ | B ≟T B′
... | no ¬eq₁  | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂    = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl   = yes refl
A `∧ B ≟T `𝟙              = no λ ()
`𝟙     ≟T A′ `⊃ B′        = no λ ()
`𝟙     ≟T A′ `∧ B′        = no λ ()
`𝟙     ≟T `𝟙              = yes refl

infix 4 _≟_
_≟_ : ∀ {Γ A} (d d′ : Γ ⊢ A) → Dec (d ≡ d′)
`v i               ≟ `v i′                 with i ≟∋ i′
... | no ¬eq                                 = no λ { refl → refl ↯ ¬eq }
... | yes refl                               = yes refl
`v i               ≟ `λ d′                 = no λ ()
`v i               ≟ d₁′ `$ d₂′            = no λ ()
`v i               ≟ d₁′ `, d₂′            = no λ ()
`v i               ≟ `proj₁ d′             = no λ ()
`v i               ≟ `proj₂ d′             = no λ ()
`v i               ≟ `unit                 = no λ ()
`λ d               ≟ `v i′                 = no λ ()
`λ d               ≟ `λ d′                 with d ≟ d′
... | no ¬eq                                 = no λ { refl → refl ↯ ¬eq }
... | yes refl                               = yes refl
`λ d               ≟ d₁′ `$ d₂′            = no λ ()
`λ d               ≟ `proj₁ d′             = no λ ()
`λ d               ≟ `proj₂ d′             = no λ ()
d₁ `$ d₂           ≟ `v i′                 = no λ ()
d₁ `$ d₂           ≟ `λ d′                 = no λ ()
_`$_ {A = A} d₁ d₂ ≟ _`$_ {A = A′} d₁′ d₂′ with A ≟T A′
... | no ¬eq                                 = no λ { refl → refl ↯ ¬eq }
... | yes refl                               with d₁ ≟ d₁′ | d₂ ≟ d₂′
...   | no ¬eq₁  | _                           = no λ { refl → refl ↯ ¬eq₁ }
...   | yes refl | no ¬eq₂                     = no λ { refl → refl ↯ ¬eq₂ }
...   | yes refl | yes refl                    = yes refl
d₁ `$ d₂           ≟ d₁′ `, d₂′            = no λ ()
d₁ `$ d₂           ≟ `proj₁ d′             = no λ ()
d₁ `$ d₂           ≟ `proj₂ d′             = no λ ()
d₁ `$ d₂           ≟ `unit                 = no λ ()
d₁ `, d₂           ≟ `v i′                 = no λ ()
d₁ `, d₂           ≟ d₁′ `$ d₂′            = no λ ()
d₁ `, d₂           ≟ d₁′ `, d₂′            with d₁ ≟ d₁′ | d₂ ≟ d₂′
... | no ¬eq₁  | _                           = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂                     = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl                    = yes refl
d₁ `, d₂           ≟ `proj₁ d′             = no λ ()
d₁ `, d₂           ≟ `proj₂ d′             = no λ ()
`proj₁ d           ≟ `v i′                 = no λ ()
`proj₁ d           ≟ `λ d′                 = no λ ()
`proj₁ d           ≟ d₁′ `$ d₂′            = no λ ()
`proj₁ d           ≟ d₁′ `, d₂′            = no λ ()
`proj₁ {B = B} d   ≟ `proj₁ {B = B′} d′    with B ≟T B′
... | no ¬eq                                 = no λ { refl → refl ↯ ¬eq }
... | yes refl                               with d ≟ d′
...   | no ¬eq                                 = no λ { refl → refl ↯ ¬eq }
...   | yes refl                               = yes refl
`proj₁ d           ≟ `proj₂ d′             = no λ ()
`proj₁ d           ≟ `unit                 = no λ ()
`proj₂ d           ≟ `v i′                 = no λ ()
`proj₂ d           ≟ `λ d′                 = no λ ()
`proj₂ d           ≟ d₁′ `$ d₂′            = no λ ()
`proj₂ d           ≟ d₁′ `, d₂′            = no λ ()
`proj₂ d           ≟ `proj₁ d′             = no λ ()
`proj₂ {A = A} d   ≟ `proj₂ {A = A′} d′    with A ≟T A′
... | no ¬eq                                 = no λ { refl → refl ↯ ¬eq }
... | yes refl                               with d ≟ d′
...   | no ¬eq                                 = no λ { refl → refl ↯ ¬eq }
...   | yes refl                               = yes refl
`proj₂ d           ≟ `unit                 = no λ ()
`unit              ≟ `v i′                 = no λ ()
`unit              ≟ d₁′ `$ d₂′            = no λ ()
`unit              ≟ `proj₁ d′             = no λ ()
`unit              ≟ `proj₂ d′             = no λ ()
`unit              ≟ `unit                 = yes refl


----------------------------------------------------------------------------------------------------
