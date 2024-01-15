module STLC-Naturals where

open import Common public


----------------------------------------------------------------------------------------------------

infixr 18 _`⊃_
data Ty : Set where
  _`⊃_ : ∀ (A B : Ty) → Ty
  `ℕ   : Ty

open CtxKit Ty public

-- intrinsically well-typed terms
infix 3 _⊢_
infixl 18 _`$_
data _⊢_ (Γ : Ctx) : ∀ (A : Ty) → Set where
  `v    : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  `λ    : ∀ {A B} (d : A ∷ Γ ⊢ B) → Γ ⊢ A `⊃ B
  _`$_  : ∀ {A B} (d₁ : Γ ⊢ A `⊃ B) (d₂ : Γ ⊢ A) → Γ ⊢ B
  `zero : Γ ⊢ `ℕ
  `suc  : ∀ (d : Γ ⊢ `ℕ) → Γ ⊢ `ℕ
  `rec  : ∀ {A} (d₁ : Γ ⊢ `ℕ) (d₂ : Γ ⊢ A) (d₃ : A ∷ `ℕ ∷ Γ ⊢ A) → Γ ⊢ A

open ⊢*Kit _⊢_ public

-- renaming
ren : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (d : Γ ⊢ A) → Γ′ ⊢ A
ren e (`v i)          = `v (ren∋ e i)
ren e (`λ d)          = `λ (ren (keep e) d)
ren e (d₁ `$ d₂)      = ren e d₁ `$ ren e d₂
ren e `zero           = `zero
ren e (`suc d)        = `suc (ren e d)
ren e (`rec d₁ d₂ d₃) = `rec (ren e d₁) (ren e d₂) (ren (keep (keep e)) d₃)

open RenKit `v ren public

-- substitution
sub : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (d : Γ ⊢ A) → Ξ ⊢ A
sub ss (`v i)          = sub∋ ss i
sub ss (`λ d)          = `λ (sub (lift* ss) d)
sub ss (d₁ `$ d₂)      = sub ss d₁ `$ sub ss d₂
sub ss `zero           = `zero
sub ss (`suc d)        = `suc (sub ss d)
sub ss (`rec d₁ d₂ d₃) = `rec (sub ss d₁) (sub ss d₂) (sub (lift* (lift* ss)) d₃)

open SubKit sub public


----------------------------------------------------------------------------------------------------

infix 4 _≟T_
_≟T_ : ∀ (A A′ : Ty) → Dec (A ≡ A′)
A `⊃ B ≟T A′ `⊃ B′        with A ≟T A′ | B ≟T B′
... | no ¬eq₁  | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂    = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl   = yes refl
A `⊃ B ≟T `ℕ              = no λ ()
`ℕ     ≟T A′ `⊃ B         = no λ ()
`ℕ     ≟T `ℕ              = yes refl

infix 4 _≟_
_≟_ : ∀ {Γ A} (d d′ : Γ ⊢ A) → Dec (d ≡ d′)
`v i               ≟ `v i′                 with i ≟∋ i′
... | no ¬eq                                 = no λ { refl → refl ↯ ¬eq }
... | yes refl                               = yes refl
`v i               ≟ `λ d′                 = no λ ()
`v i               ≟ d₁′ `$ d₂′            = no λ ()
`v i               ≟ `zero                 = no λ ()
`v i               ≟ `suc d′               = no λ ()
`v i               ≟ `rec d₁′ d₂′ d₃′      = no λ ()
`λ d               ≟ `v i′                 = no λ ()
`λ d               ≟ `λ d′                 with d ≟ d′
... | no ¬eq                                 = no λ { refl → refl ↯ ¬eq }
... | yes refl                               = yes refl
`λ d               ≟ d₁′ `$ d₂′            = no λ ()
`λ d               ≟ `rec d₁′ d₂′ d₃′      = no λ ()
d₁ `$ d₂           ≟ `v i′                 = no λ ()
d₁ `$ d₂           ≟ `λ d′                 = no λ ()
_`$_ {A = A} d₁ d₂ ≟ _`$_ {A = A′} d₁′ d₂′ with A ≟T A′
... | no ¬eq                                 = no λ { refl → refl ↯ ¬eq }
... | yes refl                               with d₁ ≟ d₁′ | d₂ ≟ d₂′
...   | no ¬eq₁  | _                           = no λ { refl → refl ↯ ¬eq₁ }
...   | yes refl | no ¬eq₂                     = no λ { refl → refl ↯ ¬eq₂ }
...   | yes refl | yes refl                    = yes refl
d₁ `$ d₂           ≟ `zero                 = no λ ()
d₁ `$ d₂           ≟ `suc d′               = no λ ()
d₁ `$ d₂           ≟ `rec d₁′ d₂′ d₃′      = no λ ()
`zero              ≟ `v i                  = no λ ()
`zero              ≟ d₁′ `$ d₂′            = no λ ()
`zero              ≟ `zero                 = yes refl
`zero              ≟ `suc d′               = no λ ()
`zero              ≟ `rec d₁′ d₂′ d₃′      = no λ ()
`suc d             ≟ `v i                  = no λ ()
`suc d             ≟ d₁′ `$ d₂′            = no λ ()
`suc d             ≟ `zero                 = no λ ()
`suc d             ≟ `suc d′               with d ≟ d′
... | no ¬eq                                 = no λ { refl → refl ↯ ¬eq }
... | yes refl                               = yes refl
`suc d             ≟ `rec d₁′ d₂′ d₃′      = no λ ()
`rec d₁ d₂ d₃      ≟ `v i                  = no λ ()
`rec d₁ d₂ d₃      ≟ `λ d′                 = no λ ()
`rec d₁ d₂ d₃      ≟ d₁′ `$ d₂′            = no λ ()
`rec d₁ d₂ d₃      ≟ `zero                 = no λ ()
`rec d₁ d₂ d₃      ≟ `suc d′               = no λ ()
`rec d₁ d₂ d₃      ≟ `rec d₁′ d₂′ d₃′      with d₁ ≟ d₁′ | d₂ ≟ d₂′ | d₃ ≟ d₃′
... | no ¬eq₁  | _        | _                = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂  | _                = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl | no ¬eq₃          = no λ { refl → refl ↯ ¬eq₃ }
... | yes refl | yes refl | yes refl         = yes refl


----------------------------------------------------------------------------------------------------
