module STLC-Naturals where

open import Common public


----------------------------------------------------------------------------------------------------

-- types
infixr 18 _`⊃_
data Ty : Set where
  _`⊃_ : ∀ (A B : Ty) → Ty
  `ℕ   : Ty

open CtxKit Ty public

-- intrinsically well-typed terms
infix 3 _⊢_
infixl 18 _`$_
data _⊢_ (Γ : Ctx) : Ty → Set where
  `v    : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  `λ    : ∀ {A B} (t : A ∷ Γ ⊢ B) → Γ ⊢ A `⊃ B
  _`$_  : ∀ {A B} (t₁ : Γ ⊢ A `⊃ B) (t₂ : Γ ⊢ A) → Γ ⊢ B
  `zero : Γ ⊢ `ℕ
  `suc  : ∀ (t : Γ ⊢ `ℕ) → Γ ⊢ `ℕ
  `rec  : ∀ {A} (t₁ : Γ ⊢ `ℕ) (t₂ : Γ ⊢ A) (t₃ : A ∷ `ℕ ∷ Γ ⊢ A) → Γ ⊢ A

open ⊢*Kit _⊢_ public

-- renaming
ren : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
ren e (`v i)          = `v (ren∋ e i)
ren e (`λ t)          = `λ (ren (keep e) t)
ren e (t₁ `$ t₂)      = ren e t₁ `$ ren e t₂
ren e `zero           = `zero
ren e (`suc t)        = `suc (ren e t)
ren e (`rec t₁ t₂ t₃) = `rec (ren e t₁) (ren e t₂) (ren (keep (keep e)) t₃)

open RenKit `v ren public

-- substitution
sub : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ⊢ A → Ξ ⊢ A
sub ss (`v i)          = sub∋ ss i
sub ss (`λ t)          = `λ (sub (lift* ss) t)
sub ss (t₁ `$ t₂)      = sub ss t₁ `$ sub ss t₂
sub ss `zero           = `zero
sub ss (`suc t)        = `suc (sub ss t)
sub ss (`rec t₁ t₂ t₃) = `rec (sub ss t₁) (sub ss t₂) (sub (lift* (lift* ss)) t₃)

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
_≟_ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Dec (t ≡ t′)
`v i          ≟ `v i′                with i ≟∋ i′
... | no ¬eq                           = no λ { refl → refl ↯ ¬eq }
... | yes refl                         = yes refl
`v i          ≟ `λ t′                = no λ ()
`v i          ≟ t₁′ `$ t₂′           = no λ ()
`v i          ≟ `zero                = no λ ()
`v i          ≟ `suc t′              = no λ ()
`v i          ≟ `rec t₁′ t₂′ t₃′     = no λ ()
`λ t          ≟ `v i′                = no λ ()
`λ t          ≟ `λ t′                with t ≟ t′
... | no ¬eq                           = no λ { refl → refl ↯ ¬eq }
... | yes refl                         = yes refl
`λ t          ≟ t₁′ `$ t₂′           = no λ ()
`λ t          ≟ `rec t₁′ t₂′ t₃′     = no λ ()
t₁ `$ t₂      ≟ `v i′                = no λ ()
t₁ `$ t₂      ≟ `λ t′                = no λ ()
t₁ `$ t₂      ≟ t₁′ `$ t₂′           with ty t₁ ≟T ty t₁′
... | no ¬eq                           = no λ { refl → refl ↯ ¬eq }
... | yes refl                         with t₁ ≟ t₁′ | t₂ ≟ t₂′
...   | no ¬eq₁  | _                     = no λ { refl → refl ↯ ¬eq₁ }
...   | yes refl | no ¬eq₂               = no λ { refl → refl ↯ ¬eq₂ }
...   | yes refl | yes refl              = yes refl
t₁ `$ t₂      ≟ `zero                = no λ ()
t₁ `$ t₂      ≟ `suc t′              = no λ ()
t₁ `$ t₂      ≟ `rec t₁′ t₂′ t₃′     = no λ ()
`zero         ≟ `v i                 = no λ ()
`zero         ≟ t₁′ `$ t₂′           = no λ ()
`zero         ≟ `zero                = yes refl
`zero         ≟ `suc t′              = no λ ()
`zero         ≟ `rec t₁′ t₂′ t₃′     = no λ ()
`suc t        ≟ `v i                 = no λ ()
`suc t        ≟ t₁′ `$ t₂′           = no λ ()
`suc t        ≟ `zero                = no λ ()
`suc t        ≟ `suc t′              with t ≟ t′
... | no ¬eq                           = no λ { refl → refl ↯ ¬eq }
... | yes refl                         = yes refl
`suc t        ≟ `rec t₁′ t₂′ t₃′     = no λ ()
`rec t₁ t₂ t₃ ≟ `v i                 = no λ ()
`rec t₁ t₂ t₃ ≟ `λ t′                = no λ ()
`rec t₁ t₂ t₃ ≟ t₁′ `$ t₂′           = no λ ()
`rec t₁ t₂ t₃ ≟ `zero                = no λ ()
`rec t₁ t₂ t₃ ≟ `suc t′              = no λ ()
`rec t₁ t₂ t₃ ≟ `rec t₁′ t₂′ t₃′     with t₁ ≟ t₁′ | t₂ ≟ t₂′ | t₃ ≟ t₃′
... | no ¬eq₁  | _        | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂  | _          = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl | no ¬eq₃    = no λ { refl → refl ↯ ¬eq₃ }
... | yes refl | yes refl | yes refl   = yes refl


----------------------------------------------------------------------------------------------------
