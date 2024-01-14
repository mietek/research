module STLC-Base where

open import Common public


----------------------------------------------------------------------------------------------------

-- NOTE: apparently having an inaccessible base type causes many more inference failures
infixr 18 _`⊃_
data Ty : Set where
  `∙   : Ty
  _`⊃_ : ∀ (A B : Ty) → Ty

open CtxKit Ty public

-- intrinsically well-typed terms
infix 3 _⊢_
infixl 18 _`$_
data _⊢_ (Γ : Ctx) : ∀ (A : Ty) → Set where
  `v   : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  `λ   : ∀ {A B} (d : A ∷ Γ ⊢ B) → Γ ⊢ A `⊃ B
  _`$_ : ∀ {A B} (d₁ : Γ ⊢ A `⊃ B) (d₂ : Γ ⊢ A) → Γ ⊢ B

open ⊢*Kit _⊢_ public

-- renaming
ren : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (d : Γ ⊢ A) → Γ′ ⊢ A
ren e (`v i)     = `v (ren∋ e i)
ren e (`λ d)     = `λ (ren (keep e) d)
ren e (d₁ `$ d₂) = ren e d₁ `$ ren e d₂

open RenKit `v ren public

-- substitution
sub : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (d : Γ ⊢ A) → Ξ ⊢ A
sub ss (`v i)     = sub∋ ss i
sub ss (`λ d)     = `λ (sub (lift* ss) d)
sub ss (d₁ `$ d₂) = sub ss d₁ `$ sub ss d₂

open SubKit sub public


----------------------------------------------------------------------------------------------------

infix 4 _≟T_
_≟T_ : ∀ (A A′ : Ty) → Dec (A ≡ A′)
`∙     ≟T `∙              = yes refl
`∙     ≟T A′ `⊃ B′        = no λ ()
A `⊃ B ≟T `∙              = no λ ()
A `⊃ B ≟T A′ `⊃ B′        with A ≟T A′ | B ≟T B′
... | no ¬eq₁  | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂    = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl   = yes refl

infix 4 _≟_
_≟_ : ∀ {Γ A} (d d′ : Γ ⊢ A) → Dec (d ≡ d′)
`v i               ≟ `v i′                 with i ≟∋ i′
... | no ¬eq                                 = no λ { refl → refl ↯ ¬eq }
... | yes refl                               = yes refl
`v i               ≟ `λ d′                 = no λ ()
`v i               ≟ d₁′ `$ d₂′            = no λ ()
`λ d               ≟ `v i′                 = no λ ()
`λ d               ≟ `λ d′                 with d ≟ d′
... | no ¬eq                                 = no λ { refl → refl ↯ ¬eq }
... | yes refl                               = yes refl
`λ d               ≟ d₁′ `$ d₂′            = no λ ()
d₁ `$ d₂           ≟ `v i′                 = no λ ()
d₁ `$ d₂           ≟ `λ d′                 = no λ ()
_`$_ {A = A} d₁ d₂ ≟ _`$_ {A = A′} d₁′ d₂′ with A ≟T A′
... | no ¬eq                                 = no λ { refl → refl ↯ ¬eq }
... | yes refl                               with d₁ ≟ d₁′ | d₂ ≟ d₂′
...   | no ¬eq₁  | _                           = no λ { refl → refl ↯ ¬eq₁ }
...   | yes refl | no ¬eq₂                     = no λ { refl → refl ↯ ¬eq₂ }
...   | yes refl | yes refl                    = yes refl


----------------------------------------------------------------------------------------------------
