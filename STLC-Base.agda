module STLC-Base where

open import Common public


----------------------------------------------------------------------------------------------------

-- types
infixr 18 _⌜⊃⌝_
data Ty : Set where
  ⌜◦⌝   : Ty
  _⌜⊃⌝_ : ∀ (A B : Ty) → Ty

open CtxKit Ty public

-- intrinsically well-typed terms
infix 3 _⊢_
infixl 18 _⌜$⌝_
data _⊢_ (Γ : Ctx) : Ty → Set where
  ⌜v⌝   : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  ⌜λ⌝   : ∀ {A B} (t : A ∷ Γ ⊢ B) → Γ ⊢ A ⌜⊃⌝ B
  _⌜$⌝_ : ∀ {A B} (t₁ : Γ ⊢ A ⌜⊃⌝ B) (t₂ : Γ ⊢ A) → Γ ⊢ B

open ⊢*Kit _⊢_ public

-- renaming
ren : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
ren e (⌜v⌝ i)     = ⌜v⌝ (ren∋ e i)
ren e (⌜λ⌝ t)     = ⌜λ⌝ (ren (keep e) t)
ren e (t₁ ⌜$⌝ t₂) = ren e t₁ ⌜$⌝ ren e t₂

open RenKit ⌜v⌝ ren public

-- substitution
sub : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ⊢ A → Ξ ⊢ A
sub ss (⌜v⌝ i)     = sub∋ ss i
sub ss (⌜λ⌝ t)     = ⌜λ⌝ (sub (lift* ss) t)
sub ss (t₁ ⌜$⌝ t₂) = sub ss t₁ ⌜$⌝ sub ss t₂

open SubKit sub public


----------------------------------------------------------------------------------------------------

-- decidable equality
infix 4 _≟T_
_≟T_ : ∀ (A A′ : Ty) → Dec (A ≡ A′)
⌜◦⌝     ≟T ⌜◦⌝            = yes refl
⌜◦⌝     ≟T A′ ⌜⊃⌝ B′      = no λ ()
A ⌜⊃⌝ B ≟T ⌜◦⌝            = no λ ()
A ⌜⊃⌝ B ≟T A′ ⌜⊃⌝ B′      with A ≟T A′ | B ≟T B′
... | no ¬eq₁  | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂    = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl   = yes refl

infix 4 _≟_
_≟_ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Dec (t ≡ t′)
⌜v⌝ i     ≟ ⌜v⌝ i′          with i ≟∋ i′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
⌜v⌝ i     ≟ ⌜λ⌝ t′          = no λ ()
⌜v⌝ i     ≟ t₁′ ⌜$⌝ t₂′     = no λ ()
⌜λ⌝ t     ≟ ⌜v⌝ i′          = no λ ()
⌜λ⌝ t     ≟ ⌜λ⌝ t′          with t ≟ t′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
⌜λ⌝ t     ≟ t₁′ ⌜$⌝ t₂′     = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜v⌝ i′          = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜λ⌝ t′          = no λ ()
t₁ ⌜$⌝ t₂ ≟ t₁′ ⌜$⌝ t₂′     with ty t₁ ≟T ty t₁′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                with t₁ ≟ t₁′ | t₂ ≟ t₂′
...   | no ¬eq₁  | _            = no λ { refl → refl ↯ ¬eq₁ }
...   | yes refl | no ¬eq₂      = no λ { refl → refl ↯ ¬eq₂ }
...   | yes refl | yes refl     = yes refl


----------------------------------------------------------------------------------------------------
