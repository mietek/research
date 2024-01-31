module STLC-Naturals2 where

open import Common public


----------------------------------------------------------------------------------------------------

-- types
infixr 18 _⌜⊃⌝_
data Ty : Set where
  _⌜⊃⌝_ : ∀ (A B : Ty) → Ty
  ⌜ℕ⌝   : Ty

open CtxKit Ty public


----------------------------------------------------------------------------------------------------

-- constants
data Con : Ty → Set where
  ⌜zero⌝ : Con ⌜ℕ⌝
  ⌜suc⌝  : Con (⌜ℕ⌝ ⌜⊃⌝ ⌜ℕ⌝)
  ⌜rec⌝  : ∀ {A} → Con (⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ (⌜ℕ⌝ ⌜⊃⌝ A ⌜⊃⌝ A) ⌜⊃⌝ A)


----------------------------------------------------------------------------------------------------

-- intrinsically well-typed terms
infix 3 _⊢_
infixl 18 _⌜$⌝_
data _⊢_ (Γ : Ctx) : Ty → Set where
  ⌜c⌝   : ∀ {A} (k : Con A) → Γ ⊢ A
  ⌜v⌝   : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  ⌜λ⌝   : ∀ {A B} (t : A ∷ Γ ⊢ B) → Γ ⊢ A ⌜⊃⌝ B
  _⌜$⌝_ : ∀ {A B} (t₁ : Γ ⊢ A ⌜⊃⌝ B) (t₂ : Γ ⊢ A) → Γ ⊢ B

open ⊢*Kit _⊢_ public


----------------------------------------------------------------------------------------------------

-- renaming
ren : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
ren e (⌜c⌝ k)     = ⌜c⌝ k
ren e (⌜v⌝ i)     = ⌜v⌝ (ren∋ e i)
ren e (⌜λ⌝ t)     = ⌜λ⌝ (ren (keep e) t)
ren e (t₁ ⌜$⌝ t₂) = ren e t₁ ⌜$⌝ ren e t₂

open RenKit ⌜v⌝ ren public


----------------------------------------------------------------------------------------------------

-- substitution
sub : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ⊢ A → Ξ ⊢ A
sub ss (⌜c⌝ k)     = ⌜c⌝ k
sub ss (⌜v⌝ i)     = sub∋ ss i
sub ss (⌜λ⌝ t)     = ⌜λ⌝ (sub (lifts ss) t)
sub ss (t₁ ⌜$⌝ t₂) = sub ss t₁ ⌜$⌝ sub ss t₂

open SubKit sub public


----------------------------------------------------------------------------------------------------

-- decidable equality
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
⌜c⌝ k     ≟ ⌜c⌝ k′          with k ≟Con k′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
⌜c⌝ k     ≟ ⌜v⌝ i             = no λ ()
⌜c⌝ k     ≟ ⌜λ⌝ t′            = no λ ()
⌜c⌝ k     ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
⌜v⌝ i     ≟ ⌜c⌝ k             = no λ ()
⌜v⌝ i     ≟ ⌜v⌝ i′          with i ≟∋ i′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
⌜v⌝ i     ≟ ⌜λ⌝ t′            = no λ ()
⌜v⌝ i     ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
⌜λ⌝ t     ≟ ⌜c⌝ k             = no λ ()
⌜λ⌝ t     ≟ ⌜v⌝ i′            = no λ ()
⌜λ⌝ t     ≟ ⌜λ⌝ t′          with t ≟ t′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
⌜λ⌝ t     ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜c⌝ k             = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜v⌝ i′            = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜λ⌝ t′            = no λ ()
t₁ ⌜$⌝ t₂ ≟ t₁′ ⌜$⌝ t₂′     with ty t₁ ≟Ty ty t₁′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                with t₁ ≟ t₁′ | t₂ ≟ t₂′
...   | no ¬eq₁  | _            = no λ { refl → refl ↯ ¬eq₁ }
...   | yes refl | no ¬eq₂      = no λ { refl → refl ↯ ¬eq₂ }
...   | yes refl | yes refl     = yes refl


----------------------------------------------------------------------------------------------------
