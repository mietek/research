module STLC-Negative where

open import Common public


----------------------------------------------------------------------------------------------------

-- types
infixr 18 _⌜⊃⌝_
infixl 19 _⌜∧⌝_
data Ty : Set where
  _⌜⊃⌝_ : ∀ (A B : Ty) → Ty
  _⌜∧⌝_ : ∀ (A B : Ty) → Ty
  ⌜𝟙⌝   : Ty

infixr 18 _`⫗_
_`⫗_ : ∀ (A B : Ty) → Ty
A `⫗ B = (A ⌜⊃⌝ B) ⌜∧⌝ (B ⌜⊃⌝ A)

open CtxKit Ty public

-- intrinsically well-typed terms
infix 3 _⊢_
infixl 18 _⌜$⌝_
data _⊢_ (Γ : Ctx) : Ty → Set where
  ⌜v⌝     : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  ⌜λ⌝     : ∀ {A B} (t : A ∷ Γ ⊢ B) → Γ ⊢ A ⌜⊃⌝ B
  _⌜$⌝_   : ∀ {A B} (t₁ : Γ ⊢ A ⌜⊃⌝ B) (t₂ : Γ ⊢ A) → Γ ⊢ B
  _⌜,⌝_   : ∀ {A B} (t₁ : Γ ⊢ A) (t₂ : Γ ⊢ B) → Γ ⊢ A ⌜∧⌝ B
  ⌜proj₁⌝ : ∀ {A B} (t : Γ ⊢ A ⌜∧⌝ B) → Γ ⊢ A
  ⌜proj₂⌝ : ∀ {A B} (t : Γ ⊢ A ⌜∧⌝ B) → Γ ⊢ B
  ⌜unit⌝  : Γ ⊢ ⌜𝟙⌝

open ⊢*Kit _⊢_ public


----------------------------------------------------------------------------------------------------

-- renaming
ren⊢ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
ren⊢ e (⌜v⌝ i)     = ⌜v⌝ (ren∋ e i)
ren⊢ e (⌜λ⌝ t)     = ⌜λ⌝ (ren⊢ (keep e) t)
ren⊢ e (t₁ ⌜$⌝ t₂) = ren⊢ e t₁ ⌜$⌝ ren⊢ e t₂
ren⊢ e (t₁ ⌜,⌝ t₂) = ren⊢ e t₁ ⌜,⌝ ren⊢ e t₂
ren⊢ e (⌜proj₁⌝ t) = ⌜proj₁⌝ (ren⊢ e t)
ren⊢ e (⌜proj₂⌝ t) = ⌜proj₂⌝ (ren⊢ e t)
ren⊢ e ⌜unit⌝      = ⌜unit⌝

open RenKit ⌜v⌝ ren⊢ public

-- substitution
sub⊢ : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ⊢ A → Ξ ⊢ A
sub⊢ ss (⌜v⌝ i)     = sub∋ ss i
sub⊢ ss (⌜λ⌝ t)     = ⌜λ⌝ (sub⊢ (lift⊢* ss) t)
sub⊢ ss (t₁ ⌜$⌝ t₂) = sub⊢ ss t₁ ⌜$⌝ sub⊢ ss t₂
sub⊢ ss (t₁ ⌜,⌝ t₂) = sub⊢ ss t₁ ⌜,⌝ sub⊢ ss t₂
sub⊢ ss (⌜proj₁⌝ t) = ⌜proj₁⌝ (sub⊢ ss t)
sub⊢ ss (⌜proj₂⌝ t) = ⌜proj₂⌝ (sub⊢ ss t)
sub⊢ ss ⌜unit⌝      = ⌜unit⌝

open SubKit sub⊢ public


----------------------------------------------------------------------------------------------------

-- decidable equality
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
⌜v⌝ i     ≟ ⌜v⌝ i′          with i ≟∋ i′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
⌜v⌝ i     ≟ ⌜λ⌝ t′            = no λ ()
⌜v⌝ i     ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
⌜v⌝ i     ≟ t₁′ ⌜,⌝ t₂′       = no λ ()
⌜v⌝ i     ≟ ⌜proj₁⌝ t′        = no λ ()
⌜v⌝ i     ≟ ⌜proj₂⌝ t′        = no λ ()
⌜v⌝ i     ≟ ⌜unit⌝            = no λ ()
⌜λ⌝ t     ≟ ⌜v⌝ i′            = no λ ()
⌜λ⌝ t     ≟ ⌜λ⌝ t′          with t ≟ t′
... | no ¬eq                  = no λ { refl → refl ↯ ¬eq }
... | yes refl                = yes refl
⌜λ⌝ t     ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
⌜λ⌝ t     ≟ ⌜proj₁⌝ t′        = no λ ()
⌜λ⌝ t     ≟ ⌜proj₂⌝ t′        = no λ ()
t₁ ⌜$⌝ t₂ ≟ ⌜v⌝ i′            = no λ ()
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
t₁ ⌜,⌝ t₂ ≟ ⌜v⌝ i′            = no λ ()
t₁ ⌜,⌝ t₂ ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
t₁ ⌜,⌝ t₂ ≟ t₁′ ⌜,⌝ t₂′     with t₁ ≟ t₁′ | t₂ ≟ t₂′
... | no ¬eq₁  | _            = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂      = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl     = yes refl
t₁ ⌜,⌝ t₂ ≟ ⌜proj₁⌝ t′        = no λ ()
t₁ ⌜,⌝ t₂ ≟ ⌜proj₂⌝ t′        = no λ ()
⌜proj₁⌝ t ≟ ⌜v⌝ i′            = no λ ()
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
⌜proj₂⌝ t ≟ ⌜v⌝ i′            = no λ ()
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
⌜unit⌝    ≟ ⌜v⌝ i′            = no λ ()
⌜unit⌝    ≟ t₁′ ⌜$⌝ t₂′       = no λ ()
⌜unit⌝    ≟ ⌜proj₁⌝ t′        = no λ ()
⌜unit⌝    ≟ ⌜proj₂⌝ t′        = no λ ()
⌜unit⌝    ≟ ⌜unit⌝            = yes refl


----------------------------------------------------------------------------------------------------
