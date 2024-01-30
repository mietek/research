module STLC-Naturals where

open import Common public


----------------------------------------------------------------------------------------------------

-- types
infixr 18 _⌜⊃⌝_
data Ty : Set where
  _⌜⊃⌝_ : ∀ (A B : Ty) → Ty
  ⌜ℕ⌝   : Ty

recTy : ∀ {𝓍} {X : Set 𝓍} → Ty → (Ty → X → Ty → X → X) → X → X
recTy (A ⌜⊃⌝ B) f⊃ fℕ = f⊃ A (recTy A f⊃ fℕ) B (recTy B f⊃ fℕ)
recTy ⌜ℕ⌝       f⊃ fℕ = fℕ

open CtxKit Ty public


----------------------------------------------------------------------------------------------------

-- intrinsically well-typed terms
infix 3 _⊢_
infixl 18 _⌜$⌝_
data _⊢_ (Γ : Ctx) : Ty → Set where
  ⌜v⌝    : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  ⌜λ⌝    : ∀ {A B} (t : A ∷ Γ ⊢ B) → Γ ⊢ A ⌜⊃⌝ B
  _⌜$⌝_  : ∀ {A B} (t₁ : Γ ⊢ A ⌜⊃⌝ B) (t₂ : Γ ⊢ A) → Γ ⊢ B
  ⌜zero⌝ : Γ ⊢ ⌜ℕ⌝
  ⌜suc⌝  : ∀ (t : Γ ⊢ ⌜ℕ⌝) → Γ ⊢ ⌜ℕ⌝
  ⌜rec⌝  : ∀ {A} (tₙ : Γ ⊢ ⌜ℕ⌝) (t₀ : Γ ⊢ A) (tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A) → Γ ⊢ A

open ⊢*Kit _⊢_ public


----------------------------------------------------------------------------------------------------

-- renaming
ren⊢ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
ren⊢ e (⌜v⌝ i)          = ⌜v⌝ (ren∋ e i)
ren⊢ e (⌜λ⌝ t)          = ⌜λ⌝ (ren⊢ (keep e) t)
ren⊢ e (t₁ ⌜$⌝ t₂)      = ren⊢ e t₁ ⌜$⌝ ren⊢ e t₂
ren⊢ e ⌜zero⌝           = ⌜zero⌝
ren⊢ e (⌜suc⌝ t)        = ⌜suc⌝ (ren⊢ e t)
ren⊢ e (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ (ren⊢ e tₙ) (ren⊢ e t₀) (ren⊢ (keep (keep e)) tₛ)

open RenKit ⌜v⌝ ren⊢ public


----------------------------------------------------------------------------------------------------

-- substitution
sub⊢ : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ⊢ A → Ξ ⊢ A
sub⊢ ss (⌜v⌝ i)          = sub∋ ss i
sub⊢ ss (⌜λ⌝ t)          = ⌜λ⌝ (sub⊢ (lift⊢* ss) t)
sub⊢ ss (t₁ ⌜$⌝ t₂)      = sub⊢ ss t₁ ⌜$⌝ sub⊢ ss t₂
sub⊢ ss ⌜zero⌝           = ⌜zero⌝
sub⊢ ss (⌜suc⌝ t)        = ⌜suc⌝ (sub⊢ ss t)
sub⊢ ss (⌜rec⌝ tₙ t₀ tₛ) = ⌜rec⌝ (sub⊢ ss tₙ) (sub⊢ ss t₀) (sub⊢ (lift⊢* (lift⊢* ss)) tₛ)

open SubKit sub⊢ public


----------------------------------------------------------------------------------------------------

infix 4 _≟Ty_
_≟Ty_ : ∀ (A A′ : Ty) → Dec (A ≡ A′)
A ⌜⊃⌝ B ≟Ty A′ ⌜⊃⌝ B′     with A ≟Ty A′ | B ≟Ty B′
... | no ¬eq₁  | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂    = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl   = yes refl
A ⌜⊃⌝ B ≟Ty ⌜ℕ⌝           = no λ ()
⌜ℕ⌝     ≟Ty A′ ⌜⊃⌝ B      = no λ ()
⌜ℕ⌝     ≟Ty ⌜ℕ⌝           = yes refl

infix 4 _≟_
_≟_ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Dec (t ≡ t′)
⌜v⌝ i          ≟ ⌜v⌝ i′              with i ≟∋ i′
... | no ¬eq                           = no λ { refl → refl ↯ ¬eq }
... | yes refl                         = yes refl
⌜v⌝ i          ≟ ⌜λ⌝ t′                = no λ ()
⌜v⌝ i          ≟ t₁′ ⌜$⌝ t₂′           = no λ ()
⌜v⌝ i          ≟ ⌜zero⌝                = no λ ()
⌜v⌝ i          ≟ ⌜suc⌝ t′              = no λ ()
⌜v⌝ i          ≟ ⌜rec⌝ tₙ′ t₀′ tₛ′     = no λ ()
⌜λ⌝ t          ≟ ⌜v⌝ i′                = no λ ()
⌜λ⌝ t          ≟ ⌜λ⌝ t′              with t ≟ t′
... | no ¬eq                           = no λ { refl → refl ↯ ¬eq }
... | yes refl                         = yes refl
⌜λ⌝ t          ≟ t₁′ ⌜$⌝ t₂′           = no λ ()
⌜λ⌝ t          ≟ ⌜rec⌝ tₙ′ t₀′ tₛ′     = no λ ()
t₁ ⌜$⌝ t₂      ≟ ⌜v⌝ i′                = no λ ()
t₁ ⌜$⌝ t₂      ≟ ⌜λ⌝ t′                = no λ ()
t₁ ⌜$⌝ t₂      ≟ t₁′ ⌜$⌝ t₂′         with ty t₁ ≟Ty ty t₁′
... | no ¬eq                           = no λ { refl → refl ↯ ¬eq }
... | yes refl                         with t₁ ≟ t₁′ | t₂ ≟ t₂′
...   | no ¬eq₁  | _                     = no λ { refl → refl ↯ ¬eq₁ }
...   | yes refl | no ¬eq₂               = no λ { refl → refl ↯ ¬eq₂ }
...   | yes refl | yes refl              = yes refl
t₁ ⌜$⌝ t₂      ≟ ⌜zero⌝                = no λ ()
t₁ ⌜$⌝ t₂      ≟ ⌜suc⌝ t′              = no λ ()
t₁ ⌜$⌝ t₂      ≟ ⌜rec⌝ tₙ′ t₀′ tₛ′     = no λ ()
⌜zero⌝         ≟ ⌜v⌝ i                 = no λ ()
⌜zero⌝         ≟ t₁′ ⌜$⌝ t₂′           = no λ ()
⌜zero⌝         ≟ ⌜zero⌝                = yes refl
⌜zero⌝         ≟ ⌜suc⌝ t′              = no λ ()
⌜zero⌝         ≟ ⌜rec⌝ tₙ′ t₀′ tₛ′     = no λ ()
⌜suc⌝ t        ≟ ⌜v⌝ i                 = no λ ()
⌜suc⌝ t        ≟ t₁′ ⌜$⌝ t₂′           = no λ ()
⌜suc⌝ t        ≟ ⌜zero⌝                = no λ ()
⌜suc⌝ t        ≟ ⌜suc⌝ t′            with t ≟ t′
... | no ¬eq                           = no λ { refl → refl ↯ ¬eq }
... | yes refl                         = yes refl
⌜suc⌝ t        ≟ ⌜rec⌝ tₙ′ t₀′ tₛ′     = no λ ()
⌜rec⌝ tₙ t₀ tₛ ≟ ⌜v⌝ i                 = no λ ()
⌜rec⌝ tₙ t₀ tₛ ≟ ⌜λ⌝ t′                = no λ ()
⌜rec⌝ tₙ t₀ tₛ ≟ t₁′ ⌜$⌝ t₂′           = no λ ()
⌜rec⌝ tₙ t₀ tₛ ≟ ⌜zero⌝                = no λ ()
⌜rec⌝ tₙ t₀ tₛ ≟ ⌜suc⌝ t′              = no λ ()
⌜rec⌝ tₙ t₀ tₛ ≟ ⌜rec⌝ tₙ′ t₀′ tₛ′   with tₙ ≟ tₙ′ | t₀ ≟ t₀′ | tₛ ≟ tₛ′
... | no ¬eqₙ  | _        | _          = no λ { refl → refl ↯ ¬eqₙ }
... | yes refl | no ¬eq₀  | _          = no λ { refl → refl ↯ ¬eq₀ }
... | yes refl | yes refl | no ¬eqₛ    = no λ { refl → refl ↯ ¬eqₛ }
... | yes refl | yes refl | yes refl   = yes refl


----------------------------------------------------------------------------------------------------
