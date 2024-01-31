module STLC-Base-Strong-EtaLong where

open import STLC-Base public
open import Isomorphism public


----------------------------------------------------------------------------------------------------

-- β-short η-long weak normal forms (F-irreducible)
mutual
  data FNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝ : ∀ {A B} {t : A ∷ Γ ⊢ B} (p : FNF t) → FNF (⌜λ⌝ t)
    nnf : ∀ {t : Γ ⊢ ⌜◦⌝} (p : FNNF t) → FNF t

  -- neutrals
  data FNNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜v⌝-  : ∀ {A} {i : Γ ∋ A} → FNNF (⌜v⌝ i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : FNNF t₁) (p₂ : FNF t₂) →
            FNNF (t₁ ⌜$⌝ t₂)

-- renaming
mutual
  renFNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → FNF t → FNF (ren e t)
  renFNF e (⌜λ⌝ p) = ⌜λ⌝ (renFNF (keep e) p)
  renFNF e (nnf p) = nnf (renFNNF e p)

  renFNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → FNNF t → FNNF (ren e t)
  renFNNF e ⌜v⌝-        = ⌜v⌝-
  renFNNF e (p₁ ⌜$⌝ p₂) = renFNNF e p₁ ⌜$⌝ renFNF e p₂

-- uniqueness of proofs
mutual
  uniFNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : FNF t) → p ≡ p′
  uniFNF (⌜λ⌝ p) (⌜λ⌝ p′) = ⌜λ⌝ & uniFNF p p′
  uniFNF (nnf p) (nnf p′) = nnf & uniFNNF p p′

  uniFNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : FNNF t) → p ≡ p′
  uniFNNF ⌜v⌝-        ⌜v⌝-          = refl
  uniFNNF (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniFNNF p₁ p₁′ ⊗ uniFNF p₂ p₂′

mutual
  FNF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (FNF t)
  FNF? {A = ⌜◦⌝}     (⌜v⌝ i)     = yes (nnf ⌜v⌝-)
  FNF? {A = ⌜◦⌝}     (t₁ ⌜$⌝ t₂) with FNNF? t₁ | FNF? t₂
  ... | yes p₁ | yes p₂            = yes (nnf (p₁ ⌜$⌝ p₂))
  ... | yes p₁ | no ¬p₂            = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _                 = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₁ ↯ ¬p₁ }
  FNF? {A = _ ⌜⊃⌝ _} (⌜v⌝ i)     = no λ ()
  FNF? {A = _ ⌜⊃⌝ _} (⌜λ⌝ t)     with FNF? t
  ... | yes p                      = yes (⌜λ⌝ p)
  ... | no ¬p                      = no λ { (⌜λ⌝ p) → p ↯ ¬p }
  FNF? {A = _ ⌜⊃⌝ _} (t₁ ⌜$⌝ t₂) = no λ ()

  FNNF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (FNNF t)
  FNNF? (⌜v⌝ i)         = yes ⌜v⌝-
  FNNF? (⌜λ⌝ t)         = no λ ()
  FNNF? (t₁ ⌜$⌝ t₂)     with FNNF? t₁ | FNF? t₂
  ... | yes p₁ | yes p₂   = yes (p₁ ⌜$⌝ p₂)
  ... | yes p₁ | no ¬p₂   = no λ { (p₁ ⌜$⌝ p₂) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _        = no λ { (p₁ ⌜$⌝ p₂) → p₁ ↯ ¬p₁ }


----------------------------------------------------------------------------------------------------

-- definitional equality
infix 4 _≝_
data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  refl≝  : ∀ {A} {t : Γ ⊢ A} → t ≝ t
  sym≝   : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
  trans≝ : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
  congλ  : ∀ {A B} {t t′ : A ∷ Γ ⊢ B} (eq : t ≝ t′) → ⌜λ⌝ t ≝ ⌜λ⌝ t′
  cong$  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
           t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
  βred⊃  : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) → ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
  ηexp⊃  : ∀ {A B} {t t′ : Γ ⊢ A ⌜⊃⌝ B} (eq : t′ ≡ ⌜λ⌝ (weak t ⌜$⌝ ⌜v⌝ zero)) → t ≝ t′

open ≝Kit (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝ public


----------------------------------------------------------------------------------------------------
