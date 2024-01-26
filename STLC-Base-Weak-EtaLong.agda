module STLC-Base-Weak-EtaLong where

open import STLC-Base public
open import Isomorphism public


----------------------------------------------------------------------------------------------------

-- β-short η-long weak normal forms (F-irreducible)
mutual
  data FNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝- : ∀ {A B} {t : A ∷ Γ ⊢ B} → FNF (⌜λ⌝ t)
    nnf  : ∀ {t : Γ ⊢ ⌜◦⌝} (p : FNNF t) → FNF t

  -- neutrals
  data FNNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜v⌝-  : ∀ {A} {i : Γ ∋ A} → FNNF (⌜v⌝ i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : FNNF t₁) (p₂ : FNF t₂) →
            FNNF (t₁ ⌜$⌝ t₂)

-- renaming
mutual
  renFNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → FNF t → FNF (ren e t)
  renFNF e ⌜λ⌝-    = ⌜λ⌝-
  renFNF e (nnf p) = nnf (renFNNF e p)

  renFNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → FNNF t → FNNF (ren e t)
  renFNNF e ⌜v⌝-        = ⌜v⌝-
  renFNNF e (p₁ ⌜$⌝ p₂) = renFNNF e p₁ ⌜$⌝ renFNF e p₂

-- uniqueness of proofs
mutual
  uniFNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : FNF t) → p ≡ p′
  uniFNF ⌜λ⌝-    ⌜λ⌝-     = refl
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
  FNF? {A = _ ⌜⊃⌝ _} (⌜λ⌝ t)     = yes ⌜λ⌝-
  FNF? {A = _ ⌜⊃⌝ _} (t₁ ⌜$⌝ t₂) = no λ ()

  FNNF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (FNNF t)
  FNNF? (⌜v⌝ i)         = yes ⌜v⌝-
  FNNF? (⌜λ⌝ t)         = no λ ()
  FNNF? (t₁ ⌜$⌝ t₂)     with FNNF? t₁ | FNF? t₂
  ... | yes p₁ | yes p₂   = yes (p₁ ⌜$⌝ p₂)
  ... | yes p₁ | no ¬p₂   = no λ { (p₁ ⌜$⌝ p₂) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _        = no λ { (p₁ ⌜$⌝ p₂) → p₁ ↯ ¬p₁ }


----------------------------------------------------------------------------------------------------

-- expandability, or neutrals at function type
data Expandable {Γ} : ∀ {A} → Γ ⊢ A → Set where
  ⌜v⌝-  : ∀ {A B} {i : Γ ∋ A ⌜⊃⌝ B} → Expandable (⌜v⌝ i)
  _⌜$⌝_ : ∀ {A B C} {t₁ : Γ ⊢ A ⌜⊃⌝ B ⌜⊃⌝ C} {t₂ : Γ ⊢ A} → FNNF t₁ → FNF t₂ →
          Expandable (t₁ ⌜$⌝ t₂)

FNNF→Expandable : ∀ {Γ A B} {t : Γ ⊢ A ⌜⊃⌝ B} → FNNF t → Expandable t
FNNF→Expandable ⌜v⌝-        = ⌜v⌝-
FNNF→Expandable (p₁ ⌜$⌝ p₂) = p₁ ⌜$⌝ p₂

Expandable→FNNF : ∀ {Γ A B} {t : Γ ⊢ A ⌜⊃⌝ B} → Expandable t → FNNF t
Expandable→FNNF ⌜v⌝-        = ⌜v⌝-
Expandable→FNNF (p₁ ⌜$⌝ p₂) = p₁ ⌜$⌝ p₂

-- TODO: delete?
-- FNF→¬Expandable : ∀ {Γ A} {t : Γ ⊢ A} → FNF t → ¬ Expandable t
-- FNF→¬Expandable ⌜λ⌝-    ()
-- FNF→¬Expandable (nnf p) ()

Expandable→¬FNF : ∀ {Γ A} {t : Γ ⊢ A} → Expandable t → ¬ FNF t
Expandable→¬FNF ⌜v⌝-        ()
Expandable→¬FNF (p₁ ⌜$⌝ p₂) ()

uniExpandable : ∀ {Γ A} {t : Γ ⊢ A} (x x′ : Expandable t) → x ≡ x′
uniExpandable ⌜v⌝-        ⌜v⌝-          = refl
uniExpandable (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniFNNF p₁ p₁′ ⊗ uniFNF p₂ p₂′

-- TODO: define NotExpandable directly and get rid of extensionality
module _ (⚠ : Extensionality) where
  uni¬Expandable : ∀ {Γ A} {t : Γ ⊢ A} (¬x ¬x′ : ¬ Expandable t) → ¬x ≡ ¬x′
  uni¬Expandable = uni→ ⚠ uni𝟘


----------------------------------------------------------------------------------------------------

data _ExpandsTo_ {Γ} : ∀ {A} (t t′ : Γ ⊢ A) → Set where
  ηexp⊃ : ∀ {A B} {t t′ : Γ ⊢ A ⌜⊃⌝ B} (eq : t′ ≡ ⌜λ⌝ (weak t ⌜$⌝ ⌜v⌝ zero))
            (x : Expandable t) →
          t ExpandsTo t′

-- TODO: delete?
-- data Expanded {Γ} : ∀ {A} (t′ : Γ ⊢ A) → Set where
--   ηexp⊃ : ∀ {A B} {t : Γ ⊢ A ⌜⊃⌝ B} {t′ : Γ ⊢ A ⌜⊃⌝ B} (x : Expandable t)
--             (eq : t′ ≡ ⌜λ⌝ (weak t ⌜$⌝ ⌜v⌝ zero)) →
--           Expanded t′

Expanded : ∀ {Γ A} (t′ : Γ ⊢ A) → Set
Expanded t′ = Σ _ λ t → t ExpandsTo t′


----------------------------------------------------------------------------------------------------

-- β-short η-long weak normal forms guaranteed not to be a top-level η-expansion (I-irreducible)
-- TODO: how to define this directly?
INF : ∀ {Γ A} → Γ ⊢ A → Set
INF t = FNF t × ¬ Expanded t

INNF : ∀ {Γ A} → Γ ⊢ A → Set
INNF t = FNNF t × ¬ Expanded t

INF→FNF : ∀ {Γ A} {t : Γ ⊢ A} → INF t → FNF t
INF→FNF (p , _) = p

-- TODO: delete?
-- INNF→FNNF : ∀ {Γ A} {t : Γ ⊢ A} → INNF t → FNNF t
-- INNF→FNNF (p , _) = p


----------------------------------------------------------------------------------------------------

-- definitional equality
infix 4 _≝_
data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  refl≝  : ∀ {A} {t : Γ ⊢ A} → t ≝ t
  sym≝   : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
  trans≝ : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
  cong$  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
           t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
  βred⊃  : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ]) →
           ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′
  ηexp⊃  : ∀ {A B} {t t′ : Γ ⊢ A ⌜⊃⌝ B} (eq : t′ ≡ ⌜λ⌝ (weak t ⌜$⌝ ⌜v⌝ zero)) → t ≝ t′

open ≝Kit (λ {_} {_} {t} → refl≝ {t = t}) sym≝ trans≝ public


----------------------------------------------------------------------------------------------------

-- call-by-value restricted expansionary reduction (Ghani p.51, table 3-4)

-- NOTE: modified by removing duplicate rules from ⇒F and replacing them with Ired,
--       and by adding FNF constraints to Icong$₂, Fcong$₂, and βred⊃
-- mutual
--   infix 4 _⇒F_
--   data _⇒F_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
--     Ired  : ∀ {A} {t t′ : Γ ⊢ A} (r : t ⇒I t′) → t ⇒F t′
--     ηexp⊃ : ∀ {A B} {t t′ : Γ ⊢ A ⌜⊃⌝ B} (eq : t′ ≡ ⌜λ⌝ (weak t ⌜$⌝ ⌜v⌝ zero))
--               (x : Expandable t) →
--             t ⇒F t′
--
--   infix 4 _⇒I_
--   data _⇒I_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
--     cong$₁  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r : t₁ ⇒I t₁′) →
--               t₁ ⌜$⌝ t₂ ⇒I t₁′ ⌜$⌝ t₂
--     Icong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : FNF t₁) (r₂ : t₂ ⇒I t₂′) →
--               t₁ ⌜$⌝ t₂ ⇒I t₁ ⌜$⌝ t₂′
--     Fcong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : FNF t₁) (r₂ : t₂ ⇒F t₂′) →
--               t₁ ⌜$⌝ t₂ ⇒I t₁ ⌜$⌝ t₂′
--     βred⊃   : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ])
--                 (p₂ : FNF t₂) →
--               ⌜λ⌝ t₁ ⌜$⌝ t₂ ⇒I t′

mutual
  -- NOTE: further modified by adding constraint to Ired
  infix 4 _⇒F_
  data _⇒F_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    Ired  : ∀ {A} {t t′ : Γ ⊢ A} (¬x : ¬ Expandable t) (r : t ⇒I t′) → t ⇒F t′
    ηexp⊃ : ∀ {A B} {t t′ : Γ ⊢ A ⌜⊃⌝ B} (eq : t′ ≡ ⌜λ⌝ (weak t ⌜$⌝ ⌜v⌝ zero))
              (x : Expandable t) →
            t ⇒F t′

  -- NOTE: further modified by removing Icong$₂ and adding Xcong$₂
  infix 4 _⇒I_
  data _⇒I_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    cong$₁  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r : t₁ ⇒I t₁′) →
              t₁ ⌜$⌝ t₂ ⇒I t₁′ ⌜$⌝ t₂
    Fcong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : FNF t₁) (r₂ : t₂ ⇒F t₂′) →
              t₁ ⌜$⌝ t₂ ⇒I t₁ ⌜$⌝ t₂′
    Xcong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (x₁ : Expandable t₁) (r₂ : t₂ ⇒F t₂′) →
              t₁ ⌜$⌝ t₂ ⇒I t₁ ⌜$⌝ t₂′
    βred⊃   : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ])
                (p₂ : FNF t₂) →
              ⌜λ⌝ t₁ ⌜$⌝ t₂ ⇒I t′

module F = ⇒Kit _⇒F_
module I = ⇒Kit _⇒I_

mutual
  FNF→¬FR : ∀ {Γ A} {t : Γ ⊢ A} → FNF t → F.¬R t
  FNF→¬FR ⌜λ⌝-    (ηexp⊃ refl ())
  FNF→¬FR (nnf p) r               = r ↯ FNNF→¬FR p

  FNNF→¬FR : ∀ {Γ} {t : Γ ⊢ ⌜◦⌝} → FNNF t → F.¬R t
  FNNF→¬FR p (Ired ¬x r) = r ↯ FNNF→¬IR p

  FNF→¬IR : ∀ {Γ A} {t : Γ ⊢ A} → FNF t → I.¬R t
  FNF→¬IR (nnf p) r = r ↯ FNNF→¬IR p

  FNNF→¬IR : ∀ {Γ A} {t : Γ ⊢ A} → FNNF t → I.¬R t
  FNNF→¬IR (p₁ ⌜$⌝ p₂) (cong$₁ r₁)      = r₁ ↯ FNNF→¬IR p₁
  FNNF→¬IR (p₁ ⌜$⌝ p₂) (Fcong$₂ p₁′ r₂) = r₂ ↯ FNF→¬FR p₂
  FNNF→¬IR (p₁ ⌜$⌝ p₂) (Xcong$₂ x₁ r₂)  = r₂ ↯ FNF→¬FR p₂

-- TODO: delete?
-- INF→¬FR : ∀ {Γ A} {t : Γ ⊢ A} → INF t → F.¬R t
-- INF→¬FR = FNF→¬FR ∘ INF→FNF

-- INNF→¬FR : ∀ {Γ} {t : Γ ⊢ ⌜◦⌝} → INNF t → F.¬R t
-- INNF→¬FR = FNNF→¬FR ∘ INNF→FNNF

INF→¬IR : ∀ {Γ A} {t : Γ ⊢ A} → INF t → I.¬R t
INF→¬IR = FNF→¬IR ∘ INF→FNF

-- INNF→¬IR : ∀ {Γ A} {t : Γ ⊢ A} → INNF t → I.¬R t
-- INNF→¬IR = FNNF→¬IR ∘ INNF→FNNF

module F′ = F.¬RKit FNF→¬FR
module I′ = I.¬RKit INF→¬IR


----------------------------------------------------------------------------------------------------

Expandable→¬IR : ∀ {Γ A B} {t : Γ ⊢ A ⌜⊃⌝ B} → Expandable t → I.¬R t
Expandable→¬IR = FNNF→¬IR ∘ Expandable→FNNF

-- TODO: delete?
-- ¬FR→¬Expandable : ∀ {Γ A} {t : Γ ⊢ A} → F.¬R t → ¬ Expandable t
-- -- ¬FR→¬Expandable = ¬η→¬Expandable ∘ ¬FR→¬η
-- ¬FR→¬Expandable {A = A ⌜⊃⌝ B} {t = ⌜v⌝ i}     ¬r x = ηexp⊃ refl x ↯ ¬r
-- ¬FR→¬Expandable {A = A ⌜⊃⌝ B} {t = t₁ ⌜$⌝ t₂} ¬r x = ηexp⊃ refl x ↯ ¬r

-- ¬FR→¬IR : ∀ {Γ A} {t : Γ ⊢ A} → F.¬R t → I.¬R t
-- ¬FR→¬IR ¬r r = Ired (¬FR→¬Expandable ¬r) r ↯ ¬r

-- ¬FRF→¬IRF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ F.RF t → ¬ I.RF t
-- ¬FRF→¬IRF = I′.¬R→¬RF ∘ ¬FR→¬IR ∘ F′.¬RF→¬R


----------------------------------------------------------------------------------------------------

-- progress
prog⇒F : ∀ {Γ A} (t : Γ ⊢ A) → F′.Prog t
prog⇒F {A = ⌜◦⌝}     (⌜v⌝ i)            = F′.done (nnf ⌜v⌝-)
prog⇒F {A = ⌜◦⌝}     (t₁ ⌜$⌝ t₂)        with prog⇒F t₁ | prog⇒F t₂
... | F′.step (Ired ¬x₁ r₁) | _            = F′.step (Ired (λ ()) (cong$₁ r₁))
... | F′.step (ηexp⊃ eq x₁) | F′.step r₂   = F′.step (Ired (λ ()) (Xcong$₂ x₁ r₂))
... | F′.step (ηexp⊃ eq x₁) | F′.done p₂   = F′.done (nnf (Expandable→FNNF x₁ ⌜$⌝ p₂))
... | F′.done p₁            | F′.step r₂   = F′.step (Ired (λ ()) (Fcong$₂ p₁ r₂))
... | F′.done ⌜λ⌝-          | F′.done p₂   = F′.step (Ired (λ ()) (βred⊃ refl p₂))
prog⇒F {A = A ⌜⊃⌝ B} (⌜v⌝ i)              = F′.step (ηexp⊃ refl ⌜v⌝-)
prog⇒F {A = A ⌜⊃⌝ B} (⌜λ⌝ t)              = F′.done ⌜λ⌝-
prog⇒F {A = A ⌜⊃⌝ B} (t₁ ⌜$⌝ t₂)        with prog⇒F t₁ | prog⇒F t₂
... | F′.step (Ired ¬x₁ r₁) | _            = F′.step (Ired (λ { (p₁ ⌜$⌝ p₂) →
                                               FNNF→Expandable p₁ ↯ ¬x₁ }) (cong$₁ r₁))
... | F′.step (ηexp⊃ eq x₁) | F′.step r₂   = F′.step (Ired (λ { (p₁ ⌜$⌝ p₂) →
                                               r₂ ↯ FNF→¬FR p₂ }) (Xcong$₂ x₁ r₂))
... | F′.step (ηexp⊃ eq x₁) | F′.done p₂   = F′.step (ηexp⊃ refl (Expandable→FNNF x₁ ⌜$⌝ p₂))
... | F′.done ⌜λ⌝-          | F′.step r₂   = F′.step (Ired (λ { (() ⌜$⌝ p₂′) }) (Fcong$₂ ⌜λ⌝- r₂))
... | F′.done ⌜λ⌝-          | F′.done p₂   = F′.step (Ired (λ { (() ⌜$⌝ p₂′) }) (βred⊃ refl p₂))

module F″ = F′.ProgKit prog⇒F

module _ (⚠ : Extensionality) where
  uni¬FRF : ∀ {Γ A} {t : Γ ⊢ A} (¬p ¬p′ : ¬ F.RF t) → ¬p ≡ ¬p′
  uni¬FRF = uni→ ⚠ uni𝟘

  uni¬IRF : ∀ {Γ A} {t : Γ ⊢ A} (¬p ¬p′ : ¬ I.RF t) → ¬p ≡ ¬p′
  uni¬IRF = uni→ ⚠ uni𝟘

  FNF≃¬FRF : ∀ {Γ A} {t : Γ ⊢ A} → FNF t ≃ (¬ F.RF t)
  FNF≃¬FRF = record
    { to      = F′.NF→¬RF
    ; from    = F″.¬RF→NF
    ; from∘to = λ p → uniFNF _ p
    ; to∘from = λ p → uni¬FRF _ p
    }

-- TODO: this doesn’t seem provable, but maybe that’s okay?
-- prog⇒I : ∀ {Γ A} (t : Γ ⊢ A) → I′.Prog t
-- prog⇒I t = ?


----------------------------------------------------------------------------------------------------

-- determinism
mutual
  det⇒F : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒F t′ → t ⇒F t″ → t′ ≡ t″
  det⇒F (Ired ¬x r)    (Ired ¬x′ r′)   = det⇒I r r′
  det⇒F (Ired ¬x r)    (ηexp⊃ refl x′) = x′ ↯ ¬x
  det⇒F (ηexp⊃ refl x) (Ired ¬x′ r′)   = x ↯ ¬x′
  det⇒F (ηexp⊃ refl x) (ηexp⊃ refl x′) = refl

  det⇒I : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒I t′ → t ⇒I t″ → t′ ≡ t″
  det⇒I (cong$₁ r₁)     (cong$₁ r₁′)      = (_⌜$⌝ _) & det⇒I r₁ r₁′
  det⇒I (cong$₁ r₁)     (Fcong$₂ p₁′ r₂′) = r₁ ↯ FNF→¬IR p₁′
  det⇒I (cong$₁ r₁)     (Xcong$₂ x₁′ r₂′) = r₁ ↯ Expandable→¬IR x₁′
  det⇒I (Fcong$₂ p₁ r₂) (cong$₁ r₁′)      = r₁′ ↯ FNF→¬IR p₁
  det⇒I (Fcong$₂ p₁ r₂) (Fcong$₂ p₁′ r₂′) = (_ ⌜$⌝_) & det⇒F r₂ r₂′
  det⇒I (Fcong$₂ p₁ r₂) (Xcong$₂ x₁′ r₂′) = p₁ ↯ Expandable→¬FNF x₁′
  det⇒I (Fcong$₂ p₁ r₂) (βred⊃ refl p₂′)  = r₂ ↯ FNF→¬FR p₂′
  det⇒I (Xcong$₂ x₁ r₂) (cong$₁ r₁′)      = r₁′ ↯ Expandable→¬IR x₁
  det⇒I (Xcong$₂ x₁ r₂) (Fcong$₂ p₁′ r₂′) = p₁′ ↯ Expandable→¬FNF x₁
  det⇒I (Xcong$₂ x₁ r₂) (Xcong$₂ x₁′ r₂′) = (_ ⌜$⌝_) & det⇒F r₂ r₂′
  det⇒I (βred⊃ refl p₂) (Fcong$₂ p₁′ r₂′) = r₂′ ↯ FNF→¬FR p₂
  det⇒I (βred⊃ refl p₂) (βred⊃ refl p₂′)  = refl

module F‴ = F.DetKit FNF→¬FR det⇒F
module I‴ = I.DetKit INF→¬IR det⇒I

-- uniqueness of proofs
module _ (⚠ : Extensionality) where
  mutual
    uni⇒F : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒F t′) → r ≡ r′
    uni⇒F (Ired ¬x r)    (Ired ¬x′ r′)   = Ired & uni¬Expandable ⚠ ¬x ¬x′ ⊗ uni⇒I r r′
    uni⇒F (Ired ¬x r)    (ηexp⊃ eq′ x′)  = x′ ↯ ¬x
    uni⇒F (ηexp⊃ eq x)   (Ired ¬x′ r′)   = x ↯ ¬x′
    uni⇒F (ηexp⊃ refl x) (ηexp⊃ refl x′) = ηexp⊃ refl & uniExpandable x x′

    uni⇒I : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒I t′) → r ≡ r′
    uni⇒I (cong$₁ r₁)     (cong$₁ r₁′)      = cong$₁ & uni⇒I r₁ r₁′
    uni⇒I (cong$₁ r₁)     (Fcong$₂ p₁′ r₂′) = r₁ ↯ FNF→¬IR p₁′
    uni⇒I (cong$₁ r₁)     (Xcong$₂ x₁′ r₂′) = r₁ ↯ Expandable→¬IR x₁′
    uni⇒I (Fcong$₂ p₁ r₂) (cong$₁ r₁′)      = r₁′ ↯ FNF→¬IR p₁
    uni⇒I (Fcong$₂ p₁ r₂) (Fcong$₂ p₁′ r₂′) = Fcong$₂ & uniFNF p₁ p₁′ ⊗ uni⇒F r₂ r₂′
    uni⇒I (Fcong$₂ p₁ r₂) (Xcong$₂ x₁′ r₂′) = p₁ ↯ Expandable→¬FNF x₁′
    uni⇒I (Fcong$₂ p₁ r₂) (βred⊃ eq′ p₂′)   = r₂ ↯ FNF→¬FR p₂′
    uni⇒I (Xcong$₂ x₁ r₂) (cong$₁ r₁′)      = r₁′ ↯ Expandable→¬IR x₁
    uni⇒I (Xcong$₂ x₁ r₂) (Fcong$₂ p₁′ r₂′) = p₁′ ↯ Expandable→¬FNF x₁
    uni⇒I (Xcong$₂ x₁ r₂) (Xcong$₂ x₁′ r₂′) = Xcong$₂ & uniExpandable x₁ x₁′ ⊗ uni⇒F r₂ r₂′
    uni⇒I (βred⊃ eq p₂)   (Fcong$₂ p₁′ r₂′) = r₂′ ↯ FNF→¬FR p₂
    uni⇒I (βred⊃ refl p₂) (βred⊃ refl p₂′)  = βred⊃ refl & uniFNF p₂ p₂′


----------------------------------------------------------------------------------------------------

-- TODO: delete?
Expandable? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (Expandable t)
Expandable? {A = ⌜◦⌝}     t           = no λ ()
Expandable? {A = A ⌜⊃⌝ B} (⌜v⌝ i)     = yes ⌜v⌝-
Expandable? {A = A ⌜⊃⌝ B} (⌜λ⌝ t)     = no λ ()
Expandable? {A = A ⌜⊃⌝ B} (t₁ ⌜$⌝ t₂) with FNNF? t₁ | FNF? t₂
... | no ¬p₁ | _                        = no λ { (p₁ ⌜$⌝ p₂) → p₁ ↯ ¬p₁ }
... | yes p₁ | no ¬p₂                   = no λ { (p₁ ⌜$⌝ p₂) → p₂ ↯ ¬p₂ }
... | yes p₁ | yes p₂                   = yes (p₁ ⌜$⌝ p₂)

-- (Ghani p.51, unnumbered lemma)
FR→IR⊎η : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒F t′ → t ⇒I t′ ⊎ t ExpandsTo t′
FR→IR⊎η (Ired ¬x (cong$₁ r₁))     = inj₁ (cong$₁ r₁)
FR→IR⊎η (Ired ¬x (Fcong$₂ p₁ r₂)) = inj₁ (Fcong$₂ p₁ r₂)
FR→IR⊎η (Ired ¬x (Xcong$₂ x₁ r₂)) = inj₁ (Xcong$₂ x₁ r₂)
FR→IR⊎η (Ired ¬x (βred⊃ eq p₂))   = inj₁ (βred⊃ eq p₂)
FR→IR⊎η (ηexp⊃ refl x)            = inj₂ (ηexp⊃ refl x)

IR⊎η→FR : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒I t′ ⊎ t ExpandsTo t′ → t ⇒F t′
IR⊎η→FR {A = ⌜◦⌝}     {t} (inj₁ r)              = Ired (λ ()) r
IR⊎η→FR {A = A ⌜⊃⌝ B} {t} (inj₁ r)              with Expandable? t
... | yes x                                        = r ↯ Expandable→¬IR x
... | no ¬x                                        = Ired ¬x r
IR⊎η→FR                   (inj₂ (ηexp⊃ refl x)) = ηexp⊃ refl x


----------------------------------------------------------------------------------------------------

-- -- TODO: delete?
-- _ExpandsTo?_ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Dec (t ExpandsTo t′)
-- ⌜v⌝ i       ExpandsTo? ⌜v⌝ i′                            = no λ { (ηexp⊃ () x) }
-- ⌜v⌝ i       ExpandsTo? ⌜λ⌝ (⌜v⌝ i′)                      = no λ { (ηexp⊃ () x) }
-- ⌜v⌝ i       ExpandsTo? ⌜λ⌝ (⌜λ⌝ t′)                      = no λ { (ηexp⊃ () x) }
-- ⌜v⌝ i       ExpandsTo? ⌜λ⌝ (⌜v⌝ i′ ⌜$⌝ ⌜v⌝ zero)         with weak∋ i ≟∋ i′
-- ... | no ¬eq                                               = no λ { (ηexp⊃ refl x) → refl ↯ ¬eq }
-- ... | yes refl                                             = yes (ηexp⊃ refl ⌜v⌝-)
-- ⌜v⌝ i       ExpandsTo? ⌜λ⌝ (⌜v⌝ i′ ⌜$⌝ ⌜v⌝ (suc _))      = no λ { (ηexp⊃ () x) }
-- ⌜v⌝ i       ExpandsTo? ⌜λ⌝ (⌜v⌝ i′ ⌜$⌝ ⌜λ⌝ t₂′)          = no λ { (ηexp⊃ () x) }
-- ⌜v⌝ i       ExpandsTo? ⌜λ⌝ (⌜v⌝ i′ ⌜$⌝ t₂′@(_ ⌜$⌝ _))    = no λ { (ηexp⊃ () x) }
-- ⌜v⌝ i       ExpandsTo? ⌜λ⌝ (⌜λ⌝ t₁′ ⌜$⌝ t₂′)             = no λ { (ηexp⊃ () x) }
-- ⌜v⌝ i       ExpandsTo? ⌜λ⌝ (t₁′@(_ ⌜$⌝ _) ⌜$⌝ t₂′)       = no λ { (ηexp⊃ () x) }
-- ⌜v⌝ i       ExpandsTo? (t₁′ ⌜$⌝ t₂′)                     = no λ { (ηexp⊃ () x) }
-- ⌜λ⌝ t       ExpandsTo? t′                                = no λ { (ηexp⊃ eq ()) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜v⌝ i′                            = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (⌜v⌝ i′)                      = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (⌜λ⌝ t′)                      = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (⌜v⌝ i′ ⌜$⌝ t₂′)              = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (⌜λ⌝ t₁′ ⌜$⌝ t₂′)             = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (t₁′ ⌜$⌝ t₂′ ⌜$⌝ ⌜v⌝ zero)    with weak (t₁ ⌜$⌝ t₂) ≟ t₁′ ⌜$⌝ t₂′
-- ... | no ¬eq                                               = no λ { (ηexp⊃ refl x) → refl ↯ ¬eq }
-- ... | yes refl                                             with FNNF? t₁ | FNF? t₂
-- ...   | no ¬p₁ | _                                           = no λ { (ηexp⊃ refl (p₁ ⌜$⌝ p₂)) →
--                                                                  p₁ ↯ ¬p₁ }
-- ...   | yes p₁ | no ¬p₂                                      = no λ { (ηexp⊃ refl (p₁′ ⌜$⌝ p₂)) →
--                                                                  p₂ ↯ ¬p₂ }
-- ...   | yes p₁ | yes p₂                                      = yes (ηexp⊃ refl (p₁ ⌜$⌝ p₂))
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (t₁′ ⌜$⌝ t₂′ ⌜$⌝ ⌜v⌝ (suc _)) = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (t₁′ ⌜$⌝ t₂′ ⌜$⌝ ⌜λ⌝ _)       = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (t₁′ ⌜$⌝ t₂′ ⌜$⌝ (_ ⌜$⌝ _))   = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? (t₁′ ⌜$⌝ t₂′)                     = no λ { (ηexp⊃ () x) }

-- private
--   lem₀ : ∀ {Γ A A′ B C} {t₁ : Γ ⊢ A ⌜⊃⌝ B ⌜⊃⌝ C} {t₁′ : Γ ⊢ A′ ⌜⊃⌝ B ⌜⊃⌝ C}
--            {t₂ : Γ ⊢ A} {t₂′ : Γ ⊢ A′} →
--            ⌜λ⌝ ((weak t₁ ⌜$⌝ weak t₂) ⌜$⌝ ⌜v⌝ zero) ≡ ⌜λ⌝ ((weak t₁′ ⌜$⌝ weak t₂′) ⌜$⌝ ⌜v⌝ zero) →
--          Σ (A ≡ A′) λ { refl → t₁ ≡ t₁′ × t₂ ≡ t₂′ }
--   lem₀ {A = A} {A′} eq with inj$₁′ (inj$₁ (injλ eq))
--   ... | refl , eq₁ = refl , injren eq₁ , injren (inj$₂ (inj$₁ (injλ eq)))

--   lem₁ : ∀ {Γ A A′ B C} {t₁ : Γ ⊢ A ⌜⊃⌝ B ⌜⊃⌝ C} {t₁′ : Γ ⊢ A′ ⌜⊃⌝ B ⌜⊃⌝ C}
--            {t₂ : Γ ⊢ A} {t₂′ : Γ ⊢ A′} →
--            ⌜λ⌝ ((weak t₁ ⌜$⌝ weak t₂) ⌜$⌝ ⌜v⌝ zero) ≡ ⌜λ⌝ ((weak t₁′ ⌜$⌝ weak t₂′) ⌜$⌝ ⌜v⌝ zero) →
--          ¬ FNNF t₁ → ¬ FNNF t₁′
--   lem₁ eq ¬p₁ p₁ with lem₀ eq
--   ... | refl , refl , refl = p₁ ↯ ¬p₁

--   lem₂ : ∀ {Γ A A′ B C} {t₁ : Γ ⊢ A ⌜⊃⌝ B ⌜⊃⌝ C} {t₁′ : Γ ⊢ A′ ⌜⊃⌝ B ⌜⊃⌝ C}
--            {t₂ : Γ ⊢ A} {t₂′ : Γ ⊢ A′} →
--            ⌜λ⌝ ((weak t₁ ⌜$⌝ weak t₂) ⌜$⌝ ⌜v⌝ zero) ≡ ⌜λ⌝ ((weak t₁′ ⌜$⌝ weak t₂′) ⌜$⌝ ⌜v⌝ zero) →
--          ¬ FNF t₂ → ¬ FNF t₂′
--   lem₂ eq ¬p₂ p₂ with lem₀ eq
--   ... | refl , refl , refl = p₂ ↯ ¬p₂

-- -- TODO: delete?
-- Expanded? : ∀ {Γ A} (t′ : Γ ⊢ A) → Dec (Expanded t′)
-- Expanded? (⌜v⌝ i′)                      = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (⌜v⌝ i′))                = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (⌜λ⌝ t′))                = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (t′ ⌜$⌝ ⌜v⌝ zero))       with unren wk⊆ t′
-- ... | no ¬p                               = no λ { (_ , ηexp⊃ refl x) → (_ , refl) ↯ ¬p }
-- ... | yes (⌜v⌝ i , refl)                  = yes (_ , ηexp⊃ refl ⌜v⌝-)
-- ... | yes (⌜λ⌝ t , refl)                  = no λ { (⌜v⌝ _ , ηexp⊃ () x)
--                                                  ; (⌜λ⌝ _ , ηexp⊃ eq ())
--                                                  ; (_ ⌜$⌝ _ , ηexp⊃ () x)
--                                                  }
-- ... | yes (t₁ ⌜$⌝ t₂ , refl)              with FNNF? t₁ | FNF? t₂
-- ...   | no ¬p₁ | _                          = no λ { (_ , ηexp⊃ eq (p₁ ⌜$⌝ p₂)) →
--                                                 p₁ ↯ lem₁ eq ¬p₁ }
-- ...   | yes p₁ | no ¬p₂                     = no λ { (_ , ηexp⊃ eq (p₁′ ⌜$⌝ p₂)) →
--                                                 p₂ ↯ lem₂ eq ¬p₂ }
-- ...   | yes p₁ | yes p₂                     = yes (_ , ηexp⊃ refl (p₁ ⌜$⌝ p₂))
-- Expanded? (⌜λ⌝ (t′ ⌜$⌝ ⌜v⌝ (suc i′)))   = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (t₁′ ⌜$⌝ ⌜λ⌝ t₂′))       = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (t₁′ ⌜$⌝ t₂′@(_ ⌜$⌝ _))) = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (t₁′ ⌜$⌝ t₂′)                 = no λ { (_ , ηexp⊃ () x) }


-- ----------------------------------------------------------------------------------------------------
