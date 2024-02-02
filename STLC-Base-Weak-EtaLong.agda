module STLC-Base-Weak-EtaLong where

open import STLC-Base-Properties public
open import Kit3 public


----------------------------------------------------------------------------------------------------

-- β-short η-long weak normal forms (F-irreducible)
mutual
  data FNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝- : ∀ {A B} {t : A ∷ Γ ⊢ B} → FNF (⌜λ⌝ t)
    nnf  : ∀ {t : Γ ⊢ ⌜◦⌝} (p : FNNF t) → FNF t

  -- neutrals
  data FNNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → FNNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : FNNF t₁) (p₂ : FNF t₂) →
            FNNF (t₁ ⌜$⌝ t₂)

data FNNF* {Γ} : ∀ {Δ} → Γ ⊢* Δ → Set where
  []  : FNNF* []
  _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} → FNNF t → FNNF* ts → FNNF* (t ∷ ts)

mutual
  uniFNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : FNF t) → p ≡ p′
  uniFNF ⌜λ⌝-    ⌜λ⌝-     = refl
  uniFNF (nnf p) (nnf p′) = nnf & uniFNNF p p′

  uniFNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : FNNF t) → p ≡ p′
  uniFNNF var-        var-          = refl
  uniFNNF (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniFNNF p₁ p₁′ ⊗ uniFNF p₂ p₂′

mutual
  FNF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (FNF t)
  FNF? {A = ⌜◦⌝}     (var i)     = yes (nnf var-)
  FNF? {A = ⌜◦⌝}     (t₁ ⌜$⌝ t₂) with FNNF? t₁ | FNF? t₂
  ... | yes p₁ | yes p₂            = yes (nnf (p₁ ⌜$⌝ p₂))
  ... | yes p₁ | no ¬p₂            = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _                 = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₁ ↯ ¬p₁ }
  FNF? {A = _ ⌜⊃⌝ _} (var i)     = no λ ()
  FNF? {A = _ ⌜⊃⌝ _} (⌜λ⌝ t)     = yes ⌜λ⌝-
  FNF? {A = _ ⌜⊃⌝ _} (t₁ ⌜$⌝ t₂) = no λ ()

  FNNF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (FNNF t)
  FNNF? (var i)         = yes var-
  FNNF? (⌜λ⌝ t)         = no λ ()
  FNNF? (t₁ ⌜$⌝ t₂)     with FNNF? t₁ | FNF? t₂
  ... | yes p₁ | yes p₂   = yes (p₁ ⌜$⌝ p₂)
  ... | yes p₁ | no ¬p₂   = no λ { (p₁ ⌜$⌝ p₂) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _        = no λ { (p₁ ⌜$⌝ p₂) → p₁ ↯ ¬p₁ }


----------------------------------------------------------------------------------------------------

-- expandability, or neutrals at function type
data Expandable {Γ} : ∀ {A} → Γ ⊢ A → Set where
  var-  : ∀ {A B} {i : Γ ∋ A ⌜⊃⌝ B} → Expandable (var i)
  _⌜$⌝_ : ∀ {A B C} {t₁ : Γ ⊢ A ⌜⊃⌝ B ⌜⊃⌝ C} {t₂ : Γ ⊢ A} → FNNF t₁ → FNF t₂ →
          Expandable (t₁ ⌜$⌝ t₂)

uniExpandable : ∀ {Γ A} {t : Γ ⊢ A} (x x′ : Expandable t) → x ≡ x′
uniExpandable var-        var-          = refl
uniExpandable (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniFNNF p₁ p₁′ ⊗ uniFNF p₂ p₂′

-- TODO: genericize?
data Expandable* {Γ} : ∀ {Δ} → Γ ⊢* Δ → Set where
  []  : Expandable* []
  _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} → Expandable t → Expandable* ts → Expandable* (t ∷ ts)

FNNF→Expandable : ∀ {Γ A B} {t : Γ ⊢ A ⌜⊃⌝ B} → FNNF t → Expandable t
FNNF→Expandable var-        = var-
FNNF→Expandable (p₁ ⌜$⌝ p₂) = p₁ ⌜$⌝ p₂

Expandable→FNNF : ∀ {Γ A B} {t : Γ ⊢ A ⌜⊃⌝ B} → Expandable t → FNNF t
Expandable→FNNF var-        = var-
Expandable→FNNF (p₁ ⌜$⌝ p₂) = p₁ ⌜$⌝ p₂

-- TODO: delete?
-- FNF→¬Expandable : ∀ {Γ A} {t : Γ ⊢ A} → FNF t → ¬ Expandable t
-- FNF→¬Expandable ⌜λ⌝-    ()
-- FNF→¬Expandable (nnf p) ()

Expandable→¬FNF : ∀ {Γ A} {t : Γ ⊢ A} → Expandable t → ¬ FNF t
Expandable→¬FNF var-        ()
Expandable→¬FNF (p₁ ⌜$⌝ p₂) ()

uni¬Expandable : ∀ {Γ A} {t : Γ ⊢ A} (¬x ¬x′ : ¬ Expandable t) → ¬x ≡ ¬x′
uni¬Expandable = uni¬


----------------------------------------------------------------------------------------------------

data _ExpandsTo_ {Γ} : ∀ {A} (t t′ : Γ ⊢ A) → Set where
  ηexp⊃ : ∀ {A B} {t t′ : Γ ⊢ A ⌜⊃⌝ B} (eq : t′ ≡ ⌜λ⌝ (wk t ⌜$⌝ var zero))
            (x : Expandable t) →
          t ExpandsTo t′

-- TODO: delete?
-- data Expanded {Γ} : ∀ {A} (t′ : Γ ⊢ A) → Set where
--   ηexp⊃ : ∀ {A B} {t : Γ ⊢ A ⌜⊃⌝ B} {t′ : Γ ⊢ A ⌜⊃⌝ B} (x : Expandable t)
--             (eq : t′ ≡ ⌜λ⌝ (wk t ⌜$⌝ var zero)) →
--           Expanded t′

Expanded : ∀ {Γ A} (t′ : Γ ⊢ A) → Set
Expanded t′ = Σ _ λ t → t ExpandsTo t′

uni¬Expanded : ∀ {Γ A} {t : Γ ⊢ A} (¬x ¬x′ : ¬ Expanded t) → ¬x ≡ ¬x′
uni¬Expanded = uni¬


----------------------------------------------------------------------------------------------------

-- β-short η-long weak normal forms guaranteed not to be a top-level η-expansion (I-irreducible)
-- TODO: how to define this directly?
INF : ∀ {Γ A} → Γ ⊢ A → Set
INF t = FNF t × ¬ Expanded t

-- TODO: delete?
-- INNF : ∀ {Γ A} → Γ ⊢ A → Set
-- INNF t = FNNF t × ¬ Expanded t

INF→FNF : ∀ {Γ A} {t : Γ ⊢ A} → INF t → FNF t
INF→FNF (p , _) = p

-- TODO: delete?
-- INNF→FNNF : ∀ {Γ A} {t : Γ ⊢ A} → INNF t → FNNF t
-- INNF→FNNF (p , _) = p

uniINF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : INF t) → p ≡ p′
uniINF (p , ¬x) (p′ , ¬x′) = _,_ & uniFNF p p′ ⊗ uni¬Expanded ¬x ¬x′


----------------------------------------------------------------------------------------------------

-- call-by-value restricted expansionary reduction (Ghani p.51, table 3-4)

-- NOTE: modified by removing duplicate rules from ⇒F and replacing them with Ired,
--       and by adding FNF constraints to Icong$₂, Fcong$₂, and βred⊃
-- mutual
--   infix 4 _⇒F_
--   data _⇒F_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
--     Ired  : ∀ {A} {t t′ : Γ ⊢ A} (r : t ⇒I t′) → t ⇒F t′
--     ηexp⊃ : ∀ {A B} {t t′ : Γ ⊢ A ⌜⊃⌝ B} (eq : t′ ≡ ⌜λ⌝ (weak t ⌜$⌝ var zero))
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
    ηexp⊃ : ∀ {A B} {t : Γ ⊢ A ⌜⊃⌝ B} {t′} (eq : t′ ≡ wk t) (x : Expandable t) →
            t ⇒F ⌜λ⌝ (t′ ⌜$⌝ var zero)

  -- NOTE: further modified by removing Icong$₂ and adding Xcong$₂
  infix 4 _⇒I_
  data _⇒I_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    cong$₁  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r : t₁ ⇒I t₁′) →
              t₁ ⌜$⌝ t₂ ⇒I t₁′ ⌜$⌝ t₂
    Fcong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : FNF t₁) (r₂ : t₂ ⇒F t₂′) →
              t₁ ⌜$⌝ t₂ ⇒I t₁ ⌜$⌝ t₂′
    Xcong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (x₁ : Expandable t₁) (r₂ : t₂ ⇒F t₂′) →
              t₁ ⌜$⌝ t₂ ⇒I t₁ ⌜$⌝ t₂′
    βred⊃   : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) (p₂ : FNF t₂) →
              ⌜λ⌝ t₁ ⌜$⌝ t₂ ⇒I t′

module RK1F = RedKit1 (kit tmkit _⇒F_)
module RK1I = RedKit1 (kit tmkit _⇒I_)

mutual
  FNF→¬FR : ∀ {Γ A} {t : Γ ⊢ A} → FNF t → RK1F.¬R t
  FNF→¬FR ⌜λ⌝-    (ηexp⊃ refl ())
  FNF→¬FR (nnf p) r               = r ↯ FNNF→¬FR p

  FNNF→¬FR : ∀ {Γ} {t : Γ ⊢ ⌜◦⌝} → FNNF t → RK1F.¬R t
  FNNF→¬FR p (Ired ¬x r) = r ↯ FNNF→¬IR p

  FNF→¬IR : ∀ {Γ A} {t : Γ ⊢ A} → FNF t → RK1I.¬R t
  FNF→¬IR (nnf p) r = r ↯ FNNF→¬IR p

  FNNF→¬IR : ∀ {Γ A} {t : Γ ⊢ A} → FNNF t → RK1I.¬R t
  FNNF→¬IR (p₁ ⌜$⌝ p₂) (cong$₁ r₁)      = r₁ ↯ FNNF→¬IR p₁
  FNNF→¬IR (p₁ ⌜$⌝ p₂) (Fcong$₂ p₁′ r₂) = r₂ ↯ FNF→¬FR p₂
  FNNF→¬IR (p₁ ⌜$⌝ p₂) (Xcong$₂ x₁ r₂)  = r₂ ↯ FNF→¬FR p₂

-- TODO: delete?
-- INF→¬FR : ∀ {Γ A} {t : Γ ⊢ A} → INF t → RK1F.¬R t
-- INF→¬FR = FNF→¬FR ∘ INF→FNF

-- INNF→¬FR : ∀ {Γ} {t : Γ ⊢ ⌜◦⌝} → INNF t → RK1F.¬R t
-- INNF→¬FR = FNNF→¬FR ∘ INNF→FNNF

INF→¬IR : ∀ {Γ A} {t : Γ ⊢ A} → INF t → RK1I.¬R t
INF→¬IR = FNF→¬IR ∘ INF→FNF

-- INNF→¬IR : ∀ {Γ A} {t : Γ ⊢ A} → INNF t → RK1I.¬R t
-- INNF→¬IR = FNNF→¬IR ∘ INNF→FNNF

module RK2F = RedKit2 (kit RK1F.redkit1 uniFNF FNF→¬FR)
module RK2I = RedKit2 (kit RK1I.redkit1 uniINF INF→¬IR)


----------------------------------------------------------------------------------------------------

Expandable→¬IR : ∀ {Γ A B} {t : Γ ⊢ A ⌜⊃⌝ B} → Expandable t → RK1I.¬R t
Expandable→¬IR = FNNF→¬IR ∘ Expandable→FNNF

-- TODO: delete?
-- ¬FR→¬Expandable : ∀ {Γ A} {t : Γ ⊢ A} → RK1F.¬R t → ¬ Expandable t
-- ¬FR→¬Expandable {A = A ⌜⊃⌝ B} {t = var i}     ¬r x = ηexp⊃ refl x ↯ ¬r
-- ¬FR→¬Expandable {A = A ⌜⊃⌝ B} {t = t₁ ⌜$⌝ t₂} ¬r x = ηexp⊃ refl x ↯ ¬r
--
-- ¬FR→¬IR : ∀ {Γ A} {t : Γ ⊢ A} → RK1F.¬R t → RK1I.¬R t
-- ¬FR→¬IR ¬r r = Ired (¬FR→¬Expandable ¬r) r ↯ ¬r
--
-- ¬FRF→¬IRF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RK1F.RF t → ¬ RK1I.RF t
-- ¬FRF→¬IRF = RK2I.¬R→¬RF ∘ ¬FR→¬IR ∘ RK2F.¬RF→¬R


----------------------------------------------------------------------------------------------------

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

mutual
  uni⇒F : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒F t′) → r ≡ r′
  uni⇒F (Ired ¬x r)    (Ired ¬x′ r′)   = Ired & uni¬Expandable ¬x ¬x′ ⊗ uni⇒I r r′
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

module DKF = DetKit (kit RK2F.redkit2 det⇒F uni⇒F)
module DKI = DetKit (kit RK2I.redkit2 det⇒I uni⇒I)


----------------------------------------------------------------------------------------------------

prog⇒F : ∀ {Γ A} (t : Γ ⊢ A) → RK2F.Prog t
prog⇒F {A = ⌜◦⌝}     (var i)                = RK2F.done (nnf var-)
prog⇒F {A = ⌜◦⌝}     (t₁ ⌜$⌝ t₂)            with prog⇒F t₁ | prog⇒F t₂
... | RK2F.step (Ired ¬x₁ r₁) | _                = RK2F.step (Ired (λ ()) (cong$₁ r₁))
... | RK2F.step (ηexp⊃ eq x₁) | RK2F.step r₂       = RK2F.step (Ired (λ ()) (Xcong$₂ x₁ r₂))
... | RK2F.step (ηexp⊃ eq x₁) | RK2F.done p₂       = RK2F.done (nnf (Expandable→FNNF x₁ ⌜$⌝ p₂))
... | RK2F.done p₁            | RK2F.step r₂       = RK2F.step (Ired (λ ()) (Fcong$₂ p₁ r₂))
... | RK2F.done ⌜λ⌝-          | RK2F.done p₂       = RK2F.step (Ired (λ ()) (βred⊃ refl p₂))
prog⇒F {A = A ⌜⊃⌝ B} (var i)                  = RK2F.step (ηexp⊃ refl var-)
prog⇒F {A = A ⌜⊃⌝ B} (⌜λ⌝ t)                  = RK2F.done ⌜λ⌝-
prog⇒F {A = A ⌜⊃⌝ B} (t₁ ⌜$⌝ t₂)            with prog⇒F t₁ | prog⇒F t₂
... | RK2F.step (Ired ¬x₁ r₁) | _                = RK2F.step (Ired (λ { (p₁ ⌜$⌝ p₂) →
                                                   FNNF→Expandable p₁ ↯ ¬x₁ }) (cong$₁ r₁))
... | RK2F.step (ηexp⊃ eq x₁) | RK2F.step r₂       = RK2F.step (Ired (λ { (p₁ ⌜$⌝ p₂) →
                                                   r₂ ↯ FNF→¬FR p₂ }) (Xcong$₂ x₁ r₂))
... | RK2F.step (ηexp⊃ eq x₁) | RK2F.done p₂       = RK2F.step (ηexp⊃ refl (Expandable→FNNF x₁ ⌜$⌝ p₂))
... | RK2F.done ⌜λ⌝-          | RK2F.step r₂       = RK2F.step (Ired (λ { (() ⌜$⌝ p₂′) }) (Fcong$₂ ⌜λ⌝- r₂))
... | RK2F.done ⌜λ⌝-          | RK2F.done p₂       = RK2F.step (Ired (λ { (() ⌜$⌝ p₂′) }) (βred⊃ refl p₂))

-- TODO: progress doesn’t seem provable for _⇒I_, but maybe that’s okay?
-- prog⇒I : ∀ {Γ A} (t : Γ ⊢ A) → RK2I.Prog t
-- prog⇒I t = {pp}

module PKF = ProgKit (kit RK2F.redkit2 prog⇒F)


----------------------------------------------------------------------------------------------------

-- stability under renaming
mutual
  renFNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → FNF t → FNF (ren e t)
  renFNF e ⌜λ⌝-    = ⌜λ⌝-
  renFNF e (nnf p) = nnf (renFNNF e p)

  renFNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → FNNF t → FNNF (ren e t)
  renFNNF e var-        = var-
  renFNNF e (p₁ ⌜$⌝ p₂) = renFNNF e p₁ ⌜$⌝ renFNF e p₂

mutual
  nerFNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → FNF (ren e t) → FNF t
  nerFNF {t = var i}     e (nnf p) = nnf (nerFNNF e p)
  nerFNF {t = ⌜λ⌝ t}     e ⌜λ⌝-    = ⌜λ⌝-
  nerFNF {t = t₁ ⌜$⌝ t₂} e (nnf p) = nnf (nerFNNF e p)

  nerFNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → FNNF (ren e t) → FNNF t
  nerFNNF {t = var i}     e var-        = var-
  nerFNNF {t = t₁ ⌜$⌝ t₂} e (p₁ ⌜$⌝ p₂) = nerFNNF e p₁ ⌜$⌝ nerFNF e p₂

renExpandable : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → Expandable t → Expandable (ren e t)
renExpandable e var-        = var-
renExpandable e (p₁ ⌜$⌝ p₂) = renFNNF e p₁ ⌜$⌝ renFNF e p₂

ren¬Expandable : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → ¬ Expandable t → ¬ Expandable (ren e t)
ren¬Expandable {t = var i}     e ¬x var-        = var- ↯ ¬x
ren¬Expandable {t = t₁ ⌜$⌝ t₂} e ¬x (p₁ ⌜$⌝ p₂) = (nerFNNF e p₁ ⌜$⌝ nerFNF e p₂) ↯ ¬x

mutual
  ren⇒F : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (e : Γ ⊆ Γ′) → t ⇒F t′ → ren e t ⇒F ren e t′
  ren⇒F e (Ired ¬x r)    = Ired (ren¬Expandable e ¬x) (ren⇒I e r)
  ren⇒F e (ηexp⊃ refl x) = ηexp⊃ (eqwkren e _) (renExpandable e x)

  ren⇒I : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (e : Γ ⊆ Γ′) → t ⇒I t′ → ren e t ⇒I ren e t′
  ren⇒I e (cong$₁ r₁)               = cong$₁ (ren⇒I e r₁)
  ren⇒I e (Fcong$₂ p₁ r₂)           = Fcong$₂ (renFNF e p₁) (ren⇒F e r₂)
  ren⇒I e (Xcong$₂ x₁ r₂)           = Xcong$₂ (renExpandable e x₁) (ren⇒F e r₂)
  ren⇒I e (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (renβred⊃ e t₁ _ ⁻¹) (renFNF e p₂)


----------------------------------------------------------------------------------------------------

-- stability under substitution
sub∋FNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {i : Γ ∋ A} → FNNF* ss → FNNF (sub∋ ss i)
sub∋FNNF {i = zero}  (p ∷ ps) = p
sub∋FNNF {i = suc i} (p ∷ ps) = sub∋FNNF ps

mutual
  subFNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → FNNF* ss → FNF t → FNF (sub ss t)
  subFNF ps ⌜λ⌝-    = ⌜λ⌝-
  subFNF ps (nnf p) = nnf (subFNNF ps p)

  subFNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → FNNF* ss → FNNF t → FNNF (sub ss t)
  subFNNF ps var-        = sub∋FNNF ps
  subFNNF ps (p₁ ⌜$⌝ p₂) = subFNNF ps p₁ ⌜$⌝ subFNF ps p₂

bus∋FNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {i : Γ ∋ A} → FNNF* ss → FNF (sub∋ ss i) → FNF (var i)
bus∋FNNF {A = ⌜◦⌝}     {i = i}     ps        p′   = nnf var-
bus∋FNNF {A = A ⌜⊃⌝ B} {i = zero}  (() ∷ ps) ⌜λ⌝-
bus∋FNNF {A = A ⌜⊃⌝ B} {i = suc i} (p ∷ ps)  p′   with bus∋FNNF ps p′
... | ()

mutual
  busFNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → FNNF* ss → FNF (sub ss t) → FNF t
  busFNF {t = var i}     ps p       = bus∋FNNF ps p
  busFNF {t = ⌜λ⌝ t}     ps ⌜λ⌝-    = ⌜λ⌝-
  busFNF {t = t₁ ⌜$⌝ t₂} ps (nnf p) = nnf (busFNNF ps p)

  busFNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → FNNF* ss → FNNF (sub ss t) → FNNF t
  busFNNF {t = var i}     ps p           = var-
  busFNNF {t = t₁ ⌜$⌝ t₂} ps (p₁ ⌜$⌝ p₂) = busFNNF ps p₁ ⌜$⌝ busFNF ps p₂

sub∋Expandable : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {i : Γ ∋ A} → Expandable* ss → Expandable (sub∋ ss i)
sub∋Expandable {i = zero}  (x ∷ xs) = x
sub∋Expandable {i = suc i} (x ∷ xs) = sub∋Expandable xs

subExpandable : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → FNNF* ss → Expandable* ss → Expandable t →
                Expandable (sub ss t)
subExpandable ps xs var-        = sub∋Expandable xs
subExpandable ps xs (p₁ ⌜$⌝ p₂) = subFNNF ps p₁ ⌜$⌝ subFNF ps p₂

sub¬Expandable : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → FNNF* ss → ¬ Expandable t →
                 ¬ Expandable (sub ss t)
sub¬Expandable {A = A ⌜⊃⌝ B} {t = var i}     ps ¬x x           = var- ↯ ¬x
sub¬Expandable {A = A ⌜⊃⌝ B} {t = t₁ ⌜$⌝ t₂} ps ¬x (p₁ ⌜$⌝ p₂) = (busFNNF ps p₁ ⌜$⌝ busFNF ps p₂) ↯ ¬x

mutual
  sub⇒I : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t t′ : Γ ⊢ A} → FNNF* ss → Expandable* ss → t ⇒I t′ →
           sub ss t ⇒I sub ss t′
  sub⇒I ps xs (cong$₁ r₁)               = cong$₁ (sub⇒I ps xs r₁)
  sub⇒I ps xs (Fcong$₂ p₁ r₂)           = Fcong$₂ (subFNF ps p₁) (sub⇒F ps xs r₂)
  sub⇒I ps xs (Xcong$₂ x₁ r₂)           = Xcong$₂ (subExpandable ps xs x₁) (sub⇒F ps xs r₂)
  sub⇒I ps xs (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (subβred⊃ _ t₁ _ ⁻¹) (subFNF ps p₂)

  sub⇒F : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t t′ : Γ ⊢ A} → FNNF* ss → Expandable* ss → t ⇒F t′ →
           sub ss t ⇒F sub ss t′
  sub⇒F ps xs (Ired ¬x r)            = Ired (sub¬Expandable ps ¬x) (sub⇒I ps xs r)
  sub⇒F ps xs (ηexp⊃ {t = t} refl x) = ηexp⊃ (eqwksub _ t) (subExpandable ps xs x)


----------------------------------------------------------------------------------------------------

Expandable? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (Expandable t)
Expandable? {A = ⌜◦⌝}     t           = no λ ()
Expandable? {A = A ⌜⊃⌝ B} (var i)     = yes var-
Expandable? {A = A ⌜⊃⌝ B} (⌜λ⌝ t)     = no λ ()
Expandable? {A = A ⌜⊃⌝ B} (t₁ ⌜$⌝ t₂) with FNNF? t₁ | FNF? t₂
... | no ¬p₁ | _                        = no λ { (p₁ ⌜$⌝ p₂) → p₁ ↯ ¬p₁ }
... | yes p₁ | no ¬p₂                   = no λ { (p₁ ⌜$⌝ p₂) → p₂ ↯ ¬p₂ }
... | yes p₁ | yes p₂                   = yes (p₁ ⌜$⌝ p₂)

-- (Ghani p.51, unnumbered lemma)
FR→IR⊎ExpandsTo : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒F t′ → t ⇒I t′ ⊎ t ExpandsTo t′
FR→IR⊎ExpandsTo (Ired ¬x (cong$₁ r₁))     = left (cong$₁ r₁)
FR→IR⊎ExpandsTo (Ired ¬x (Fcong$₂ p₁ r₂)) = left (Fcong$₂ p₁ r₂)
FR→IR⊎ExpandsTo (Ired ¬x (Xcong$₂ x₁ r₂)) = left (Xcong$₂ x₁ r₂)
FR→IR⊎ExpandsTo (Ired ¬x (βred⊃ eq p₂))   = left (βred⊃ eq p₂)
FR→IR⊎ExpandsTo (ηexp⊃ refl x)            = right (ηexp⊃ refl x)

IR⊎ExpandsTo→FR : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒I t′ ⊎ t ExpandsTo t′ → t ⇒F t′
IR⊎ExpandsTo→FR {A = ⌜◦⌝}     {t} (left r)               = Ired (λ ()) r
IR⊎ExpandsTo→FR {A = A ⌜⊃⌝ B} {t} (left r)               with Expandable? t
... | yes x                                                 = r ↯ Expandable→¬IR x
... | no ¬x                                                 = Ired ¬x r
IR⊎ExpandsTo→FR                   (right (ηexp⊃ refl x)) = ηexp⊃ refl x


----------------------------------------------------------------------------------------------------

-- -- TODO: delete?
-- _ExpandsTo?_ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Dec (t ExpandsTo t′)
-- var i       ExpandsTo? var i′                            = no λ { (ηexp⊃ () x) }
-- var i       ExpandsTo? ⌜λ⌝ (var i′)                      = no λ { (ηexp⊃ () x) }
-- var i       ExpandsTo? ⌜λ⌝ (⌜λ⌝ t′)                      = no λ { (ηexp⊃ () x) }
-- var i       ExpandsTo? ⌜λ⌝ (var i′ ⌜$⌝ var zero)         with wk∋ i ≟∋ i′
-- ... | no ¬eq                                               = no λ { (ηexp⊃ refl x) → refl ↯ ¬eq }
-- ... | yes refl                                             = yes (ηexp⊃ refl var-)
-- var i       ExpandsTo? ⌜λ⌝ (var i′ ⌜$⌝ var (suc _))      = no λ { (ηexp⊃ () x) }
-- var i       ExpandsTo? ⌜λ⌝ (var i′ ⌜$⌝ ⌜λ⌝ t₂′)          = no λ { (ηexp⊃ () x) }
-- var i       ExpandsTo? ⌜λ⌝ (var i′ ⌜$⌝ t₂′@(_ ⌜$⌝ _))    = no λ { (ηexp⊃ () x) }
-- var i       ExpandsTo? ⌜λ⌝ (⌜λ⌝ t₁′ ⌜$⌝ t₂′)             = no λ { (ηexp⊃ () x) }
-- var i       ExpandsTo? ⌜λ⌝ (t₁′@(_ ⌜$⌝ _) ⌜$⌝ t₂′)       = no λ { (ηexp⊃ () x) }
-- var i       ExpandsTo? (t₁′ ⌜$⌝ t₂′)                     = no λ { (ηexp⊃ () x) }
-- ⌜λ⌝ t       ExpandsTo? t′                                = no λ { (ηexp⊃ eq ()) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? var i′                            = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (var i′)                      = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (⌜λ⌝ t′)                      = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (var i′ ⌜$⌝ t₂′)              = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (⌜λ⌝ t₁′ ⌜$⌝ t₂′)             = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (t₁′ ⌜$⌝ t₂′ ⌜$⌝ var zero)    with wk (t₁ ⌜$⌝ t₂) ≟ t₁′ ⌜$⌝ t₂′
-- ... | no ¬eq                                               = no λ { (ηexp⊃ refl x) → refl ↯ ¬eq }
-- ... | yes refl                                             with FNNF? t₁ | FNF? t₂
-- ...   | no ¬p₁ | _                                           = no λ { (ηexp⊃ refl (p₁ ⌜$⌝ p₂)) →
--                                                                  p₁ ↯ ¬p₁ }
-- ...   | yes p₁ | no ¬p₂                                      = no λ { (ηexp⊃ refl (p₁′ ⌜$⌝ p₂)) →
--                                                                  p₂ ↯ ¬p₂ }
-- ...   | yes p₁ | yes p₂                                      = yes (ηexp⊃ refl (p₁ ⌜$⌝ p₂))
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (t₁′ ⌜$⌝ t₂′ ⌜$⌝ var (suc _)) = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (t₁′ ⌜$⌝ t₂′ ⌜$⌝ ⌜λ⌝ _)       = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (t₁′ ⌜$⌝ t₂′ ⌜$⌝ (_ ⌜$⌝ _))   = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? (t₁′ ⌜$⌝ t₂′)                     = no λ { (ηexp⊃ () x) }

-- private
--   lem₀ : ∀ {Γ A A′ B C} {t₁ : Γ ⊢ A ⌜⊃⌝ B ⌜⊃⌝ C} {t₁′ : Γ ⊢ A′ ⌜⊃⌝ B ⌜⊃⌝ C}
--            {t₂ : Γ ⊢ A} {t₂′ : Γ ⊢ A′} →
--            ⌜λ⌝ ((wk t₁ ⌜$⌝ wk t₂) ⌜$⌝ var zero) ≡ ⌜λ⌝ ((wk t₁′ ⌜$⌝ wk t₂′) ⌜$⌝ var zero) →
--          Σ (A ≡ A′) λ { refl → t₁ ≡ t₁′ × t₂ ≡ t₂′ }
--   lem₀ {A = A} {A′} eq with inj$₁′ (inj$₁ (injλ eq))
--   ... | refl , eq₁ = refl , injren eq₁ , injren (inj$₂ (inj$₁ (injλ eq)))

--   lem₁ : ∀ {Γ A A′ B C} {t₁ : Γ ⊢ A ⌜⊃⌝ B ⌜⊃⌝ C} {t₁′ : Γ ⊢ A′ ⌜⊃⌝ B ⌜⊃⌝ C}
--            {t₂ : Γ ⊢ A} {t₂′ : Γ ⊢ A′} →
--            ⌜λ⌝ ((wk t₁ ⌜$⌝ wk t₂) ⌜$⌝ var zero) ≡ ⌜λ⌝ ((wk t₁′ ⌜$⌝ wk t₂′) ⌜$⌝ var zero) →
--          ¬ FNNF t₁ → ¬ FNNF t₁′
--   lem₁ eq ¬p₁ p₁ with lem₀ eq
--   ... | refl , refl , refl = p₁ ↯ ¬p₁

--   lem₂ : ∀ {Γ A A′ B C} {t₁ : Γ ⊢ A ⌜⊃⌝ B ⌜⊃⌝ C} {t₁′ : Γ ⊢ A′ ⌜⊃⌝ B ⌜⊃⌝ C}
--            {t₂ : Γ ⊢ A} {t₂′ : Γ ⊢ A′} →
--            ⌜λ⌝ ((wk t₁ ⌜$⌝ wk t₂) ⌜$⌝ var zero) ≡ ⌜λ⌝ ((wk t₁′ ⌜$⌝ wk t₂′) ⌜$⌝ var zero) →
--          ¬ FNF t₂ → ¬ FNF t₂′
--   lem₂ eq ¬p₂ p₂ with lem₀ eq
--   ... | refl , refl , refl = p₂ ↯ ¬p₂

-- Expanded? : ∀ {Γ A} (t′ : Γ ⊢ A) → Dec (Expanded t′)
-- Expanded? (var i′)                      = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (var i′))                = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (⌜λ⌝ t′))                = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (t′ ⌜$⌝ var zero))       with unren wk⊆ t′
-- ... | no ¬p                               = no λ { (_ , ηexp⊃ refl x) → (_ , refl) ↯ ¬p }
-- ... | yes (var i , refl)                  = yes (_ , ηexp⊃ refl var-)
-- ... | yes (⌜λ⌝ t , refl)                  = no λ { (var _ , ηexp⊃ () x)
--                                                  ; (⌜λ⌝ _ , ηexp⊃ eq ())
--                                                  ; (_ ⌜$⌝ _ , ηexp⊃ () x)
--                                                  }
-- ... | yes (t₁ ⌜$⌝ t₂ , refl)              with FNNF? t₁ | FNF? t₂
-- ...   | no ¬p₁ | _                          = no λ { (_ , ηexp⊃ eq (p₁ ⌜$⌝ p₂)) →
--                                                 p₁ ↯ lem₁ eq ¬p₁ }
-- ...   | yes p₁ | no ¬p₂                     = no λ { (_ , ηexp⊃ eq (p₁′ ⌜$⌝ p₂)) →
--                                                 p₂ ↯ lem₂ eq ¬p₂ }
-- ...   | yes p₁ | yes p₂                     = yes (_ , ηexp⊃ refl (p₁ ⌜$⌝ p₂))
-- Expanded? (⌜λ⌝ (t′ ⌜$⌝ var (suc i′)))   = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (t₁′ ⌜$⌝ ⌜λ⌝ t₂′))       = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (t₁′ ⌜$⌝ t₂′@(_ ⌜$⌝ _))) = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (t₁′ ⌜$⌝ t₂′)                 = no λ { (_ , ηexp⊃ () x) }


-- ----------------------------------------------------------------------------------------------------
