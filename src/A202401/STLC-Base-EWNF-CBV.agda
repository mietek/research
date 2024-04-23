----------------------------------------------------------------------------------------------------

-- call-by-value reduction to β-short η-long expanded weak normal form, derived from Ghani
-- TODO: clean up; write up

module A202401.STLC-Base-EWNF-CBV where

open import A202401.STLC-Base-RenSub public
import A202401.STLC-Base-EWNF as F
open F using (⌜λ⌝- ; nnf ; var- ; _⌜$⌝_ ; ∙ ; _,_)
open import A202401.Kit3 public


----------------------------------------------------------------------------------------------------

-- expandability, or neutrals at function type
data Expandable {Γ} : ∀ {A} → Γ ⊢ A → Set where
  var-  : ∀ {A B} {i : Γ ∋ A ⌜⊃⌝ B} → Expandable (var i)
  _⌜$⌝_ : ∀ {A B C} {t₁ : Γ ⊢ A ⌜⊃⌝ B ⌜⊃⌝ C} {t₂ : Γ ⊢ A} (p₁ : F.NNF t₁) (p₂ : F.NF t₂) →
          Expandable (t₁ ⌜$⌝ t₂)

uniExpandable : ∀ {Γ A} {t : Γ ⊢ A} (x x′ : Expandable t) → x ≡ x′
uniExpandable var-        var-          = refl
uniExpandable (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & F.uniNNF p₁ p₁′ ⊗ F.uniNF p₂ p₂′

-- TODO: kit?
data Expandable* {Γ} : ∀ {Δ} → Γ ⊢§ Δ → Set where
  ∙   : Expandable* ∙
  _,_ : ∀ {Δ A} {τ : Γ ⊢§ Δ} {t : Γ ⊢ A} (ξ : Expandable* τ) (x : Expandable t) → Expandable* (τ , t)

FNNF→Expandable : ∀ {Γ A B} {t : Γ ⊢ A ⌜⊃⌝ B} → F.NNF t → Expandable t
FNNF→Expandable var-        = var-
FNNF→Expandable (p₁ ⌜$⌝ p₂) = p₁ ⌜$⌝ p₂

Expandable→FNNF : ∀ {Γ A B} {t : Γ ⊢ A ⌜⊃⌝ B} → Expandable t → F.NNF t
Expandable→FNNF var-        = var-
Expandable→FNNF (p₁ ⌜$⌝ p₂) = p₁ ⌜$⌝ p₂

-- TODO: delete?
-- FNF→¬Expandable : ∀ {Γ A} {t : Γ ⊢ A} → FNF t → ¬ Expandable t
-- FNF→¬Expandable ⌜λ⌝-    ()
-- FNF→¬Expandable (nnf p) ()

Expandable→¬FNF : ∀ {Γ A} {t : Γ ⊢ A} → Expandable t → ¬ F.NF t
Expandable→¬FNF var-        ()
Expandable→¬FNF (p₁ ⌜$⌝ p₂) ()

uni¬Expandable : ∀ {Γ A} {t : Γ ⊢ A} (¬x ¬x′ : ¬ Expandable t) → ¬x ≡ ¬x′
uni¬Expandable = uni¬


----------------------------------------------------------------------------------------------------

data _ExpandsTo_ {Γ} : ∀ {A} (t t′ : Γ ⊢ A) → Set where
  ηexp⊃ : ∀ {A B} {t t′ : Γ ⊢ A ⌜⊃⌝ B} (eq : t′ ≡ ⌜λ⌝ (wk t ⌜$⌝ var zero)) (x : Expandable t) →
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
INF t = F.NF t × ¬ Expanded t

-- TODO: delete?
-- INNF : ∀ {Γ A} → Γ ⊢ A → Set
-- INNF t = FNNF t × ¬ Expanded t

INF→FNF : ∀ {Γ A} {t : Γ ⊢ A} → INF t → F.NF t
INF→FNF (p , _) = p

-- TODO: delete?
-- INNF→FNNF : ∀ {Γ A} {t : Γ ⊢ A} → INNF t → FNNF t
-- INNF→FNNF (p , _) = p

uniINF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : INF t) → p ≡ p′
uniINF (p , ¬x) (p′ , ¬x′) = _,_ & F.uniNF p p′ ⊗ uni¬Expanded ¬x ¬x′


----------------------------------------------------------------------------------------------------

-- call-by-value restricted expansionary reduction (derived from Ghani p.51, table 3-4)

-- NOTE: modified by removing duplicate rules from `_⇒F_` and replacing them with `Ired`,
--       and by adding `FNF` constraints to `Icong$₂`, `Fcong$₂`, and `βred⊃`
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
--     cong$₁  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r₁ : t₁ ⇒I t₁′) →
--               t₁ ⌜$⌝ t₂ ⇒I t₁′ ⌜$⌝ t₂
--     Icong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : FNF t₁) (r₂ : t₂ ⇒I t₂′) →
--               t₁ ⌜$⌝ t₂ ⇒I t₁ ⌜$⌝ t₂′
--     Fcong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : FNF t₁) (r₂ : t₂ ⇒F t₂′) →
--               t₁ ⌜$⌝ t₂ ⇒I t₁ ⌜$⌝ t₂′
--     βred⊃   : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ])
--                 (p₂ : FNF t₂) →
--               ⌜λ⌝ t₁ ⌜$⌝ t₂ ⇒I t′

mutual
  -- NOTE: further modified by adding constraint to `Ired`
  infix 4 _⇒F_
  data _⇒F_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    Ired  : ∀ {A} {t t′ : Γ ⊢ A} (¬x : ¬ Expandable t) (r : t ⇒I t′) → t ⇒F t′
    ηexp⊃ : ∀ {A B} {t : Γ ⊢ A ⌜⊃⌝ B} {t′} (eq : t′ ≡ wk t) (x : Expandable t) →
            t ⇒F ⌜λ⌝ (t′ ⌜$⌝ var zero)

  -- NOTE: further modified by removing `Icong$₂` and adding `Xcong$₂`
  infix 4 _⇒I_
  data _⇒I_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    cong$₁  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r₁ : t₁ ⇒I t₁′) →
              t₁ ⌜$⌝ t₂ ⇒I t₁′ ⌜$⌝ t₂
    Fcong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : F.NF t₁) (r₂ : t₂ ⇒F t₂′) →
              t₁ ⌜$⌝ t₂ ⇒I t₁ ⌜$⌝ t₂′
    Xcong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (x₁ : Expandable t₁) (r₂ : t₂ ⇒F t₂′) →
              t₁ ⌜$⌝ t₂ ⇒I t₁ ⌜$⌝ t₂′
    βred⊃   : ∀ {A B} {t₁ : Γ , A ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) (p₂ : F.NF t₂) →
              ⌜λ⌝ t₁ ⌜$⌝ t₂ ⇒I t′

module RK1F = RedKit1 (kit tmkit _⇒F_)
module RK1I = RedKit1 (kit tmkit _⇒I_)

mutual
  FNF→¬FR : ∀ {Γ A} {t : Γ ⊢ A} → F.NF t → RK1F.¬R t
  FNF→¬FR ⌜λ⌝-    (ηexp⊃ refl ())
  FNF→¬FR (nnf p) r               = r ↯ FNNF→¬FR p

  FNNF→¬FR : ∀ {Γ} {t : Γ ⊢ ⌜◦⌝} → F.NNF t → RK1F.¬R t
  FNNF→¬FR p (Ired ¬x r) = r ↯ FNNF→¬IR p

  FNF→¬IR : ∀ {Γ A} {t : Γ ⊢ A} → F.NF t → RK1I.¬R t
  FNF→¬IR (nnf p) r = r ↯ FNNF→¬IR p

  FNNF→¬IR : ∀ {Γ A} {t : Γ ⊢ A} → F.NNF t → RK1I.¬R t
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

module RK2F = RedKit2 (kit RK1F.redkit1 F.uniNF FNF→¬FR)
module RK2I = RedKit2 (kit RK1I.redkit1 uniINF INF→¬IR)


----------------------------------------------------------------------------------------------------

Expandable→¬IR : ∀ {Γ A B} {t : Γ ⊢ A ⌜⊃⌝ B} → Expandable t → RK1I.¬R t
Expandable→¬IR = FNNF→¬IR ∘ Expandable→FNNF

-- TODO: delete?
-- ¬FR→¬Expandable : ∀ {A Γ} {t : Γ ⊢ A} → RK1F.¬R t → ¬ Expandable t
-- ¬FR→¬Expandable {A ⌜⊃⌝ B} {t = var i}     ¬r x = ηexp⊃ refl x ↯ ¬r
-- ¬FR→¬Expandable {A ⌜⊃⌝ B} {t = t₁ ⌜$⌝ t₂} ¬r x = ηexp⊃ refl x ↯ ¬r
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
  uni⇒I (Fcong$₂ p₁ r₂) (Fcong$₂ p₁′ r₂′) = Fcong$₂ & F.uniNF p₁ p₁′ ⊗ uni⇒F r₂ r₂′
  uni⇒I (Fcong$₂ p₁ r₂) (Xcong$₂ x₁′ r₂′) = p₁ ↯ Expandable→¬FNF x₁′
  uni⇒I (Fcong$₂ p₁ r₂) (βred⊃ eq′ p₂′)   = r₂ ↯ FNF→¬FR p₂′
  uni⇒I (Xcong$₂ x₁ r₂) (cong$₁ r₁′)      = r₁′ ↯ Expandable→¬IR x₁
  uni⇒I (Xcong$₂ x₁ r₂) (Fcong$₂ p₁′ r₂′) = p₁′ ↯ Expandable→¬FNF x₁
  uni⇒I (Xcong$₂ x₁ r₂) (Xcong$₂ x₁′ r₂′) = Xcong$₂ & uniExpandable x₁ x₁′ ⊗ uni⇒F r₂ r₂′
  uni⇒I (βred⊃ eq p₂)   (Fcong$₂ p₁′ r₂′) = r₂′ ↯ FNF→¬FR p₂
  uni⇒I (βred⊃ refl p₂) (βred⊃ refl p₂′)  = βred⊃ refl & F.uniNF p₂ p₂′

module DKF = DetKit (kit RK2F.redkit2 det⇒F uni⇒F)
module DKI = DetKit (kit RK2I.redkit2 det⇒I uni⇒I)


----------------------------------------------------------------------------------------------------

prog⇒F : ∀ {A Γ} (t : Γ ⊢ A) → RK2F.Prog t
prog⇒F {⌜◦⌝}     (var i)                    = RK2F.done (nnf var-)
prog⇒F {⌜◦⌝}     (t₁ ⌜$⌝ t₂)                with prog⇒F t₁ | prog⇒F t₂
... | RK2F.step (Ired ¬x₁ r₁) | _              = RK2F.step (Ired (λ ()) (cong$₁ r₁))
... | RK2F.step (ηexp⊃ eq x₁) | RK2F.step r₂   = RK2F.step (Ired (λ ()) (Xcong$₂ x₁ r₂))
... | RK2F.step (ηexp⊃ eq x₁) | RK2F.done p₂   = RK2F.done (nnf (Expandable→FNNF x₁ ⌜$⌝ p₂))
... | RK2F.done p₁            | RK2F.step r₂   = RK2F.step (Ired (λ ()) (Fcong$₂ p₁ r₂))
... | RK2F.done ⌜λ⌝-          | RK2F.done p₂   = RK2F.step (Ired (λ ()) (βred⊃ refl p₂))
prog⇒F {A ⌜⊃⌝ B} (var i)                      = RK2F.step (ηexp⊃ refl var-)
prog⇒F {A ⌜⊃⌝ B} (⌜λ⌝ t)                      = RK2F.done ⌜λ⌝-
prog⇒F {A ⌜⊃⌝ B} (t₁ ⌜$⌝ t₂)                with prog⇒F t₁ | prog⇒F t₂
... | RK2F.step (Ired ¬x₁ r₁) | _              = RK2F.step (Ired (λ { (p₁ ⌜$⌝ p₂) →
                                                   FNNF→Expandable p₁ ↯ ¬x₁ }) (cong$₁ r₁))
... | RK2F.step (ηexp⊃ eq x₁) | RK2F.step r₂   = RK2F.step (Ired (λ { (p₁ ⌜$⌝ p₂) →
                                                   r₂ ↯ FNF→¬FR p₂ }) (Xcong$₂ x₁ r₂))
... | RK2F.step (ηexp⊃ eq x₁) | RK2F.done p₂   = RK2F.step (ηexp⊃ refl (Expandable→FNNF x₁ ⌜$⌝ p₂))
... | RK2F.done ⌜λ⌝-          | RK2F.step r₂   = RK2F.step (Ired (λ { (() ⌜$⌝ p₂′) }) (Fcong$₂ ⌜λ⌝- r₂))
... | RK2F.done ⌜λ⌝-          | RK2F.done p₂   = RK2F.step (Ired (λ { (() ⌜$⌝ p₂′) }) (βred⊃ refl p₂))

-- TODO: progress doesn’t seem provable for _⇒I_, but maybe that’s okay?
-- prog⇒I : ∀ {Γ A} (t : Γ ⊢ A) → RK2I.Prog t
-- prog⇒I t = {pp}

module PKF = ProgKit (kit RK2F.redkit2 prog⇒F)


----------------------------------------------------------------------------------------------------

renExpandable : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → Expandable t → Expandable (ren ϱ t)
renExpandable ϱ var-        = var-
renExpandable ϱ (p₁ ⌜$⌝ p₂) = F.renNNF ϱ p₁ ⌜$⌝ F.renNF ϱ p₂

ren¬Expandable : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → ¬ Expandable t → ¬ Expandable (ren ϱ t)
ren¬Expandable {t = var i}     ϱ ¬x var-        = var- ↯ ¬x
ren¬Expandable {t = t₁ ⌜$⌝ t₂} ϱ ¬x (p₁ ⌜$⌝ p₂) = (F.nerNNF ϱ p₁ ⌜$⌝ F.nerNF ϱ p₂) ↯ ¬x

mutual
  ren⇒F : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → t ⇒F t′ → ren ϱ t ⇒F ren ϱ t′
  ren⇒F ϱ (Ired ¬x r)    = Ired (ren¬Expandable ϱ ¬x) (ren⇒I ϱ r)
  ren⇒F ϱ (ηexp⊃ refl x) = ηexp⊃ (eqwkren ϱ _) (renExpandable ϱ x)

  ren⇒I : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → t ⇒I t′ → ren ϱ t ⇒I ren ϱ t′
  ren⇒I ϱ (cong$₁ r₁)               = cong$₁ (ren⇒I ϱ r₁)
  ren⇒I ϱ (Fcong$₂ p₁ r₂)           = Fcong$₂ (F.renNF ϱ p₁) (ren⇒F ϱ r₂)
  ren⇒I ϱ (Xcong$₂ x₁ r₂)           = Xcong$₂ (renExpandable ϱ x₁) (ren⇒F ϱ r₂)
  ren⇒I ϱ (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (rencut ϱ t₁ _ ⁻¹) (F.renNF ϱ p₂)

sub∋Expandable : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {i : Γ ∋ A} → Expandable* σ → Expandable (sub∋ σ i)
sub∋Expandable {i = zero}  (ξ , x) = x
sub∋Expandable {i = wk∋ i} (ξ , x) = sub∋Expandable ξ

subExpandable : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} → F.NNF§ σ → Expandable* σ → Expandable t →
                Expandable (sub σ t)
subExpandable ψ ξ var-        = sub∋Expandable ξ
subExpandable ψ ξ (p₁ ⌜$⌝ p₂) = F.subNNF ψ p₁ ⌜$⌝ F.subNF ψ p₂

sub¬Expandable : ∀ {A Γ Ξ} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} → F.NNF§ σ → ¬ Expandable t →
                 ¬ Expandable (sub σ t)
sub¬Expandable {A ⌜⊃⌝ B} {t = var i}     ψ ¬x x           = var- ↯ ¬x
sub¬Expandable {A ⌜⊃⌝ B} {t = t₁ ⌜$⌝ t₂} ψ ¬x (p₁ ⌜$⌝ p₂) = (F.busNNF ψ p₁ ⌜$⌝ F.busNF ψ p₂) ↯ ¬x

mutual
  sub⇒I : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t t′ : Γ ⊢ A} → F.NNF§ σ → Expandable* σ → t ⇒I t′ →
           sub σ t ⇒I sub σ t′
  sub⇒I ψ ξ (cong$₁ r₁)               = cong$₁ (sub⇒I ψ ξ r₁)
  sub⇒I ψ ξ (Fcong$₂ p₁ r₂)           = Fcong$₂ (F.subNF ψ p₁) (sub⇒F ψ ξ r₂)
  sub⇒I ψ ξ (Xcong$₂ x₁ r₂)           = Xcong$₂ (subExpandable ψ ξ x₁) (sub⇒F ψ ξ r₂)
  sub⇒I ψ ξ (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (subcut _ t₁ _ ⁻¹) (F.subNF ψ p₂)

  sub⇒F : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t t′ : Γ ⊢ A} → F.NNF§ σ → Expandable* σ → t ⇒F t′ →
           sub σ t ⇒F sub σ t′
  sub⇒F ψ ξ (Ired ¬x r)            = Ired (sub¬Expandable ψ ¬x) (sub⇒I ψ ξ r)
  sub⇒F ψ ξ (ηexp⊃ {t = t} refl x) = ηexp⊃ (eqwksub _ t) (subExpandable ψ ξ x)


----------------------------------------------------------------------------------------------------

Expandable? : ∀ {A Γ} (t : Γ ⊢ A) → Dec (Expandable t)
Expandable? {⌜◦⌝}     t           = no λ ()
Expandable? {A ⌜⊃⌝ B} (var i)     = yes var-
Expandable? {A ⌜⊃⌝ B} (⌜λ⌝ t)     = no λ ()
Expandable? {A ⌜⊃⌝ B} (t₁ ⌜$⌝ t₂) with F.NNF? t₁ | F.NF? t₂
... | no ¬p₁ | _                    = no λ { (p₁ ⌜$⌝ p₂) → p₁ ↯ ¬p₁ }
... | yes p₁ | no ¬p₂               = no λ { (p₁ ⌜$⌝ p₂) → p₂ ↯ ¬p₂ }
... | yes p₁ | yes p₂               = yes (p₁ ⌜$⌝ p₂)

-- (Ghani p.51, unnumbered lemma)
FR→IR⊎ExpandsTo : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒F t′ → t ⇒I t′ ⊎ t ExpandsTo t′
FR→IR⊎ExpandsTo (Ired ¬x (cong$₁ r₁))     = left (cong$₁ r₁)
FR→IR⊎ExpandsTo (Ired ¬x (Fcong$₂ p₁ r₂)) = left (Fcong$₂ p₁ r₂)
FR→IR⊎ExpandsTo (Ired ¬x (Xcong$₂ x₁ r₂)) = left (Xcong$₂ x₁ r₂)
FR→IR⊎ExpandsTo (Ired ¬x (βred⊃ eq p₂))   = left (βred⊃ eq p₂)
FR→IR⊎ExpandsTo (ηexp⊃ refl x)            = right (ηexp⊃ refl x)

IR⊎ExpandsTo→FR : ∀ {A Γ} {t t′ : Γ ⊢ A} → t ⇒I t′ ⊎ t ExpandsTo t′ → t ⇒F t′
IR⊎ExpandsTo→FR {⌜◦⌝}     {t = t} (left r)               = Ired (λ ()) r
IR⊎ExpandsTo→FR {A ⌜⊃⌝ B} {t = t} (left r)               with Expandable? t
... | yes x                                                 = r ↯ Expandable→¬IR x
... | no ¬x                                                 = Ired ¬x r
IR⊎ExpandsTo→FR                   (right (ηexp⊃ refl x)) = ηexp⊃ refl x


----------------------------------------------------------------------------------------------------

-- -- TODO: delete?
-- _ExpandsTo?_ : ∀ {Γ A} (t t′ : Γ ⊢ A) → Dec (t ExpandsTo t′)
-- var i       ExpandsTo? var i′                            = no λ { (ηexp⊃ () x) }
-- var i       ExpandsTo? ⌜λ⌝ (var i′)                      = no λ { (ηexp⊃ () x) }
-- var i       ExpandsTo? ⌜λ⌝ (⌜λ⌝ t′)                      = no λ { (ηexp⊃ () x) }
-- var i       ExpandsTo? ⌜λ⌝ (var i′ ⌜$⌝ var zero)         with wk∋ i ≟∋ i′ -- TODO: bitrot due to wk∋ change
-- ... | no ¬eq                                               = no λ { (ηexp⊃ refl x) → {!refl ↯ ¬eq!} }
-- ... | yes refl                                             = yes (ηexp⊃ {!refl!} var-)
-- var i       ExpandsTo? ⌜λ⌝ (var i′ ⌜$⌝ var (wk∋ _))      = no λ { (ηexp⊃ () x) }
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
-- ... | yes refl                                             with F.NNF? t₁ | F.NF? t₂
-- ...   | no ¬p₁ | _                                           = no λ { (ηexp⊃ refl (p₁ ⌜$⌝ p₂)) →
--                                                                  p₁ ↯ ¬p₁ }
-- ...   | yes p₁ | no ¬p₂                                      = no λ { (ηexp⊃ refl (p₁′ ⌜$⌝ p₂)) →
--                                                                  p₂ ↯ ¬p₂ }
-- ...   | yes p₁ | yes p₂                                      = yes (ηexp⊃ refl (p₁ ⌜$⌝ p₂))
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (t₁′ ⌜$⌝ t₂′ ⌜$⌝ var (wk∋ _)) = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (t₁′ ⌜$⌝ t₂′ ⌜$⌝ ⌜λ⌝ _)       = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? ⌜λ⌝ (t₁′ ⌜$⌝ t₂′ ⌜$⌝ (_ ⌜$⌝ _))   = no λ { (ηexp⊃ () x) }
-- (t₁ ⌜$⌝ t₂) ExpandsTo? (t₁′ ⌜$⌝ t₂′)                     = no λ { (ηexp⊃ () x) }

-- private
--   lem₀ : ∀ {Γ A A′ B C} {t₁ : Γ ⊢ A ⌜⊃⌝ B ⌜⊃⌝ C} {t₁′ : Γ ⊢ A′ ⌜⊃⌝ B ⌜⊃⌝ C}
--            {t₂ : Γ ⊢ A} {t₂′ : Γ ⊢ A′} →
--            ⌜λ⌝ ((wk t₁ ⌜$⌝ wk t₂) ⌜$⌝ var zero) ≡ ⌜λ⌝ ((wk t₁′ ⌜$⌝ wk t₂′) ⌜$⌝ var zero) →
--          Σ (A ≡ A′) λ { refl → t₁ ≡ t₁′ × t₂ ≡ t₂′ }
--   lem₀ eq with inj$₁′ (inj$₁ (injλ eq))
--   ... | refl , eq₁ = refl , injren eq₁ , injren (inj$₂ (inj$₁ (injλ eq)))

--   lem₁ : ∀ {Γ A A′ B C} {t₁ : Γ ⊢ A ⌜⊃⌝ B ⌜⊃⌝ C} {t₁′ : Γ ⊢ A′ ⌜⊃⌝ B ⌜⊃⌝ C}
--            {t₂ : Γ ⊢ A} {t₂′ : Γ ⊢ A′} →
--            ⌜λ⌝ ((wk t₁ ⌜$⌝ wk t₂) ⌜$⌝ var zero) ≡ ⌜λ⌝ ((wk t₁′ ⌜$⌝ wk t₂′) ⌜$⌝ var zero) →
--          ¬ F.NNF t₁ → ¬ F.NNF t₁′
--   lem₁ eq ¬p₁ p₁ with lem₀ eq
--   ... | refl , refl , refl = p₁ ↯ ¬p₁

--   lem₂ : ∀ {Γ A A′ B C} {t₁ : Γ ⊢ A ⌜⊃⌝ B ⌜⊃⌝ C} {t₁′ : Γ ⊢ A′ ⌜⊃⌝ B ⌜⊃⌝ C}
--            {t₂ : Γ ⊢ A} {t₂′ : Γ ⊢ A′} →
--            ⌜λ⌝ ((wk t₁ ⌜$⌝ wk t₂) ⌜$⌝ var zero) ≡ ⌜λ⌝ ((wk t₁′ ⌜$⌝ wk t₂′) ⌜$⌝ var zero) →
--          ¬ F.NF t₂ → ¬ F.NF t₂′
--   lem₂ eq ¬p₂ p₂ with lem₀ eq
--   ... | refl , refl , refl = p₂ ↯ ¬p₂

-- Expanded? : ∀ {Γ A} (t′ : Γ ⊢ A) → Dec (Expanded t′)
-- Expanded? (var i′)                      = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (var i′))                = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (⌜λ⌝ t′))                = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (t′ ⌜$⌝ var zero))       with unren (wk⊑ id⊑) t′
-- ... | no ¬p                               = no λ { (_ , ηexp⊃ refl x) → (_ , refl) ↯ ¬p }
-- ... | yes (var i , refl)                  = yes (_ , ηexp⊃ refl var-)
-- ... | yes (⌜λ⌝ t , refl)                  = no λ { (var _ , ηexp⊃ () x)
--                                                  ; (⌜λ⌝ _ , ηexp⊃ eq ())
--                                                  ; (_ ⌜$⌝ _ , ηexp⊃ () x)
--                                                  }
-- ... | yes (t₁ ⌜$⌝ t₂ , refl)              with F.NNF? t₁ | F.NF? t₂
-- ...   | no ¬p₁ | _                          = no λ { (_ , ηexp⊃ eq (p₁ ⌜$⌝ p₂)) →
--                                                 p₁ ↯ lem₁ eq ¬p₁ }
-- ...   | yes p₁ | no ¬p₂                     = no λ { (_ , ηexp⊃ eq (p₁′ ⌜$⌝ p₂)) →
--                                                 p₂ ↯ lem₂ eq ¬p₂ }
-- ...   | yes p₁ | yes p₂                     = yes (_ , ηexp⊃ refl (p₁ ⌜$⌝ p₂))
-- Expanded? (⌜λ⌝ (t′ ⌜$⌝ var (wk∋ i′)))   = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (t₁′ ⌜$⌝ ⌜λ⌝ t₂′))       = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (⌜λ⌝ (t₁′ ⌜$⌝ t₂′@(_ ⌜$⌝ _))) = no λ { (_ , ηexp⊃ () x) }
-- Expanded? (t₁′ ⌜$⌝ t₂′)                 = no λ { (_ , ηexp⊃ () x) }


-- ----------------------------------------------------------------------------------------------------
