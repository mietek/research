module STLC-Base-Weak-EtaLong where

open import STLC-Base public


----------------------------------------------------------------------------------------------------

-- β-short η-long expanded weak normal forms
mutual
  data ENF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    `λ   : ∀ {A B} {t : A ∷ Γ ⊢ B} → ENF (`λ t)
    `nnf : ∀ {t : Γ ⊢ `◦} (p : ENNF t) → ENF t

  -- neutrals
  data ENNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    `v   : ∀ {A} {i : Γ ∋ A} → ENNF (`v i)
    _`$_ : ∀ {A B} {t₁ : Γ ⊢ A `⊃ B} {t₂ : Γ ⊢ A} (p₁ : ENNF t₁) (p₂ : ENF t₂) → ENNF (t₁ `$ t₂)

-- renaming
mutual
  renENF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → ENF t → ENF (ren e t)
  renENF e `λ       = `λ
  renENF e (`nnf p) = `nnf (renENNF e p)

  renENNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → ENNF t → ENNF (ren e t)
  renENNF e `v         = `v
  renENNF e (p₁ `$ p₂) = renENNF e p₁ `$ renENF e p₂

-- uniqueness of proofs
mutual
  uniENF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : ENF t) → p ≡ p′
  uniENF `λ       `λ        = refl
  uniENF (`nnf p) (`nnf p′) = `nnf & uniENNF p p′

  uniENNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : ENNF t) → p ≡ p′
  uniENNF `v         `v           = refl
  uniENNF (p₁ `$ p₂) (p₁′ `$ p₂′) = _`$_ & uniENNF p₁ p₁′ ⊗ uniENF p₂ p₂′

-- expandability
data Exp {Γ} : ∀ {A} → Γ ⊢ A → Set where
  `v   : ∀ {A B} {i : Γ ∋ A `⊃ B} → Exp (`v i)
  _`$_ : ∀ {A B C} {t₁ : Γ ⊢ A `⊃ B `⊃ C} {t₂ : Γ ⊢ A} → Exp (t₁ `$ t₂)

ENF→¬Exp : ∀ {Γ A} {t : Γ ⊢ A} → ENF t → ¬ Exp t
ENF→¬Exp `λ       ()
ENF→¬Exp (`nnf p) ()

uniExp : ∀ {Γ A} {t : Γ ⊢ A} (x x′ : Exp t) → x ≡ x′
uniExp `v  `v    = refl
uniExp _`$_ _`$_ = refl


----------------------------------------------------------------------------------------------------

-- definitional equality
infix 4 _≝_
data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  refl≝  : ∀ {A} {t : Γ ⊢ A} → t ≝ t
  sym≝   : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
  trans≝ : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
  cong$  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A `⊃ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
           t₁ `$ t₂ ≝ t₁′ `$ t₂′
  βred⊃  : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ]) →
           `λ t₁ `$ t₂ ≝ t′
  ηexp⊃  : ∀ {A B} {t t′ : Γ ⊢ A `⊃ B} (eq : t′ ≡ `λ (weak t `$ `v zero)) → t ≝ t′

open ≝Kit (λ {_} {_} {t} → refl≝ {t = t}) sym≝ trans≝ public


----------------------------------------------------------------------------------------------------

-- call-by-value restricted expansionary reduction; Ghani p.51, table 3-4
mutual
  infix 4 _⇒F_
  data _⇒F_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    embI  : ∀ {A} {t t′ : Γ ⊢ A} (r : t ⇒I t′) → t ⇒F t′
    ηexp⊃ : ∀ {A B} {t t′ : Γ ⊢ A `⊃ B} (eq : t′ ≡ `λ (weak t `$ `v zero)) (x : Exp t) → t ⇒F t′

  infix 4 _⇒I_
  data _⇒I_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    cong$₁  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A `⊃ B} {t₂ : Γ ⊢ A} (r : t₁ ⇒I t₁′) →
              t₁ `$ t₂ ⇒I t₁′ `$ t₂
    congI$₂ : ∀ {A B} {t₁ : Γ ⊢ A `⊃ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : ENF t₁) (r₂ : t₂ ⇒I t₂′) →
              t₁ `$ t₂ ⇒I t₁ `$ t₂′
    congF$₂ : ∀ {A B} {t₁ : Γ ⊢ A `⊃ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : ENF t₁) (r₂ : t₂ ⇒F t₂′) →
              t₁ `$ t₂ ⇒I t₁ `$ t₂′
    βred⊃   : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ])
                (p₂ : ENF t₂) →
              `λ t₁ `$ t₂ ⇒I t′

module F = ⇒Kit _⇒F_
module I = ⇒Kit _⇒I_

mutual
  ENF→¬FR : ∀ {Γ A} {t : Γ ⊢ A} → ENF t → F.¬R t
  ENF→¬FR `λ       (ηexp⊃ refl ())
  ENF→¬FR (`nnf p) r               = r ↯ ENNF→¬FR p

  ENNF→¬FR : ∀ {Γ} {t : Γ ⊢ `◦} → ENNF t → F.¬R t
  ENNF→¬FR p (embI r) = r ↯ ENNF→¬IR p

  ENF→¬IR : ∀ {Γ A} {t : Γ ⊢ A} → ENF t → I.¬R t
  ENF→¬IR (`nnf p) r = r ↯ ENNF→¬IR p

  ENNF→¬IR : ∀ {Γ A} {t : Γ ⊢ A} → ENNF t → I.¬R t
  ENNF→¬IR `v         ()
  ENNF→¬IR (p₁ `$ p₂) (cong$₁ r₁)      = r₁ ↯ ENNF→¬IR p₁
  ENNF→¬IR (p₁ `$ p₂) (congI$₂ p₁′ r₂) = r₂ ↯ ENF→¬IR p₂
  ENNF→¬IR (p₁ `$ p₂) (congF$₂ p₁′ r₂) = r₂ ↯ ENF→¬FR p₂

-- progress?
-- TODO: how to define a notion of normal form that corresponds to ⇒I-irreducibility?
mutual
  postulate
    WTFNF      : ∀ {Γ A} → Γ ⊢ A → Set
    WTFNF→¬FR : ∀ {Γ A} {t : Γ ⊢ A} → WTFNF t → F.¬R t
    prog⇒I    : ∀ {Γ A} (t : Γ ⊢ A) → I.Prog WTFNF t

  prog⇒F : ∀ {Γ A} (t : Γ ⊢ A) → F.Prog ENF t
  prog⇒F {A = A `⊃ B} (`v i)     = F.step (ηexp⊃ refl `v)
  prog⇒F {A = `◦}     (`v i)     = F.done (`nnf `v)
  prog⇒F              (`λ t)     = F.done `λ
  prog⇒F {A = A `⊃ B} (t₁ `$ t₂) = F.step (ηexp⊃ refl _`$_)
  prog⇒F {A = `◦}     (t₁ `$ t₂) with prog⇒I t₁ | prog⇒F t₁ | prog⇒F t₂
  ... | I.step r₁ | _         | _         = F.step (embI (cong$₁ r₁))
  ... | I.done p₁ | F.step r₁ | _         = r₁ ↯ WTFNF→¬FR p₁
  ... | I.done _  | F.done p₁ | F.step r₂ = F.step (embI (congF$₂ p₁ r₂))
  ... | I.done _  | F.done `λ | F.done p₂ = F.step (embI (βred⊃ refl p₂))

-- determinism?
-- TODO: looks unprovable
-- mutual
--   det⇒I : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} (r : t ⇒I t′) (r′ : t ⇒I t″) → t′ ≡ t″
--   det⇒I (cong$₁ r₁)     (cong$₁ r₁′)      = (_`$ _) & det⇒I r₁ r₁′
--   det⇒I (cong$₁ r₁)     (congI$₂ p₁′ r₂′) = r₁ ↯ ENF→¬IR p₁′
--   det⇒I (cong$₁ r₁)     (congF$₂ p₁′ r₂′) = r₁ ↯ ENF→¬IR p₁′
--   det⇒I (congI$₂ p₁ r₂) (cong$₁ r₁′)      = r₁′ ↯ ENF→¬IR p₁
--   det⇒I (congI$₂ p₁ r₂) (congI$₂ p₁′ r₂′) = (_ `$_) & det⇒I r₂ r₂′
--   det⇒I (congI$₂ p₁ r₂) (congF$₂ p₁′ r₂′) = (_ `$_) & det⇒ r₂ r₂′
--   det⇒I (congI$₂ p₁ r₂) (βred⊃ refl p₂′)  = r₂ ↯ ENF→¬IR p₂′
--   det⇒I (congF$₂ p₁ r₂) (cong$₁ r₁′)      = r₁′ ↯ ENF→¬IR p₁
--   det⇒I (congF$₂ p₁ r₂) (congI$₂ p₁′ r₂′) = (_ `$_) & sym (det⇒ r₂′ r₂)
--   det⇒I (congF$₂ p₁ r₂) (congF$₂ p₁′ r₂′) = (_ `$_) & det⇒F r₂ r₂′
--   det⇒I (congF$₂ p₁ r₂) (βred⊃ refl p₂′)  = r₂ ↯ ENF→¬FR p₂′
--   det⇒I (βred⊃ refl p₂) (congI$₂ p₁′ r₂′) = r₂′ ↯ ENF→¬IR p₂
--   det⇒I (βred⊃ refl p₂) (congF$₂ p₁′ r₂′) = r₂′ ↯ ENF→¬FR p₂
--   det⇒I (βred⊃ refl p₂) (βred⊃ refl p₂′)  = refl
--
--   det⇒F : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} (r : t ⇒F t′) (r′ : t ⇒F t″) → t′ ≡ t″
--   det⇒F (embI r)       r′              = det⇒ r r′
--   det⇒F (ηexp⊃ refl x) (embI r′)       = {!!}
--   det⇒F (ηexp⊃ refl x) (ηexp⊃ refl x′) = refl
--
--   det⇒ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} (r : t ⇒I t′) (r′ : t ⇒F t″) → t′ ≡ t″
--   det⇒ r (embI r′)      = det⇒I r r′
--   det⇒ r (ηexp⊃ eq′ x′) = {!!}

-- uniqueness of proofs?
-- TODO: looks unprovable
-- mutual
--   uni⇒I : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒I t′) → r ≡ r′
--   uni⇒I (cong$₁ r₁)     (cong$₁ r₁′)      = cong$₁ & uni⇒I r₁ r₁′
--   uni⇒I (cong$₁ r₁)     (congI$₂ p₁′ r₂′) = r₁ ↯ ENF→¬IR p₁′
--   uni⇒I (cong$₁ r₁)     (congF$₂ p₁′ r₂′) = r₁ ↯ ENF→¬IR p₁′
--   uni⇒I (congI$₂ p₁ r₂) (cong$₁ r₁′)      = r₁′ ↯ ENF→¬IR p₁
--   uni⇒I (congI$₂ p₁ r₂) (congI$₂ p₁′ r₂′) = congI$₂ & uniENF p₁ p₁′ ⊗ uni⇒I r₂ r₂′
--   uni⇒I (congI$₂ p₁ r₂) (congF$₂ p₁′ r₂′) = {!!}
--   uni⇒I (congI$₂ p₁ r₂) (βred⊃ eq′ p₂′)   = r₂ ↯ ENF→¬IR p₂′
--   uni⇒I (congF$₂ p₁ r₂) (cong$₁ r₁′)      = r₁′ ↯ ENF→¬IR p₁
--   uni⇒I (congF$₂ p₁ r₂) (congI$₂ p₁′ r₂′) = {!!}
--   uni⇒I (congF$₂ p₁ r₂) (congF$₂ p₁′ r₂′) = congF$₂ & uniENF p₁ p₁′ ⊗ uni⇒F r₂ r₂′
--   uni⇒I (congF$₂ p₁ r₂) (βred⊃ eq′ p₂′)   = r₂ ↯ ENF→¬FR p₂′
--   uni⇒I (βred⊃ eq p₂)   (congI$₂ p₁′ r₂′) = r₂′ ↯ ENF→¬IR p₂
--   uni⇒I (βred⊃ eq p₂)   (congF$₂ p₁′ r₂′) = r₂′ ↯ ENF→¬FR p₂
--   uni⇒I (βred⊃ refl p₂) (βred⊃ refl p₂′)  = βred⊃ refl & uniENF p₂ p₂′
--
--   uni⇒F : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒F t′) → r ≡ r′
--   uni⇒F (embI r)       (embI r′)       = embI & uni⇒I r r′
--   uni⇒F (embI r)       (ηexp⊃ eq′ x′)  = {!!}
--   uni⇒F (ηexp⊃ eq x)   (embI r′)       = {!!}
--   uni⇒F (ηexp⊃ refl x) (ηexp⊃ refl x′) = ηexp⊃ refl & uniExp x x′


----------------------------------------------------------------------------------------------------

embI* : ∀ {Γ A} {t t′ : Γ ⊢ A} → t I.⇒* t′ → t F.⇒* t′
embI* I.done        = F.done
embI* (I.step r rs) = F.step (embI r) (embI* rs)

-- Ghani p.51, lemma 3.3.0 (unnumbered)
Lem330 : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
Lem330 {A = A} t t′ = t ⇒I t′
                    ⊎ Σ (Ty × Ty) λ { (A′ , B′) →
                        Σ (A ≡ A′ `⊃ B′) λ { refl →
                          t′ ≡ `λ (weak t `$ `v zero) × Exp t } }

FR→lem330 : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒F t′ → Lem330 t t′
FR→lem330 (embI (cong$₁ r₁))     = inj₁ (cong$₁ r₁)
FR→lem330 (embI (congI$₂ p₁ r₂)) = inj₁ (congI$₂ p₁ r₂)
FR→lem330 (embI (congF$₂ p₁ r₂)) = inj₁ (congF$₂ p₁ r₂)
FR→lem330 (embI (βred⊃ eq p₂))   = inj₁ (βred⊃ eq p₂)
FR→lem330 (ηexp⊃ refl x)         = inj₂ (_ , refl , refl , x)

lem330→FR : ∀ {Γ A} {t t′ : Γ ⊢ A} → Lem330 t t′ → t ⇒F t′
lem330→FR (inj₁ r)                     = embI r
lem330→FR (inj₂ (_ , refl , refl , x)) = ηexp⊃ refl x

-- local confluence; Ghani p.53, lemma 3.3.3
-- TODO: needs lemma 3.3.2
-- mutual
--   lconf⇒F : ∀ {Γ A} {t t₁ t₂ : Γ ⊢ A} → t ⇒F t₁ → t ⇒F t₂ →
--              Σ _ λ t′ → t₁ F.⇒* t′ × t₂ F.⇒* t′
--   lconf⇒F {t = `v i}     (ηexp⊃ refl x) (ηexp⊃ refl x′) = _ , F.done , F.done
--   lconf⇒F {t = `λ t}     (embI r)       (embI r′)       with lem333⇒I r r′
--   ... | t′ , inj₁ rs , inj₁ rs′                            = t′ , embI* rs , embI* rs′
--   ... | t′ , inj₁ rs , inj₂ rs′                            = t′ , embI* rs , rs′
--   ... | t′ , inj₂ rs , inj₁ rs′                            = t′ , rs , embI* rs′
--   ... | t′ , inj₂ rs , inj₂ rs′                            = t′ , rs , rs′
--   lconf⇒F {t = t₁ `$ t₂} r r′ = {!!}
--
--   lem333⇒I : ∀ {Γ A} {t t₁ t₂ : Γ ⊢ A} → t ⇒I t₁ → t ⇒I t₂ →
--               Σ _ λ t′ → (t₁ I.⇒* t′ ⊎ t₁ F.⇒* t′) × (t₂ I.⇒* t′ ⊎ t₂ F.⇒* t′)
--   lem333⇒I {t = t₁ `$ t₂} r r′ = {!!}


----------------------------------------------------------------------------------------------------
