module STLC-Naturals-Weak-NotEtaLong where

open import STLC-Naturals-Properties public
open import Kit3 public


----------------------------------------------------------------------------------------------------

-- β-short not-η-long semi-weak normal forms
-- TODO: try making ⌜suc⌝ weak
mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝-   : ∀ {A B} {t : A ∷ Γ ⊢ B} → NF (⌜λ⌝ t)
    ⌜zero⌝ : NF ⌜zero⌝
    ⌜suc⌝  : ∀ {t : Γ ⊢ ⌜ℕ⌝} (p : NF t) → NF (⌜suc⌝ t)
    nnf    : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → NNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)
    ⌜rec⌝ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {t₁ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} (pₙ : NNF tₙ) (p₀ : NF t₀)
              (p₁ : NF t₁) →
            NNF (⌜rec⌝ tₙ t₀ t₁)

data NNF* {Γ} : ∀ {Δ} → Γ ⊢* Δ → Set where
  []  : NNF* []
  _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} → NNF t → NNF* ts → NNF* (t ∷ ts)

mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF ⌜λ⌝-      ⌜λ⌝-       = refl
  uniNF ⌜zero⌝    ⌜zero⌝     = refl
  uniNF (⌜suc⌝ p) (⌜suc⌝ p′) = ⌜suc⌝ & uniNF p p′
  uniNF (nnf p)   (nnf p′)   = nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
  uniNNF var-             var-                = refl
  uniNNF (p₁ ⌜$⌝ p₂)      (p₁′ ⌜$⌝ p₂′)       = _⌜$⌝_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′
  uniNNF (⌜rec⌝ pₙ p₀ pₛ) (⌜rec⌝ pₙ′ p₀′ pₛ′) = ⌜rec⌝ & uniNNF pₙ pₙ′ ⊗ uniNF p₀ p₀′ ⊗ uniNF pₛ pₛ′


----------------------------------------------------------------------------------------------------

-- call-by-value reduction
infix 4 _⇒_
data _⇒_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  cong$₁   : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r₁ : t₁ ⇒ t₁′) →
             t₁ ⌜$⌝ t₂ ⇒ t₁′ ⌜$⌝ t₂
  cong$₂   : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : NF t₁) (r₂ : t₂ ⇒ t₂′) →
             t₁ ⌜$⌝ t₂ ⇒ t₁ ⌜$⌝ t₂′
  congsuc  : ∀ {t t′ : Γ ⊢ ⌜ℕ⌝} (r : t ⇒ t′) → ⌜suc⌝ t ⇒ ⌜suc⌝ t′
  congrecₙ : ∀ {A} {tₙ tₙ′ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} (rₙ : tₙ ⇒ tₙ′) →
             ⌜rec⌝ tₙ t₀ tₛ ⇒ ⌜rec⌝ tₙ′ t₀ tₛ
  congrec₀ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ t₀′ : Γ ⊢ A} {tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} (pₙ : NF tₙ)
               (r₀ : t₀ ⇒ t₀′) →
             ⌜rec⌝ tₙ t₀ tₛ ⇒ ⌜rec⌝ tₙ t₀′ tₛ
  congrecₛ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ tₛ′ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} (pₙ : NF tₙ)
               (p₀ : NF t₀) (rₛ : tₛ ⇒ tₛ′) →
             ⌜rec⌝ tₙ t₀ tₛ ⇒ ⌜rec⌝ tₙ t₀ tₛ′
  βred⊃    : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) (p₂ : NF t₂) →
             ⌜λ⌝ t₁ ⌜$⌝ t₂ ⇒ t′
  βredℕ₀   : ∀ {A} {t₀ : Γ ⊢ A} {tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} (p₀ : NF t₀) (pₛ : NF tₛ) →
             ⌜rec⌝ ⌜zero⌝ t₀ tₛ ⇒ t₀
  βredℕₛ   : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ : A ∷ ⌜ℕ⌝ ∷ Γ ⊢ A} {t′}
               (eq : t′ ≡ tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ] [ tₙ ]) → (pₙ : NF (⌜suc⌝ tₙ)) (p₀ : NF t₀)
               (pₛ : NF tₛ) →
             ⌜rec⌝ (⌜suc⌝ tₙ) t₀ tₛ ⇒ t′

open RedKit1 (kit tmkit _⇒_) public

mutual
  NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t
  NF→¬R (⌜suc⌝ p) (congsuc r) = r ↯ NF→¬R p
  NF→¬R (nnf p) r           = r ↯ NNF→¬R p

  NNF→¬R : ∀ {Γ A} {t  : Γ ⊢ A} → NNF t → ¬R t
  NNF→¬R (p₁ ⌜$⌝ p₂)      (cong$₁ r₁)           = r₁ ↯ NNF→¬R p₁
  NNF→¬R (p₁ ⌜$⌝ p₂)      (cong$₂ p₁′ r₂)       = r₂ ↯ NF→¬R p₂
  NNF→¬R (() ⌜$⌝ p₂)      (βred⊃ eq p₂′)
  NNF→¬R (⌜rec⌝ pₙ p₀ pₛ) (congrecₙ rₙ)         = rₙ ↯ NNF→¬R pₙ
  NNF→¬R (⌜rec⌝ pₙ p₀ pₛ) (congrec₀ pₙ′ r₀)     = r₀ ↯ NF→¬R p₀
  NNF→¬R (⌜rec⌝ pₙ p₀ pₛ) (congrecₛ pₙ′ p₀′ rₛ) = rₛ ↯ NF→¬R pₛ

open RedKit2 (kit redkit1 uniNF NF→¬R) public


----------------------------------------------------------------------------------------------------

det⇒ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒ t″ → t′ ≡ t″
det⇒ (cong$₁ r₁)            (cong$₁ r₁′)              = (_⌜$⌝ _) & det⇒ r₁ r₁′
det⇒ (cong$₁ r₁)            (cong$₂ p₁′ r₂′)          = r₁ ↯ NF→¬R p₁′
det⇒ (cong$₂ p₁ r₂)         (cong$₁ r₁′)              = r₁′ ↯ NF→¬R p₁
det⇒ (cong$₂ p₁ r₂)         (cong$₂ p₁′ r₂′)          = (_ ⌜$⌝_) & det⇒ r₂ r₂′
det⇒ (cong$₂ p₁ r₂)         (βred⊃ refl p₂′)          = r₂ ↯ NF→¬R p₂′
det⇒ (congsuc r)            (congsuc r′)              = ⌜suc⌝ & det⇒ r r′
det⇒ (congrecₙ rₙ)          (congrecₙ rₙ′)            = _ & det⇒ rₙ rₙ′
det⇒ (congrecₙ rₙ)          (congrec₀ pₙ′ r₀′)        = rₙ ↯ NF→¬R pₙ′
det⇒ (congrecₙ rₙ)          (congrecₛ pₙ′ p₀′ rₛ′)    = rₙ ↯ NF→¬R pₙ′
det⇒ (congrecₙ rₙ)          (βredℕₛ refl pₙ′ p₀′ pₛ′) = rₙ ↯ NF→¬R pₙ′
det⇒ (congrec₀ pₙ r₀)       (congrecₙ rₙ′)            = rₙ′ ↯ NF→¬R pₙ
det⇒ (congrec₀ pₙ r₀)       (congrec₀ pₙ′ r₀′)        = _ & uniNF pₙ pₙ′ ⊗ det⇒ r₀ r₀′
det⇒ (congrec₀ pₙ r₀)       (congrecₛ pₙ′ p₀′ rₛ′)    = r₀ ↯ NF→¬R p₀′
det⇒ (congrec₀ pₙ r₀)       (βredℕ₀ p₀′ pₛ′)          = r₀ ↯ NF→¬R p₀′
det⇒ (congrec₀ pₙ r₀)       (βredℕₛ refl pₙ′ p₀′ pₛ′) = r₀ ↯ NF→¬R p₀′
det⇒ (congrecₛ pₙ p₀ rₛ)    (congrecₙ rₙ′)            = rₙ′ ↯ NF→¬R pₙ
det⇒ (congrecₛ pₙ p₀ rₛ)    (congrec₀ pₙ′ r₀′)        = r₀′ ↯ NF→¬R p₀
det⇒ (congrecₛ pₙ p₀ rₛ)    (congrecₛ pₙ′ p₀′ rₛ′)    = _ & uniNF pₙ pₙ′ ⊗ uniNF p₀ p₀
                                                           ⊗ det⇒ rₛ rₛ′
det⇒ (congrecₛ pₙ p₀ rₛ)    (βredℕ₀ p₀′ pₛ′)          = rₛ ↯ NF→¬R pₛ′
det⇒ (congrecₛ pₙ p₀ rₛ)    (βredℕₛ refl pₙ′ p₀′ pₛ′) = rₛ ↯ NF→¬R pₛ′
det⇒ (βred⊃ refl p₂)        (cong$₂ p₁′ r₂′)          = r₂′ ↯ NF→¬R p₂
det⇒ (βred⊃ refl p₂)        (βred⊃ refl p₂′)          = refl
det⇒ (βredℕ₀ p₀ pₛ)         (congrec₀ pₙ′ r₀′)        = r₀′ ↯ NF→¬R p₀
det⇒ (βredℕ₀ p₀ pₛ)         (congrecₛ pₙ′ p₀′ rₛ′)    = rₛ′ ↯ NF→¬R pₛ
det⇒ (βredℕ₀ p₀ pₛ)         (βredℕ₀ p₀′ pₛ′)          = refl
det⇒ (βredℕₛ refl pₙ p₀ pₛ) (congrecₙ rₙ′)            = rₙ′ ↯ NF→¬R pₙ
det⇒ (βredℕₛ refl pₙ p₀ pₛ) (congrec₀ pₙ′ r₀′)        = r₀′ ↯ NF→¬R p₀
det⇒ (βredℕₛ refl pₙ p₀ pₛ) (congrecₛ pₙ′ p₀′ rₛ′)    = rₛ′ ↯ NF→¬R pₛ
det⇒ (βredℕₛ refl pₙ p₀ pₛ) (βredℕₛ refl pₙ′ p₀′ pₛ′) = refl

uni⇒ : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒ t′) → r ≡ r′
uni⇒ (cong$₁ r₁)            (cong$₁ r₁′)              = cong$₁ & uni⇒ r₁ r₁′
uni⇒ (cong$₁ r₁)            (cong$₂ p₁′ r₂′)          = r₁ ↯ NF→¬R p₁′
uni⇒ (cong$₂ p₁ r₂)         (cong$₁ r₁′)              = r₁′ ↯ NF→¬R p₁
uni⇒ (cong$₂ p₁ r₂)         (cong$₂ p₁′ r₂′)          = cong$₂ & uniNF p₁ p₁′ ⊗ uni⇒ r₂ r₂′
uni⇒ (cong$₂ p₁ r₂)         (βred⊃ eq′ p₂)            = r₂ ↯ NF→¬R p₂
uni⇒ (congsuc r)            (congsuc r′)              = congsuc & uni⇒ r r′
uni⇒ (congrecₙ rₙ)          (congrecₙ rₙ′)            = congrecₙ & uni⇒ rₙ rₙ′
uni⇒ (congrecₙ rₙ)          (congrec₀ pₙ′ r₀′)        = rₙ ↯ NF→¬R pₙ′
uni⇒ (congrecₙ rₙ)          (congrecₛ pₙ′ p₀′ rₛ′)    = rₙ ↯ NF→¬R pₙ′
uni⇒ (congrecₙ rₙ)          (βredℕₛ eq′ pₙ′ p₀′ pₛ′)  = rₙ ↯ NF→¬R pₙ′
uni⇒ (congrec₀ pₙ r₀)       (congrecₙ rₙ′)            = rₙ′ ↯ NF→¬R pₙ
uni⇒ (congrec₀ pₙ r₀)       (congrec₀ pₙ′ r₀′)        = congrec₀ & uniNF pₙ pₙ′ ⊗ uni⇒ r₀ r₀′
uni⇒ (congrec₀ pₙ r₀)       (congrecₛ pₙ′ p₀′ rₛ′)    = r₀ ↯ NF→¬R p₀′
uni⇒ (congrec₀ pₙ r₀)       (βredℕ₀ p₀′ pₛ′)          = r₀ ↯ NF→¬R p₀′
uni⇒ (congrec₀ pₙ r₀)       (βredℕₛ eq′ pₙ′ p₀′ pₛ′)  = r₀ ↯ NF→¬R p₀′
uni⇒ (congrecₛ pₙ p₀ rₛ)    (congrecₙ rₙ′)            = rₙ′ ↯ NF→¬R pₙ
uni⇒ (congrecₛ pₙ p₀ rₛ)    (congrec₀ pₙ′ r₀′)        = r₀′ ↯ NF→¬R p₀
uni⇒ (congrecₛ pₙ p₀ rₛ)    (congrecₛ pₙ′ p₀′ rₛ′)    = _ & uniNF pₙ pₙ′ ⊗ uniNF p₀ p₀′
                                                           ⊗ uni⇒ rₛ rₛ′
uni⇒ (congrecₛ pₙ p₀ rₛ)    (βredℕₛ eq′ pₙ′ p₀′ pₛ′)  = rₛ ↯ NF→¬R pₛ′
uni⇒ (βred⊃ eq p₂)          (cong$₂ p₁′ r₂′)          = r₂′ ↯ NF→¬R p₂
uni⇒ (βred⊃ refl p₂)        (βred⊃ refl p₂′)          = βred⊃ refl & uniNF p₂ p₂′
uni⇒ (βredℕ₀ p₀ pₛ)         (congrec₀ pₙ′ r₀′)        = r₀′ ↯ NF→¬R p₀
uni⇒ (βredℕ₀ p₀ pₛ)         (βredℕ₀ p₀′ pₛ′)          = βredℕ₀ & uniNF p₀ p₀′ ⊗ uniNF pₛ pₛ′
uni⇒ (βredℕₛ eq pₙ p₀ pₛ)   (congrecₙ rₙ′)            = rₙ′ ↯ NF→¬R pₙ
uni⇒ (βredℕₛ eq pₙ p₀ pₛ)   (congrec₀ pₙ′ r₀′)        = r₀′ ↯ NF→¬R p₀
uni⇒ (βredℕₛ eq pₙ p₀ pₛ)   (congrecₛ pₙ′ p₀′ rₛ′)    = rₛ′ ↯ NF→¬R pₛ
uni⇒ (βredℕₛ refl pₙ p₀ pₛ) (βredℕₛ refl pₙ′ p₀′ pₛ′) = βredℕₛ refl & uniNF pₙ pₙ′ ⊗ uniNF p₀ p₀′
                                                           ⊗ uniNF pₛ pₛ′

open DetKit (kit redkit2 det⇒ uni⇒) public


----------------------------------------------------------------------------------------------------

prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
prog⇒ (var i)                            = done (nnf var-)
prog⇒ (⌜λ⌝ t)                            = done ⌜λ⌝-
prog⇒ (t₁ ⌜$⌝ t₂)                        with prog⇒ t₁ | prog⇒ t₂
... | step r₁       | _                     = step (cong$₁ r₁)
... | done p₁       | step r₂               = step (cong$₂ p₁ r₂)
... | done ⌜λ⌝-     | done p₂               = step (βred⊃ refl p₂)
... | done (nnf p₁) | done p₂               = done (nnf (p₁ ⌜$⌝ p₂))
prog⇒ ⌜zero⌝                             = done ⌜zero⌝
prog⇒ (⌜suc⌝ t)                          with prog⇒ t
... | step r                                = step (congsuc r)
... | done p                                = done (⌜suc⌝ p)
prog⇒ (⌜rec⌝ tₙ t₀ tₛ)                   with prog⇒ tₙ | prog⇒ t₀ | prog⇒ tₛ
... | step rₙ         | _       | _         = step (congrecₙ rₙ)
... | done pₙ         | step r₀ | _         = step (congrec₀ pₙ r₀)
... | done pₙ         | done p₀ | step rₛ   = step (congrecₛ pₙ p₀ rₛ)
... | done ⌜zero⌝     | done p₀ | done pₛ   = step (βredℕ₀ p₀ pₛ)
... | done (⌜suc⌝ pₙ) | done p₀ | done pₛ   = step (βredℕₛ refl (⌜suc⌝ pₙ) p₀ pₛ)
... | done (nnf pₙ)   | done p₀ | done pₛ   = done (nnf (⌜rec⌝ pₙ p₀ pₛ))

open ProgKit (kit redkit2 prog⇒) public


----------------------------------------------------------------------------------------------------

-- TODO
{-# DISPLAY TyKit.Ctx _ = Ctx #-}
{-# DISPLAY TmKitParams.Ty _ = Ty #-}
{-# DISPLAY RenSubKit3Params._⊆_ _ = _⊆_ #-}
{-# DISPLAY RenSubKit3Params._⊢_ _ = _⊢_ #-}
{-# DISPLAY RenSubKit3Params._[_] _ = _[_] #-}
{-# DISPLAY RenSubKit3Params.ren _ = ren #-}
{-# DISPLAY RenSubKit3Params.sub _ = sub #-}
{-# DISPLAY RenSubKit3Params.lift* _ = lift* #-}
{-# DISPLAY SubKit.get* _ = get* #-}
{-# DISPLAY RenSubKit1Params.get* _ = get* #-}
{-# DISPLAY RenSubKit1Params.id⊆ _ = id⊆ #-}
{-# DISPLAY RenKitParams._⊢*_ _ = _⊢*_ #-}

open ≡-Reasoning


----------------------------------------------------------------------------------------------------

-- stability under renaming
mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NF t → NF (ren e t)
  renNF e ⌜λ⌝-      = ⌜λ⌝-
  renNF e ⌜zero⌝    = ⌜zero⌝
  renNF e (⌜suc⌝ p) = ⌜suc⌝ (renNF e p)
  renNF e (nnf p)   = nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF t → NNF (ren e t)
  renNNF e var-             = var-
  renNNF e (p₁ ⌜$⌝ p₂)      = renNNF e p₁ ⌜$⌝ renNF e p₂
  renNNF e (⌜rec⌝ pₙ p₀ pₛ) = ⌜rec⌝ (renNNF e pₙ) (renNF e p₀) (renNF (lift⊆² e) pₛ)

sub∋NNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {i : Γ ∋ A} → NNF* ss → NNF (sub∋ ss i)
sub∋NNF {i = zero}  (p ∷ ps) = p
sub∋NNF {i = suc i} (p ∷ ps) = sub∋NNF ps

rensNNF : ∀ {Γ Γ′ Δ} {ss : Γ ⊢* Δ} (e : Γ ⊆ Γ′) → NNF* ss → NNF* (ren* e ss)
rensNNF e []       = []
rensNNF e (p ∷ ps) = renNNF e p ∷ rensNNF e ps

wksNNF : ∀ {B Γ Δ} {ss : Γ ⊢* Δ} → NNF* ss → NNF* (wk* {B} ss)
wksNNF ps = rensNNF (wk⊆ id⊆) ps

liftsNNF : ∀ {B Γ Δ} {ss : Γ ⊢* Δ} → NNF* ss → NNF* (lift* {B} ss)
liftsNNF ps = var- ∷ wksNNF ps

liftsNNF² : ∀ {B C Γ Δ} {ss : Γ ⊢* Δ} → NNF* ss → NNF* (lift*² {B} {C} ss)
liftsNNF² = liftsNNF ∘ liftsNNF

mutual
  subNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → NNF* ss → NF t → NF (sub ss t)
  subNF ps ⌜λ⌝-      = ⌜λ⌝-
  subNF ps ⌜zero⌝    = ⌜zero⌝
  subNF ps (⌜suc⌝ p) = ⌜suc⌝ (subNF ps p)
  subNF ps (nnf p)   = nnf (subNNF ps p)

  subNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → NNF* ss → NNF t → NNF (sub ss t)
  subNNF ps var-             = sub∋NNF ps
  subNNF ps (p₁ ⌜$⌝ p₂)      = subNNF ps p₁ ⌜$⌝ subNF ps p₂
  subNNF ps (⌜rec⌝ pₙ p₀ pₛ) = ⌜rec⌝ (subNNF ps pₙ) (subNF ps p₀) (subNF (liftsNNF² ps) pₛ)


----------------------------------------------------------------------------------------------------

ren⇒ : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (e : Γ ⊆ Γ′) → t ⇒ t′ → ren e t ⇒ ren e t′
ren⇒ e (cong$₁ r₁)               = cong$₁ (ren⇒ e r₁)
ren⇒ e (cong$₂ p₁ r₂)            = cong$₂ (renNF e p₁) (ren⇒ e r₂)
ren⇒ e (congsuc r)               = congsuc (ren⇒ e r)
ren⇒ e (congrecₙ rₙ)             = congrecₙ (ren⇒ e rₙ)
ren⇒ e (congrec₀ pₙ r₀)          = congrec₀ (renNF e pₙ) (ren⇒ e r₀)
ren⇒ e (congrecₛ pₙ p₀ rₛ)       = congrecₛ (renNF e pₙ) (renNF e p₀) (ren⇒ (lift⊆² e) rₛ)
ren⇒ e (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (rencut e t₁ _ ⁻¹) (renNF e p₂)
ren⇒ e (βredℕ₀ p₀ pₛ)            = βredℕ₀ (renNF e p₀) (renNF (lift⊆² e) pₛ)
ren⇒ e (βredℕₛ {tₙ = tₙ} {t₀} {tₛ} refl pₙ p₀ pₛ) =
    βredℕₛ eq (renNF e pₙ) (renNF e p₀) (renNF (lift⊆² e) pₛ)
  where
    eq =
      begin
        ren e (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ] [ tₙ ])
      ≡⟨ rencut e (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ]) tₙ ⁻¹ ⟩
        ren (lift⊆ e) (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ]) [ ren e tₙ ]
      ≡⟨ (_[ ren e tₙ ]) & (
          begin
            ren (lift⊆ e) (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ])
          ≡⟨ rencut (lift⊆ e) tₛ (wk (⌜rec⌝ tₙ t₀ tₛ)) ⁻¹ ⟩
            ren (lift⊆² e) tₛ [ ren (lift⊆ e) (wk (⌜rec⌝ tₙ t₀ tₛ)) ]
          ≡⟨ (ren (lift⊆² e) tₛ [_]) & (
              begin
                ren (lift⊆ e) (wk (⌜rec⌝ tₙ t₀ tₛ))
              ≡⟨ compren (lift⊆ e) (wk⊆ id⊆) (⌜rec⌝ tₙ t₀ tₛ) ⁻¹ ⟩
                ren (wk⊆ (e ∘⊆ id⊆)) (⌜rec⌝ tₙ t₀ tₛ)
              ≡⟨ (flip ren (⌜rec⌝ tₙ t₀ tₛ) ∘ wk⊆) & rid⊆ e ⟩
                ren (wk⊆ e) (⌜rec⌝ tₙ t₀ tₛ)
              ≡⟨⟩
                ⌜rec⌝ (ren (wk⊆ e) tₙ)
                      (ren (wk⊆ e) t₀)
                      (ren (lift⊆² (wk⊆ e)) tₛ)
              ≡⟨ ⌜rec⌝ & ( (flip ren tₙ ∘ wk⊆) & lid⊆ e ⁻¹
                         ⋮ compren (wk⊆ id⊆) e tₙ
                         )
                       ⊗ ( (flip ren t₀ ∘ wk⊆) & lid⊆ e ⁻¹
                         ⋮ compren (wk⊆ id⊆) e t₀
                         )
                       ⊗ ( (flip ren tₛ ∘ lift⊆² ∘ wk⊆) & lid⊆ e ⁻¹
                         ⋮ compren (lift⊆² (wk⊆ id⊆)) (lift⊆² e) tₛ
                         ) ⟩
                ⌜rec⌝ (wk (ren e tₙ))
                      (wk (ren e t₀))
                      (ren (lift⊆² (wk⊆ id⊆)) (ren (lift⊆² e) tₛ))
              ≡⟨⟩
                wk (⌜rec⌝ (ren e tₙ) (ren e t₀) (ren (lift⊆² e) tₛ))
              ∎) ⟩
            ren (lift⊆² e) tₛ [ wk (⌜rec⌝ (ren e tₙ) (ren e t₀) (ren (lift⊆² e) tₛ)) ]
          ∎) ⟩
        ren (lift⊆² e) tₛ
          [ wk (⌜rec⌝ (ren e tₙ) (ren e t₀) (ren (lift⊆² e) tₛ)) ]
          [ ren e tₙ ]
      ∎

-- TODO: !!!
postulate
  oops : ∀ {Γ Ξ 𝙓 𝙔 𝙕} (ss : Ξ ⊢* Γ) →
         ren* (wk⊆   {B = 𝙓} (lift⊆ {B = 𝙔} (lift⊆ {B = 𝙕} id⊆))) (ren* (wk⊆ {B = 𝙔} (lift⊆ {B = 𝙕} id⊆)) (wk* {B = 𝙕} ss)) ≡
         ren* (lift⊆ {B = 𝙓} (lift⊆ {B = 𝙔} (wk⊆   {B = 𝙕} id⊆))) (ren* (wk⊆ {B = 𝙓} (lift⊆ {B = 𝙔} id⊆)) (wk* {B = 𝙔} ss))

sub⇒ : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t t′ : Γ ⊢ A} → NNF* ss → t ⇒ t′ →
        sub ss t ⇒ sub ss t′
sub⇒ ps (cong$₁ r₁)               = cong$₁ (sub⇒ ps r₁)
sub⇒ ps (cong$₂ p₁ r₂)            = cong$₂ (subNF ps p₁) (sub⇒ ps r₂)
sub⇒ ps (congsuc r)               = congsuc (sub⇒ ps r)
sub⇒ ps (congrecₙ rₙ)             = congrecₙ (sub⇒ ps rₙ)
sub⇒ ps (congrec₀ pₙ r₀)          = congrec₀ (subNF ps pₙ) (sub⇒ ps r₀)
sub⇒ ps (congrecₛ pₙ p₀ rₛ)       = congrecₛ (subNF ps pₙ) (subNF ps p₀) (sub⇒ (liftsNNF² ps) rₛ)
sub⇒ ps (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (subcut _ t₁ _ ⁻¹) (subNF ps p₂)
sub⇒ ps (βredℕ₀ p₀ pₛ)            = βredℕ₀ (subNF ps p₀) (subNF (liftsNNF² ps) pₛ)
sub⇒ {ss = ss} ps (βredℕₛ {tₙ = tₙ} {t₀} {tₛ} refl pₙ p₀ pₛ) =
    βredℕₛ eq (subNF ps pₙ) (subNF ps p₀) (subNF (liftsNNF² ps) pₛ)
  where
    eq =
      begin
        sub ss (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ] [ tₙ ])
      ≡⟨ subcut ss (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ]) tₙ ⁻¹ ⟩
        sub (lift* ss) (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ]) [ sub ss tₙ ]
      ≡⟨ (_[ sub ss tₙ ]) & (
          begin
            sub (lift* ss) (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ])
          ≡⟨ subcut (lift* ss) tₛ (wk (⌜rec⌝ tₙ t₀ tₛ)) ⁻¹ ⟩
            sub (lift*² ss) tₛ [ sub (lift* ss) (wk (⌜rec⌝ tₙ t₀ tₛ)) ]
          ≡⟨ (sub (lift*² ss) tₛ [_]) & (
              begin
                sub (lift* ss) (wk (⌜rec⌝ tₙ t₀ tₛ))
              ≡⟨ eqsubren (lift* ss) (wk⊆ id⊆) (⌜rec⌝ tₙ t₀ tₛ) ⁻¹ ⟩
                sub (get* (wk⊆ id⊆) (lift* ss)) (⌜rec⌝ tₙ t₀ tₛ)
              ≡⟨⟩
                sub (get* id⊆ (wk* ss)) (⌜rec⌝ tₙ t₀ tₛ)
              ≡⟨ flip sub (⌜rec⌝ tₙ t₀ tₛ) & lidget* (wk* ss) ⟩
                sub (wk* ss) (⌜rec⌝ tₙ t₀ tₛ)
              ≡⟨⟩
                ⌜rec⌝ (sub (wk* ss) tₙ)
                      (sub (wk* ss) t₀)
                      (sub (lift*² (wk* ss)) tₛ)
              ≡⟨ ⌜rec⌝ & eqrensub (wk⊆ id⊆) ss tₙ
                       ⊗ eqrensub (wk⊆ id⊆) ss t₀
                       ⊗ (
                           begin
                             sub (lift*² (wk* ss)) tₛ
                           ≡⟨ flip sub tₛ & (
                               begin
                                 lift*² (wk* ss)
                               ≡⟨⟩
                                 var zero ∷
                                   (var (suc zero) ∷
                                     ren* (wk⊆ (lift⊆² id⊆))
                                       (ren* (wk⊆ (lift⊆ id⊆)) (ren* (wk⊆ id⊆) ss)))
                               ≡⟨ (var zero ∷_) & ((var (suc zero) ∷_) & oops ss) ⟩
                                 var zero ∷
                                   (var (suc zero) ∷
                                     ren* (lift⊆² (wk⊆ id⊆))
                                       (ren* (wk⊆ (lift⊆ id⊆)) (ren* (wk⊆ id⊆) ss)))
                               ≡⟨⟩
                                 ren* (lift⊆² (wk⊆ id⊆)) (lift*² ss)
                               ∎) ⟩
                             sub (ren* (lift⊆² (wk⊆ id⊆)) (lift*² ss)) tₛ
                           ≡⟨ eqrensub (lift⊆² (wk⊆ id⊆)) (lift*² ss) tₛ ⟩
                             ren (lift⊆² (wk⊆ id⊆)) (sub (lift*² ss) tₛ)
                           ∎) ⟩
                ⌜rec⌝ (wk (sub ss tₙ))
                      (wk (sub ss t₀))
                      (ren (lift⊆² (wk⊆ id⊆)) (sub (lift*² ss) tₛ))
              ≡⟨⟩
                wk (⌜rec⌝ (sub ss tₙ) (sub ss t₀) (sub (lift*² ss) tₛ))
              ∎) ⟩
            sub (lift* (lift* ss)) tₛ
              [ wk (⌜rec⌝ (sub ss tₙ) (sub ss t₀) (sub (lift*² ss) tₛ)) ]
          ∎) ⟩
        sub (lift* (lift* ss)) tₛ
          [ wk (⌜rec⌝ (sub ss tₙ) (sub ss t₀) (sub (lift*² ss) tₛ)) ]
          [ sub ss tₙ ]
      ∎


-- TODO
-- sub⇒ : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t t′ : Γ ⊢ A} → NNF* ss → t ⇒ t′ →
--         sub ss t ⇒ sub ss t′
-- sub⇒ ps (cong$₁ r₁)               = cong$₁ (sub⇒ ps r₁)
-- sub⇒ ps (cong$₂ p₁ r₂)            = cong$₂ (subNF ps p₁) (sub⇒ ps r₂)
-- sub⇒ ps (congsuc r)               = congsuc (sub⇒ ps r)
-- sub⇒ ps (congrecₙ rₙ)             = congrecₙ (sub⇒ ps rₙ)
-- sub⇒ ps (congrec₀ pₙ r₀)          = congrec₀ (subNF ps pₙ) (sub⇒ ps r₀)
-- sub⇒ ps (congrecₛ pₙ p₀ rₛ)       = congrecₛ (subNF ps pₙ) (subNF ps p₀)
--                                        (sub⇒ (liftsNNF (liftsNNF ps)) rₛ)
-- sub⇒ ps (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (subcut _ t₁ _ ⁻¹) (subNF ps p₂)
-- sub⇒ ps (βredℕ₀ p₀ pₛ)            = βredℕ₀ (subNF ps p₀) (subNF (liftsNNF (liftsNNF ps)) pₛ)
-- sub⇒ {ss = ss} ps (βredℕₛ {tₙ = tₙ} {t₀} {tₛ} refl pₙ p₀ pₛ) =
--     βredℕₛ eq (subNF ps pₙ) (subNF ps p₀) (subNF (liftsNNF (liftsNNF ps)) pₛ)
--   where
--     eq =
--       begin
--         sub ss (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ] [ tₙ ])
--       ≡⟨ subcut ss (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ]) tₙ ⁻¹ ⟩
--         sub (lifts ss) (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ]) [ sub ss tₙ ]
--       ≡⟨ (_[ sub ss tₙ ]) & (
--           begin
--             sub (lifts ss) (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ])
--           ≡⟨ subcut (lifts ss) tₛ (wk (⌜rec⌝ tₙ t₀ tₛ)) ⁻¹ ⟩
--             sub (lifts (lifts ss)) tₛ [ sub (lifts ss) (wk (⌜rec⌝ tₙ t₀ tₛ)) ]
--           ≡⟨ (sub (lifts (lifts ss)) tₛ [_]) & (
--               begin
--                 sub (lifts ss) (wk (⌜rec⌝ tₙ t₀ tₛ))
--               ≡⟨⟩
--                 ⌜rec⌝ (sub (lifts ss) (wk tₙ))
--                       (sub (lifts ss) (wk t₀))
--                       (sub (lifts (lifts (lifts ss))) (ren (lift⊆ (lift⊆ (wk⊆ id⊆))) tₛ))
--               ≡⟨ ⌜rec⌝ & ( eqsubren (lifts ss) (wk⊆ id⊆) tₙ ⁻¹
--                          ⋮ flip sub tₙ & lidget* (wk* ss)
--                          ⋮ eqrensub (wk⊆ id⊆) ss tₙ
--                          )
--                        ⊗ ( eqsubren (lifts ss) (wk⊆ id⊆) t₀ ⁻¹
--                          ⋮ flip sub t₀ & lidget* (wk* ss)
--                          ⋮ eqrensub (wk⊆ id⊆) ss t₀
--                          )
--                        ⊗ (
--                            begin
--                              sub (lifts (lifts (lifts ss))) (ren (lift⊆ (lift⊆ (wk⊆ id⊆))) tₛ)
--                            ≡⟨ eqsubren (lifts (lifts (lifts ss))) (lift⊆ (lift⊆ (wk⊆ id⊆))) tₛ ⁻¹ ⟩
--                              sub (get* (lift⊆ (lift⊆ (wk⊆ id⊆))) (lifts (lifts (lifts ss)))) tₛ
--                            ≡⟨⟩
--                              sub (var zero ∷ (var (suc zero) ∷
--                                get* id⊆ (ren* (wk⊆ (lift⊆ (lift⊆ id⊆))) (ren* (wk⊆ (lift⊆ id⊆)) (wk* ss)))))
--                                tₛ
--                            ≡⟨ (flip sub tₛ ∘ (var zero ∷_)) & ((var (suc zero) ∷_) & (
--                                begin
--                                  get* id⊆ (ren* (wk⊆ (lift⊆ (lift⊆ id⊆))) (ren* (wk⊆ (lift⊆ id⊆)) (wk* ss)))
--                                ≡⟨ lidget* (ren* (wk⊆ (lift⊆ (lift⊆ id⊆))) (ren* (wk⊆ (lift⊆ id⊆)) (wk* ss))) ⟩
--                                  ren* (wk⊆ (lift⊆ (lift⊆ id⊆))) (ren* (wk⊆ (lift⊆ id⊆)) (wk* ss))
--                                ≡⟨ {!!} ⟩
--                                  ren* (lift⊆ (lift⊆ (wk⊆ id⊆))) (ren* (wk⊆ (lift⊆ id⊆)) (wk* ss))
--                                ∎)) ⟩
--                              sub (var zero ∷ (var (suc zero) ∷
--                                ren* (lift⊆ (lift⊆ (wk⊆ id⊆))) (ren* (wk⊆ (lift⊆ id⊆)) (wk* ss))))
--                                tₛ
--                            ≡⟨⟩
--                              sub (ren* (lift⊆ (lift⊆ (wk⊆ id⊆))) (lifts (lifts ss))) tₛ
--                            ≡⟨ eqrensub (lift⊆ (lift⊆ (wk⊆ id⊆))) (lifts (lifts ss)) tₛ ⟩
--                              ren (lift⊆ (lift⊆ (wk⊆ id⊆))) (sub (lifts (lifts ss)) tₛ)
--                            ∎
--                        ) ⟩
--                 ⌜rec⌝ (wk (sub ss tₙ))
--                       (wk (sub ss t₀))
--                       (ren (lift⊆ (lift⊆ (wk⊆ id⊆))) (sub (lifts (lifts ss)) tₛ))
--               ≡⟨⟩
--                 wk (⌜rec⌝ (sub ss tₙ) (sub ss t₀) (sub (lifts (lifts ss)) tₛ))
--               ∎) ⟩
--             sub (lifts (lifts ss)) tₛ
--               [ wk (⌜rec⌝ (sub ss tₙ) (sub ss t₀) (sub (lifts (lifts ss)) tₛ)) ]
--           ∎) ⟩
--         sub (lifts (lifts ss)) tₛ
--           [ wk (⌜rec⌝ (sub ss tₙ) (sub ss t₀) (sub (lifts (lifts ss)) tₛ)) ]
--           [ sub ss tₙ ]
--       ∎


-- ----------------------------------------------------------------------------------------------------
