----------------------------------------------------------------------------------------------------

-- call-by-value reduction to β-short semi-weak normal form

module STLC-Naturals-SWNF-CBV where

open import STLC-Naturals-RenSub public
open import STLC-Naturals-SWNF public
open import Kit3 public


----------------------------------------------------------------------------------------------------

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
  NF→¬R (nnf p)   r           = r ↯ NNF→¬R p

  NNF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NNF t → ¬R t
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

ren⇒ : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (e : Γ ⊆ Γ′) → t ⇒ t′ → ren e t ⇒ ren e t′
ren⇒ e (cong$₁ r₁)               = cong$₁ (ren⇒ e r₁)
ren⇒ e (cong$₂ p₁ r₂)            = cong$₂ (renNF e p₁) (ren⇒ e r₂)
ren⇒ e (congsuc r)               = congsuc (ren⇒ e r)
ren⇒ e (congrecₙ rₙ)             = congrecₙ (ren⇒ e rₙ)
ren⇒ e (congrec₀ pₙ r₀)          = congrec₀ (renNF e pₙ) (ren⇒ e r₀)
ren⇒ e (congrecₛ pₙ p₀ rₛ)       = congrecₛ (renNF e pₙ) (renNF e p₀)
                                      (ren⇒ (lift⊆ (lift⊆ e)) rₛ)
ren⇒ e (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (rencut e t₁ _ ⁻¹) (renNF e p₂)
ren⇒ e (βredℕ₀ p₀ pₛ)            = βredℕ₀ (renNF e p₀) (renNF (lift⊆ (lift⊆ e)) pₛ)
ren⇒ e (βredℕₛ {tₙ = tₙ} {t₀} {tₛ} refl pₙ p₀ pₛ) =
    βredℕₛ eq (renNF e pₙ) (renNF e p₀) (renNF (lift⊆ (lift⊆ e)) pₛ)
      where
  eq : ren e (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ] [ tₙ ]) ≡
       ren (lift⊆ (lift⊆ e)) tₛ
         [ wk (⌜rec⌝ (ren e tₙ) (ren e t₀) (ren (lift⊆ (lift⊆ e)) tₛ)) ] [ ren e tₙ ]
  eq = rencut e (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ]) tₙ ⁻¹
     ⋮ (_[ ren e tₙ ]) &
         ( rencut (lift⊆ e) tₛ (wk (⌜rec⌝ tₙ t₀ tₛ)) ⁻¹
         ⋮ (ren (lift⊆ (lift⊆ e)) tₛ [_]) &
             ( compren (lift⊆ e) (wk⊆ id⊆) (⌜rec⌝ tₙ t₀ tₛ) ⁻¹
             ⋮ (flip ren (⌜rec⌝ tₙ t₀ tₛ) ∘ wk⊆) & (rid⊆ e ⋮ lid⊆ e ⁻¹)
             ⋮ ⌜rec⌝ & compren (wk⊆ id⊆) e tₙ
                     ⊗ compren (wk⊆ id⊆) e t₀
                     ⊗ compren (lift⊆ (lift⊆ (wk⊆ id⊆))) (lift⊆ (lift⊆ e)) tₛ
             )
         )

sub⇒ : ∀ {Γ Ξ A} {ss : Ξ ⊢§ Γ} {t t′ : Γ ⊢ A} → NNF§ ss → t ⇒ t′ → sub ss t ⇒ sub ss t′
sub⇒ ps (cong$₁ r₁)               = cong$₁ (sub⇒ ps r₁)
sub⇒ ps (cong$₂ p₁ r₂)            = cong$₂ (subNF ps p₁) (sub⇒ ps r₂)
sub⇒ ps (congsuc r)               = congsuc (sub⇒ ps r)
sub⇒ ps (congrecₙ rₙ)             = congrecₙ (sub⇒ ps rₙ)
sub⇒ ps (congrec₀ pₙ r₀)          = congrec₀ (subNF ps pₙ) (sub⇒ ps r₀)
sub⇒ ps (congrecₛ pₙ p₀ rₛ)       = congrecₛ (subNF ps pₙ) (subNF ps p₀)
                                       (sub⇒ (liftNNF§ (liftNNF§ ps)) rₛ)
sub⇒ ps (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (subcut _ t₁ _ ⁻¹) (subNF ps p₂)
sub⇒ ps (βredℕ₀ p₀ pₛ)            = βredℕ₀ (subNF ps p₀) (subNF (liftNNF§ (liftNNF§ ps)) pₛ)
sub⇒ {ss = ss} ps (βredℕₛ {tₙ = tₙ} {t₀} {tₛ} refl pₙ p₀ pₛ) =
    βredℕₛ eq (subNF ps pₙ) (subNF ps p₀) (subNF (liftNNF§ (liftNNF§ ps)) pₛ)
      where
  eq : sub ss (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ] [ tₙ ]) ≡
       sub (lift§ (lift§ ss)) tₛ
         [ wk (⌜rec⌝ (sub ss tₙ) (sub ss t₀) (sub (lift§ (lift§ ss)) tₛ)) ] [ sub ss tₙ ]
  eq = subcut ss (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ]) tₙ ⁻¹
     ⋮ (_[ sub ss tₙ ]) &
         ( subcut (lift§ ss) tₛ (wk (⌜rec⌝ tₙ t₀ tₛ)) ⁻¹
         ⋮ (sub (lift§ (lift§ ss)) tₛ [_]) &
             ( eqsubren (lift§ ss) (wk⊆ id⊆) (⌜rec⌝ tₙ t₀ tₛ) ⁻¹
             ⋮ flip sub (⌜rec⌝ tₙ t₀ tₛ) & lidget§ (wk§ ss)
             ⋮ ⌜rec⌝ & eqrensub (wk⊆ id⊆) ss tₙ
                     ⊗ eqrensub (wk⊆ id⊆) ss t₀
                     ⊗ ( ((flip sub tₛ ∘ (var zero ∷_)) ∘ (var (suc zero) ∷_)) & -- TODO: should _∘_ be infixl?
                             ( wk§ & eqwkren§ (wk⊆ id⊆) ss ⁻¹
                             ⋮ eqwkren§ (lift⊆ (wk⊆ id⊆)) (wk§ ss) ⁻¹
                             )
                       ⋮ eqrensub (lift⊆ (lift⊆ (wk⊆ id⊆))) (lift§ (lift§ ss)) tₛ
                       )
             )
        )


----------------------------------------------------------------------------------------------------
