----------------------------------------------------------------------------------------------------

-- call-by-value reduction to β-short weak normal form

module STLC-Naturals-WNF-CBV where

open import STLC-Naturals-RenSub public
open import STLC-Naturals-WNF public
open import Kit3 public


----------------------------------------------------------------------------------------------------

infix 4 _⇒_
data _⇒_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  cong$₁   : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r₁ : t₁ ⇒ t₁′) →
             t₁ ⌜$⌝ t₂ ⇒ t₁′ ⌜$⌝ t₂
  cong$₂   : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : NF t₁) (r₂ : t₂ ⇒ t₂′) →
             t₁ ⌜$⌝ t₂ ⇒ t₁ ⌜$⌝ t₂′
  congrecₙ : ∀ {A} {tₙ tₙ′ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ : (Γ , ⌜ℕ⌝) , A ⊢ A} (rₙ : tₙ ⇒ tₙ′) →
             ⌜rec⌝ tₙ t₀ tₛ ⇒ ⌜rec⌝ tₙ′ t₀ tₛ
  congrec₀ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ t₀′ : Γ ⊢ A} {tₛ : (Γ , ⌜ℕ⌝) , A ⊢ A} (pₙ : NF tₙ)
               (r₀ : t₀ ⇒ t₀′) →
             ⌜rec⌝ tₙ t₀ tₛ ⇒ ⌜rec⌝ tₙ t₀′ tₛ
  congrecₛ : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ tₛ′ : (Γ , ⌜ℕ⌝) , A ⊢ A} (pₙ : NF tₙ)
               (p₀ : NF t₀) (rₛ : tₛ ⇒ tₛ′) →
             ⌜rec⌝ tₙ t₀ tₛ ⇒ ⌜rec⌝ tₙ t₀ tₛ′
  βred⊃    : ∀ {A B} {t₁ : Γ , A ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) (p₂ : NF t₂) →
             ⌜λ⌝ t₁ ⌜$⌝ t₂ ⇒ t′
  βredℕ₀   : ∀ {A} {t₀ : Γ ⊢ A} {tₛ : (Γ , ⌜ℕ⌝) , A ⊢ A} (p₀ : NF t₀) (pₛ : NF tₛ) →
             ⌜rec⌝ ⌜zero⌝ t₀ tₛ ⇒ t₀
  βredℕₛ   : ∀ {A} {tₙ : Γ ⊢ ⌜ℕ⌝} {t₀ : Γ ⊢ A} {tₛ : (Γ , ⌜ℕ⌝) , A ⊢ A} {t′}
               (eq : t′ ≡ tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ] [ tₙ ]) → (pₙ : NF (⌜suc⌝ tₙ)) (p₀ : NF t₀)
               (pₛ : NF tₛ) →
             ⌜rec⌝ (⌜suc⌝ tₙ) t₀ tₛ ⇒ t′

open RedKit1 (kit tmkit _⇒_) public

mutual
  NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t
  NF→¬R (nnf p) r = r ↯ NNF→¬R p

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
prog⇒ (⌜suc⌝ t)                          = done ⌜suc⌝-
prog⇒ (⌜rec⌝ tₙ t₀ tₛ)                   with prog⇒ tₙ | prog⇒ t₀ | prog⇒ tₛ
... | step rₙ         | _       | _         = step (congrecₙ rₙ)
... | done pₙ         | step r₀ | _         = step (congrec₀ pₙ r₀)
... | done pₙ         | done p₀ | step rₛ   = step (congrecₛ pₙ p₀ rₛ)
... | done ⌜zero⌝     | done p₀ | done pₛ   = step (βredℕ₀ p₀ pₛ)
... | done ⌜suc⌝-     | done p₀ | done pₛ   = step (βredℕₛ refl ⌜suc⌝- p₀ pₛ)
... | done (nnf pₙ)   | done p₀ | done pₛ   = done (nnf (⌜rec⌝ pₙ p₀ pₛ))

open ProgKit (kit redkit2 prog⇒) public


----------------------------------------------------------------------------------------------------

ren⇒ : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → t ⇒ t′ → ren ϱ t ⇒ ren ϱ t′
ren⇒ ϱ (cong$₁ r₁)               = cong$₁ (ren⇒ ϱ r₁)
ren⇒ ϱ (cong$₂ p₁ r₂)            = cong$₂ (renNF ϱ p₁) (ren⇒ ϱ r₂)
ren⇒ ϱ (congrecₙ rₙ)             = congrecₙ (ren⇒ ϱ rₙ)
ren⇒ ϱ (congrec₀ pₙ r₀)          = congrec₀ (renNF ϱ pₙ) (ren⇒ ϱ r₀)
ren⇒ ϱ (congrecₛ pₙ p₀ rₛ)       = congrecₛ (renNF ϱ pₙ) (renNF ϱ p₀)
                                      (ren⇒ (lift⊑ (lift⊑ ϱ)) rₛ)
ren⇒ ϱ (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (rencut ϱ t₁ _ ⁻¹) (renNF ϱ p₂)
ren⇒ ϱ (βredℕ₀ p₀ pₛ)            = βredℕ₀ (renNF ϱ p₀) (renNF (lift⊑ (lift⊑ ϱ)) pₛ)
ren⇒ ϱ (βredℕₛ {tₙ = tₙ} {t₀} {tₛ} refl pₙ p₀ pₛ) =
    βredℕₛ eq (renNF ϱ pₙ) (renNF ϱ p₀) (renNF (lift⊑ (lift⊑ ϱ)) pₛ)
      where
  eq : ren ϱ (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ] [ tₙ ]) ≡
       ren (lift⊑ (lift⊑ ϱ)) tₛ
         [ wk (⌜rec⌝ (ren ϱ tₙ) (ren ϱ t₀) (ren (lift⊑ (lift⊑ ϱ)) tₛ)) ] [ ren ϱ tₙ ]
  eq = rencut ϱ (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ]) tₙ ⁻¹
     ⋮ (_[ ren ϱ tₙ ]) &
         ( rencut (lift⊑ ϱ) tₛ (wk (⌜rec⌝ tₙ t₀ tₛ)) ⁻¹
         ⋮ (ren (lift⊑ (lift⊑ ϱ)) tₛ [_]) &
             ( compren (lift⊑ ϱ) (wk⊑ id⊑) (⌜rec⌝ tₙ t₀ tₛ) ⁻¹
             ⋮ (flip ren (⌜rec⌝ tₙ t₀ tₛ) ∘ wk⊑) & (rid⊑ ϱ ⋮ lid⊑ ϱ ⁻¹)
             ⋮ ⌜rec⌝ & compren (wk⊑ id⊑) ϱ tₙ
                     ⊗ compren (wk⊑ id⊑) ϱ t₀
                     ⊗ compren (lift⊑ (lift⊑ (wk⊑ id⊑))) (lift⊑ (lift⊑ ϱ)) tₛ
             )
         )

sub⇒ : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t t′ : Γ ⊢ A} → NNF§ σ → t ⇒ t′ → sub σ t ⇒ sub σ t′
sub⇒ ψ (cong$₁ r₁)               = cong$₁ (sub⇒ ψ r₁)
sub⇒ ψ (cong$₂ p₁ r₂)            = cong$₂ (subNF ψ p₁) (sub⇒ ψ r₂)
sub⇒ ψ (congrecₙ rₙ)             = congrecₙ (sub⇒ ψ rₙ)
sub⇒ ψ (congrec₀ pₙ r₀)          = congrec₀ (subNF ψ pₙ) (sub⇒ ψ r₀)
sub⇒ ψ (congrecₛ pₙ p₀ rₛ)       = congrecₛ (subNF ψ pₙ) (subNF ψ p₀)
                                      (sub⇒ (liftNNF§ (liftNNF§ ψ)) rₛ)
sub⇒ ψ (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (subcut _ t₁ _ ⁻¹) (subNF ψ p₂)
sub⇒ ψ (βredℕ₀ p₀ pₛ)            = βredℕ₀ (subNF ψ p₀) (subNF (liftNNF§ (liftNNF§ ψ)) pₛ)
sub⇒ {σ = σ} ψ (βredℕₛ {tₙ = tₙ} {t₀} {tₛ} refl pₙ p₀ pₛ) =
    βredℕₛ eq (subNF ψ pₙ) (subNF ψ p₀) (subNF (liftNNF§ (liftNNF§ ψ)) pₛ)
      where
  eq : sub σ (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ] [ tₙ ]) ≡
       sub (lift§ (lift§ σ)) tₛ
         [ wk (⌜rec⌝ (sub σ tₙ) (sub σ t₀) (sub (lift§ (lift§ σ)) tₛ)) ] [ sub σ tₙ ]
  eq = subcut σ (tₛ [ wk (⌜rec⌝ tₙ t₀ tₛ) ]) tₙ ⁻¹
     ⋮ (_[ sub σ tₙ ]) &
         ( subcut (lift§ σ) tₛ (wk (⌜rec⌝ tₙ t₀ tₛ)) ⁻¹
         ⋮ (sub (lift§ (lift§ σ)) tₛ [_]) &
             ( eqsubren (lift§ σ) (wk⊑ id⊑) (⌜rec⌝ tₙ t₀ tₛ) ⁻¹
             ⋮ flip sub (⌜rec⌝ tₙ t₀ tₛ) & lidget§ (wk§ σ)
             ⋮ ⌜rec⌝ & eqrensub (wk⊑ id⊑) σ tₙ
                     ⊗ eqrensub (wk⊑ id⊑) σ t₀
                     ⊗ ( ((flip sub tₛ ∘ (_, var zero)) ∘ (_, var (wk∋ zero))) & -- TODO: should _∘_ be infixl?
                             ( wk§ & eqwkren§ (wk⊑ id⊑) σ ⁻¹
                             ⋮ eqwkren§ (lift⊑ (wk⊑ id⊑)) (wk§ σ) ⁻¹
                             )
                       ⋮ eqrensub (lift⊑ (lift⊑ (wk⊑ id⊑))) (lift§ (lift§ σ)) tₛ
                       )
             )
        )


----------------------------------------------------------------------------------------------------
