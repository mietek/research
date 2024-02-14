----------------------------------------------------------------------------------------------------

-- applicative order reduction to β-short normal form

module STLC-Base-NF-AO where

open import STLC-Base-RenSub public
open import STLC-Base-NF public
open import Kit3 public


----------------------------------------------------------------------------------------------------

infix 4 _⇒_
data _⇒_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  congλ  : ∀ {A B} {t t′ : A ∷ Γ ⊢ B} (r : t ⇒ t′) → ⌜λ⌝ t ⇒ ⌜λ⌝ t′
  cong$₁ : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r₁ : t₁ ⇒ t₁′) →
           t₁ ⌜$⌝ t₂ ⇒ t₁′ ⌜$⌝ t₂
  cong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : NF t₁) (r₂ : t₂ ⇒ t₂′) →
           t₁ ⌜$⌝ t₂ ⇒ t₁ ⌜$⌝ t₂′
  βred⊃  : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) (p₁ : NF t₁)
             (p₂ : NF t₂) →
           ⌜λ⌝ t₁ ⌜$⌝ t₂ ⇒ t′

open RedKit1 (kit tmkit _⇒_) public

mutual
  NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t
  NF→¬R (⌜λ⌝ p) (congλ r) = r ↯ NF→¬R p
  NF→¬R (nnf p) r         = r ↯ NNF→¬R p

  NNF→¬R : ∀ {Γ A} {t  : Γ ⊢ A} → NNF t → ¬R t
  NNF→¬R (p₁ ⌜$⌝ p₂) (cong$₁ r₁)     = r₁ ↯ NNF→¬R p₁
  NNF→¬R (p₁ ⌜$⌝ p₂) (cong$₂ p₁′ r₂) = r₂ ↯ NF→¬R p₂

open RedKit2 (kit redkit1 uniNF NF→¬R) public


----------------------------------------------------------------------------------------------------

det⇒ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒ t″ → t′ ≡ t″
det⇒ (congλ r)          (congλ r′)           = ⌜λ⌝ & det⇒ r r′
det⇒ (cong$₁ r₁)        (cong$₁ r₁′)         = (_⌜$⌝ _) & det⇒ r₁ r₁′
det⇒ (cong$₁ r₁)        (cong$₂ p₁′ r₂′)     = r₁ ↯ NF→¬R p₁′
det⇒ (cong$₁ r₁)        (βred⊃ refl p₁′ p₂′) = r₁ ↯ NF→¬R (⌜λ⌝ p₁′)
det⇒ (cong$₂ p₁ r₂)     (cong$₁ r₁′)         = r₁′ ↯ NF→¬R p₁
det⇒ (cong$₂ p₁ r₂)     (cong$₂ p₁′ r₂′)     = (_ ⌜$⌝_) & det⇒ r₂ r₂′
det⇒ (cong$₂ p₁ r₂)     (βred⊃ refl p₁′ p₂′) = r₂ ↯ NF→¬R p₂′
det⇒ (βred⊃ refl p₁ p₂) (cong$₁ r₁′)         = r₁′ ↯ NF→¬R (⌜λ⌝ p₁)
det⇒ (βred⊃ refl p₁ p₂) (cong$₂ p₁′ r₂′)     = r₂′ ↯ NF→¬R p₂
det⇒ (βred⊃ refl p₁ p₂) (βred⊃ refl p₁′ p₂′) = refl

uni⇒ : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒ t′) → r ≡ r′
uni⇒ (congλ r)          (congλ r′)           = congλ & uni⇒ r r′
uni⇒ (cong$₁ r₁)        (cong$₁ r₁′)         = cong$₁ & uni⇒ r₁ r₁′
uni⇒ (cong$₁ r₁)        (cong$₂ p₁′ r₂′)     = r₁ ↯ NF→¬R p₁′
uni⇒ (cong$₁ r₁)        (βred⊃ eq p₁′ p₂′)   = r₁ ↯ NF→¬R (⌜λ⌝ p₁′)
uni⇒ (cong$₂ p₁ r₂)     (cong$₁ r₁′)         = r₁′ ↯ NF→¬R p₁
uni⇒ (cong$₂ p₁ r₂)     (cong$₂ p₁′ r₂′)     = cong$₂ & uniNF p₁ p₁′ ⊗ uni⇒ r₂ r₂′
uni⇒ (cong$₂ p₁ r₂)     (βred⊃ eq′ p₁′ p₂′)  = r₂ ↯ NF→¬R p₂′
uni⇒ (βred⊃ eq p₁ p₂)   (cong$₁ r₁′)         = r₁′ ↯ NF→¬R (⌜λ⌝ p₁)
uni⇒ (βred⊃ eq p₁ p₂)   (cong$₂ p₁′ r₂′)     = r₂′ ↯ NF→¬R p₂
uni⇒ (βred⊃ refl p₁ p₂) (βred⊃ refl p₁′ p₂′) = βred⊃ refl & uniNF p₁ p₁′ ⊗ uniNF p₂ p₂′

open DetKit (kit redkit2 det⇒ uni⇒) public


----------------------------------------------------------------------------------------------------

prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
prog⇒ (var i)                = done (nnf var-)
prog⇒ (⌜λ⌝ t)                with prog⇒ t
... | step r                    = step (congλ r)
... | done p                    = done (⌜λ⌝ p)
prog⇒ (t₁ ⌜$⌝ t₂)            with prog⇒ t₁ | prog⇒ t₂
... | step r₁       | _         = step (cong$₁ r₁)
... | done p₁       | step r₂   = step (cong$₂ p₁ r₂)
... | done (⌜λ⌝ p₁) | done p₂   = step (βred⊃ refl p₁ p₂)
... | done (nnf p₁) | done p₂   = done (nnf (p₁ ⌜$⌝ p₂))

open ProgKit (kit redkit2 prog⇒) public


----------------------------------------------------------------------------------------------------

ren⇒ : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (e : Γ ⊑ Γ′) → t ⇒ t′ → ren e t ⇒ ren e t′
ren⇒ e (congλ r)                    = congλ (ren⇒ (lift⊑ e) r)
ren⇒ e (cong$₁ r₁)                  = cong$₁ (ren⇒ e r₁)
ren⇒ e (cong$₂ p₁ r₂)               = cong$₂ (renNF e p₁) (ren⇒ e r₂)
ren⇒ e (βred⊃ {t₁ = t₁} refl p₁ p₂) = βred⊃ (rencut e t₁ _ ⁻¹) (renNF (lift⊑ e) p₁) (renNF e p₂)

sub⇒ : ∀ {Γ Ξ A} {ss : Ξ ⊢§ Γ} {t t′ : Γ ⊢ A} → NNF§ ss → t ⇒ t′ → sub ss t ⇒ sub ss t′
sub⇒ ps (congλ r)                    = congλ (sub⇒ (liftNNF§ ps) r)
sub⇒ ps (cong$₁ r₁)                  = cong$₁ (sub⇒ ps r₁)
sub⇒ ps (cong$₂ p₁ r₂)               = cong$₂ (subNF ps p₁) (sub⇒ ps r₂)
sub⇒ ps (βred⊃ {t₁ = t₁} refl p₁ p₂) = βred⊃ (subcut _ t₁ _ ⁻¹) (subNF (liftNNF§ ps) p₁)
                                          (subNF ps p₂)


----------------------------------------------------------------------------------------------------
