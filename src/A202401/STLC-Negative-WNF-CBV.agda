----------------------------------------------------------------------------------------------------

-- call-by-value reduction to β-short weak normal form

module A202401.STLC-Negative-WNF-CBV where

open import A202401.STLC-Negative-RenSub public
open import A202401.STLC-Negative-WNF public
open import A202401.Kit3 public


----------------------------------------------------------------------------------------------------

infix 4 _⇒_
data _⇒_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  cong$₁  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r₁ : t₁ ⇒ t₁′) →
            t₁ ⌜$⌝ t₂ ⇒ t₁′ ⌜$⌝ t₂
  cong$₂  : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : NF t₁) (r₂ : t₂ ⇒ t₂′) →
            t₁ ⌜$⌝ t₂ ⇒ t₁ ⌜$⌝ t₂′
  congfst : ∀ {A B} {t t′ : Γ ⊢ A ⌜∧⌝ B} (r : t ⇒ t′) → ⌜fst⌝ t ⇒ ⌜fst⌝ t′
  congsnd : ∀ {A B} {t t′ : Γ ⊢ A ⌜∧⌝ B} (r : t ⇒ t′) → ⌜snd⌝ t ⇒ ⌜snd⌝ t′
  βred⊃   : ∀ {A B} {t₁ : Γ , A ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) (p₂ : NF t₂) →
            ⌜λ⌝ t₁ ⌜$⌝ t₂ ⇒ t′
  βred∧₁  : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → ⌜fst⌝ (t₁ ⌜,⌝ t₂) ⇒ t₁
  βred∧₂  : ∀ {A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → ⌜snd⌝ (t₁ ⌜,⌝ t₂) ⇒ t₂

open RedKit1 (kit tmkit _⇒_) public

mutual
  NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t
  NF→¬R (nnf p) r = r ↯ NNF→¬R p

  NNF→¬R : ∀ {Γ A} {t  : Γ ⊢ A} → NNF t → ¬R t
  NNF→¬R (p₁ ⌜$⌝ p₂) (cong$₁ r₁)     = r₁ ↯ NNF→¬R p₁
  NNF→¬R (p₁ ⌜$⌝ p₂) (cong$₂ p₁′ r₂) = r₂ ↯ NF→¬R p₂
  NNF→¬R (⌜fst⌝ p)   (congfst r)     = r ↯ NNF→¬R p
  NNF→¬R (⌜snd⌝ p)   (congsnd r)     = r ↯ NNF→¬R p

open RedKit2 (kit redkit1 uniNF NF→¬R) public


----------------------------------------------------------------------------------------------------

det⇒ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒ t″ → t′ ≡ t″
det⇒ (cong$₁ r₁)     (cong$₁ r₁′)     = (_⌜$⌝ _) & det⇒ r₁ r₁′
det⇒ (cong$₁ r₁)     (cong$₂ p₁′ r₂′) = r₁ ↯ NF→¬R p₁′
det⇒ (cong$₂ p₁ r₂)  (cong$₁ r₁′)     = r₁′ ↯ NF→¬R p₁
det⇒ (cong$₂ p₁ r₂)  (cong$₂ p₁′ r₂′) = (_ ⌜$⌝_) & det⇒ r₂ r₂′
det⇒ (cong$₂ p₁ r₂)  (βred⊃ refl p₂′) = r₂ ↯ NF→¬R p₂′
det⇒ (congfst r)     (congfst r′)     = ⌜fst⌝ & det⇒ r r′
det⇒ (congsnd r)     (congsnd r′)     = ⌜snd⌝ & det⇒ r r′
det⇒ (βred⊃ refl p₂) (cong$₂ p₁′ r₂′) = r₂′ ↯ NF→¬R p₂
det⇒ (βred⊃ refl p₂) (βred⊃ refl p₂′) = refl
det⇒ βred∧₁          βred∧₁           = refl
det⇒ βred∧₂          βred∧₂           = refl

uni⇒ : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒ t′) → r ≡ r′
uni⇒ (cong$₁ r₁)     (cong$₁ r₁′)     = cong$₁ & uni⇒ r₁ r₁′
uni⇒ (cong$₁ r₁)     (cong$₂ p₁′ r₂′) = r₁ ↯ NF→¬R p₁′
uni⇒ (cong$₂ p₁ r₂)  (cong$₁ r₁′)     = r₁′ ↯ NF→¬R p₁
uni⇒ (cong$₂ p₁ r₂)  (cong$₂ p₁′ r₂′) = cong$₂ & uniNF p₁ p₁′ ⊗ uni⇒ r₂ r₂′
uni⇒ (cong$₂ p₁ r₂)  (βred⊃ eq′ p₂′)  = r₂ ↯ NF→¬R p₂′
uni⇒ (congfst r)     (congfst r′)     = congfst & uni⇒ r r′
uni⇒ (congsnd r)     (congsnd r′)     = congsnd & uni⇒ r r′
uni⇒ (βred⊃ eq p₂)   (cong$₂ p₁′ r₂′) = r₂′ ↯ NF→¬R p₂
uni⇒ (βred⊃ refl p₂) (βred⊃ refl p₂′) = βred⊃ refl & uniNF p₂ p₂′
uni⇒ βred∧₁          βred∧₁           = refl
uni⇒ βred∧₂          βred∧₂           = refl

open DetKit (kit redkit2 det⇒ uni⇒) public


----------------------------------------------------------------------------------------------------

prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
prog⇒ (var i)                = done (nnf var-)
prog⇒ (⌜λ⌝ t)                = done ⌜λ⌝-
prog⇒ (t₁ ⌜$⌝ t₂)            with prog⇒ t₁ | prog⇒ t₂
... | step r₁       | _         = step (cong$₁ r₁)
... | done p₁       | step r₂   = step (cong$₂ p₁ r₂)
... | done ⌜λ⌝-     | done p₂   = step (βred⊃ refl p₂)
... | done (nnf p₁) | done p₂   = done (nnf (p₁ ⌜$⌝ p₂))
prog⇒ (t₁ ⌜,⌝ t₂)              = done -⌜,⌝-
prog⇒ (⌜fst⌝ t)              with prog⇒ t
... | step r                    = step (congfst r)
... | done -⌜,⌝-                = step (βred∧₁)
... | done (nnf p)              = done (nnf (⌜fst⌝ p))
prog⇒ (⌜snd⌝ t)              with prog⇒ t
... | step r                    = step (congsnd r)
... | done -⌜,⌝-                = step (βred∧₂)
... | done (nnf p)              = done (nnf (⌜snd⌝ p))
prog⇒ ⌜unit⌝                   = done ⌜unit⌝

open ProgKit (kit redkit2 prog⇒) public


----------------------------------------------------------------------------------------------------

ren⇒ : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → t ⇒ t′ → ren ϱ t ⇒ ren ϱ t′
ren⇒ ϱ (cong$₁ r₁)               = cong$₁ (ren⇒ ϱ r₁)
ren⇒ ϱ (cong$₂ p₁ r₂)            = cong$₂ (renNF ϱ p₁) (ren⇒ ϱ r₂)
ren⇒ ϱ (congfst r)               = congfst (ren⇒ ϱ r)
ren⇒ ϱ (congsnd r)               = congsnd (ren⇒ ϱ r)
ren⇒ ϱ (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (rencut ϱ t₁ _ ⁻¹) (renNF ϱ p₂)
ren⇒ ϱ βred∧₁                    = βred∧₁
ren⇒ ϱ βred∧₂                    = βred∧₂

sub⇒ : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t t′ : Γ ⊢ A} → NNF§ σ → t ⇒ t′ → sub σ t ⇒ sub σ t′
sub⇒ ψ (cong$₁ r₁)               = cong$₁ (sub⇒ ψ r₁)
sub⇒ ψ (cong$₂ p₁ r₂)            = cong$₂ (subNF ψ p₁) (sub⇒ ψ r₂)
sub⇒ ψ (congfst r)               = congfst (sub⇒ ψ r)
sub⇒ ψ (congsnd r)               = congsnd (sub⇒ ψ r)
sub⇒ ψ (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (subcut _ t₁ _ ⁻¹) (subNF ψ p₂)
sub⇒ ψ βred∧₁                    = βred∧₁
sub⇒ ψ βred∧₂                    = βred∧₂


----------------------------------------------------------------------------------------------------
