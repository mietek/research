----------------------------------------------------------------------------------------------------

-- call-by-value reduction to β-short weak normal form

module STLC-Base-WNF-CBV where

open import STLC-Base-RenSub public
open import STLC-Base-WNF public
open import Kit3 public


----------------------------------------------------------------------------------------------------

infix 4 _⇒_
data _⇒_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  cong$₁ : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r₁ : t₁ ⇒ t₁′) →
           t₁ ⌜$⌝ t₂ ⇒ t₁′ ⌜$⌝ t₂
  cong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : NF t₁) (r₂ : t₂ ⇒ t₂′) →
           t₁ ⌜$⌝ t₂ ⇒ t₁ ⌜$⌝ t₂′
  βred⊃  : ∀ {A B} {t₁ : Γ , A ⊢ B} {t₂ : Γ ⊢ A} {t′} (eq : t′ ≡ t₁ [ t₂ ]) (p₂ : NF t₂) →
           ⌜λ⌝ t₁ ⌜$⌝ t₂ ⇒ t′

open RedKit1 (kit tmkit _⇒_) public

mutual
  NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t
  NF→¬R (nnf p) r = r ↯ NNF→¬R p

  NNF→¬R : ∀ {Γ A} {t  : Γ ⊢ A} → NNF t → ¬R t
  NNF→¬R (p₁ ⌜$⌝ p₂) (cong$₁ r₁)     = r₁ ↯ NNF→¬R p₁
  NNF→¬R (p₁ ⌜$⌝ p₂) (cong$₂ p₁′ r₂) = r₂ ↯ NF→¬R p₂

open RedKit2 (kit redkit1 uniNF NF→¬R) public


----------------------------------------------------------------------------------------------------

det⇒ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒ t″ → t′ ≡ t″
det⇒ (cong$₁ r₁)     (cong$₁ r₁′)     = (_⌜$⌝ _) & det⇒ r₁ r₁′
det⇒ (cong$₁ r₁)     (cong$₂ p₁′ r₂′) = r₁ ↯ NF→¬R p₁′
det⇒ (cong$₂ p₁ r₂)  (cong$₁ r₁′)     = r₁′ ↯ NF→¬R p₁
det⇒ (cong$₂ p₁ r₂)  (cong$₂ p₁′ r₂′) = (_ ⌜$⌝_) & det⇒ r₂ r₂′
det⇒ (cong$₂ p₁ r₂)  (βred⊃ refl p₂′) = r₂ ↯ NF→¬R p₂′
det⇒ (βred⊃ refl p₂) (cong$₂ p₁′ r₂′) = r₂′ ↯ NF→¬R p₂
det⇒ (βred⊃ refl p₂) (βred⊃ refl p₂′) = refl

uni⇒ : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒ t′) → r ≡ r′
uni⇒ (cong$₁ r₁)     (cong$₁ r₁′)     = cong$₁ & uni⇒ r₁ r₁′
uni⇒ (cong$₁ r₁)     (cong$₂ p₁′ r₂′) = r₁ ↯ NF→¬R p₁′
uni⇒ (cong$₂ p₁ r₂)  (cong$₁ r₁′)     = r₁′ ↯ NF→¬R p₁
uni⇒ (cong$₂ p₁ r₂)  (cong$₂ p₁′ r₂′) = cong$₂ & uniNF p₁ p₁′ ⊗ uni⇒ r₂ r₂′
uni⇒ (cong$₂ p₁ r₂)  (βred⊃ eq′ p₂′)  = r₂ ↯ NF→¬R p₂′
uni⇒ (βred⊃ eq p₂)   (cong$₂ p₁′ r₂′) = r₂′ ↯ NF→¬R p₂
uni⇒ (βred⊃ refl p₂) (βred⊃ refl p₂′) = βred⊃ refl & uniNF p₂ p₂′

open DetKit (kit redkit2 det⇒ uni⇒) public


----------------------------------------------------------------------------------------------------

module Progress where
  prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
  prog⇒ (var i)                = done (nnf var-)
  prog⇒ (⌜λ⌝ t)                = done ⌜λ⌝-
  prog⇒ (t₁ ⌜$⌝ t₂)            with prog⇒ t₁ | prog⇒ t₂
  ... | step r₁       | _         = step (cong$₁ r₁)
  ... | done p₁       | step r₂   = step (cong$₂ p₁ r₂)
  ... | done ⌜λ⌝-     | done p₂   = step (βred⊃ refl p₂)
  ... | done (nnf p₁) | done p₂   = done (nnf (p₁ ⌜$⌝ p₂))

  open ProgKit (kit redkit2 prog⇒) public hiding (NF?)

module ProgressAlt1 where
  ¬NF→RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ NF t → RF t
  ¬NF→RF {t = var i}         ¬p                   = nnf var- ↯ ¬p
  ¬NF→RF {t = ⌜λ⌝ t}         ¬p                   = ⌜λ⌝- ↯ ¬p
  ¬NF→RF {t = t₁ ⌜$⌝ t₂}     ¬p                   with NNF? t₁ | NF? t₂
  ¬NF→RF {t = _ ⌜$⌝ _}       ¬p | yes p₁ | yes p₂   = nnf (p₁ ⌜$⌝ p₂) ↯ ¬p
  ¬NF→RF {t = _ ⌜$⌝ _}       ¬p | yes p₁ | no ¬p₂   = let _ , r₂ = ¬NF→RF ¬p₂
                                                         in  _ , cong$₂ (nnf p₁) r₂
  ¬NF→RF {t = var _ ⌜$⌝ _}   ¬p | no ¬p₁ | _        = var- ↯ ¬p₁
  ¬NF→RF {t = ⌜λ⌝ _ ⌜$⌝ _}   ¬p | no ¬p₁ | yes p₂   = _ , βred⊃ refl p₂
  ¬NF→RF {t = ⌜λ⌝ _ ⌜$⌝ _}   ¬p | no ¬p₁ | no ¬p₂   = let _ , r₂ = ¬NF→RF ¬p₂
                                                         in  _ , cong$₂ ⌜λ⌝- r₂
  ¬NF→RF {t = _ ⌜$⌝ _ ⌜$⌝ _} ¬p | no ¬p₁ | _        = let _ , r₁ = ¬NF→RF λ { (nnf p₁) → p₁ ↯ ¬p₁ }
                                                         in  _ , cong$₁ r₁

  open NF?→ProgKit (kit redkit2 NF? ¬NF→RF) public

module ProgressAlt2 where

  ¬RF→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → NF t
  ¬RF→NF {t = var i}         ¬p               = nnf var-
  ¬RF→NF {t = ⌜λ⌝ t}         ¬p               = ⌜λ⌝-
  ¬RF→NF {t = var _ ⌜$⌝ _}   ¬p               with ¬RF→NF λ { (_ , r₂) → (_ , cong$₂ (nnf var-) r₂) ↯ ¬p }
  ¬RF→NF {t = var _ ⌜$⌝ _}   ¬p | p₂            = nnf (var- ⌜$⌝ p₂)
  ¬RF→NF {t = ⌜λ⌝ _ ⌜$⌝ _}   ¬p               with ¬RF→NF λ { (_ , r₂) → (_ , cong$₂ ⌜λ⌝- r₂) ↯ ¬p }
  ¬RF→NF {t = ⌜λ⌝ _ ⌜$⌝ _}   ¬p | p₂            = (_ , βred⊃ refl p₂) ↯ ¬p
  ¬RF→NF {t = _ ⌜$⌝ _ ⌜$⌝ _} ¬p               with ¬RF→NF λ { (_ , r₁) → (_ , cong$₁ r₁) ↯ ¬p }
  ¬RF→NF {t = _ ⌜$⌝ _ ⌜$⌝ _} ¬p | nnf p₁        with ¬RF→NF λ { (_ , r₁) → (_ , cong$₂ (nnf p₁) r₁) ↯ ¬p }
  ¬RF→NF {t = _ ⌜$⌝ _ ⌜$⌝ _} ¬p | nnf p₁ | p₂     = nnf (p₁ ⌜$⌝ p₂)

  RF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (RF t)
  RF? (var i)                                       = no λ ()
  RF? (⌜λ⌝ t)                                       = no λ ()
  RF? (t₁ ⌜$⌝ t₂)                                   with RF? t₁ | RF? t₂
  RF? (_ ⌜$⌝ _)       | no ¬p₁       | yes (_ , r₂)   = yes (_ , cong$₂ (¬RF→NF ¬p₁) r₂)
  RF? (var _ ⌜$⌝ _)   | no ¬p₁       | no ¬p₂         = no λ { (_ , cong$₂ p₁ r₂) → r₂ ↯ ¬RF→¬R ¬p₂ }
  RF? (⌜λ⌝ _ ⌜$⌝ _)   | no ¬p₁       | no ¬p₂         = yes (_ , βred⊃ refl (¬RF→NF ¬p₂))
  RF? (_ ⌜$⌝ _ ⌜$⌝ _) | no ¬p₁       | no ¬p₂         = no λ { (_ , cong$₁ r₁) → r₁ ↯ ¬RF→¬R ¬p₁
                                                             ; (_ , cong$₂ p₁ r₂) → r₂ ↯ ¬RF→¬R ¬p₂
                                                             }
  RF? (_ ⌜$⌝ _ ⌜$⌝ _) | yes (_ , r₁) | _              = yes (_ , cong$₁ r₁)

  open RF?→ProgKit (kit redkit2 RF? ¬RF→NF) public

open Progress public


----------------------------------------------------------------------------------------------------

ren⇒ : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (ρ : Γ ⊑ Γ′) → t ⇒ t′ → ren ρ t ⇒ ren ρ t′
ren⇒ ρ (cong$₁ r₁)               = cong$₁ (ren⇒ ρ r₁)
ren⇒ ρ (cong$₂ p₁ r₂)            = cong$₂ (renNF ρ p₁) (ren⇒ ρ r₂)
ren⇒ ρ (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (rencut ρ t₁ _ ⁻¹) (renNF ρ p₂)

sub⇒ : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t t′ : Γ ⊢ A} → NNF§ σ → t ⇒ t′ → sub σ t ⇒ sub σ t′
sub⇒ ψ (cong$₁ r₁)               = cong$₁ (sub⇒ ψ r₁)
sub⇒ ψ (cong$₂ p₁ r₂)            = cong$₂ (subNF ψ p₁) (sub⇒ ψ r₂)
sub⇒ ψ (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (subcut _ t₁ _ ⁻¹) (subNF ψ p₂)


----------------------------------------------------------------------------------------------------

-- TODO: SN
cong$₁⇒* : ∀ {Γ A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} → t₁ ⇒* t₁′ →
            t₁ ⌜$⌝ t₂ ⇒* t₁′ ⌜$⌝ t₂
cong$₁⇒* done        = done
cong$₁⇒* (step r rs) = step (cong$₁ r) (cong$₁⇒* rs)

cong$₂⇒* : ∀ {Γ A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} → NF t₁ → t₂ ⇒* t₂′ →
            t₁ ⌜$⌝ t₂ ⇒* t₁ ⌜$⌝ t₂′
cong$₂⇒* p₁ done        = done
cong$₂⇒* p₁ (step r rs) = step (cong$₂ p₁ r) (cong$₂⇒* p₁ rs)

ren⇒* : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (ρ : Γ ⊑ Γ′) → t ⇒* t′ → ren ρ t ⇒* ren ρ t′
ren⇒* ρ done        = done
ren⇒* ρ (step r rs) = step (ren⇒ ρ r) (ren⇒* ρ rs)

sub⇒* : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t t′ : Γ ⊢ A} (ψ : NNF§ σ) → t ⇒* t′ →
         sub σ t ⇒* sub σ t′
sub⇒* ψ done        = done
sub⇒* ψ (step r rs) = step (sub⇒ ψ r) (sub⇒* ψ rs)


----------------------------------------------------------------------------------------------------

-- TODO: rename `rp`
infix 4 _⇓_
_⇓_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
t ⇓ t′ = t ⇒* t′ × NF t′

step⇓ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t′ ⇓ t″ → t ⇓ t″
step⇓ r (rs′ , p″) = step r rs′ , p″

skip⇓ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇓ t″ → t′ ⇓ t″
skip⇓ r (rs′ , p″) = skip⇒* r rs′ p″ , p″

det⇓ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇓ t′ → t ⇓ t″ → t′ ≡ t″
det⇓ (rs , p′) (rs′ , p″) = det⇒* rs p′ rs′ p″

uni⇓ : ∀ {Γ A} {t t′ : Γ ⊢ A} (rp rp′ : t ⇓ t′) → rp ≡ rp′
uni⇓ (rs , p′) (rs′ , p″) = _,_ & uni⇒* rs rs′ p′ ⊗ uniNF p′ p″

ren⇓ : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (ρ : Γ ⊑ Γ′) → t ⇓ t′ → ren ρ t ⇓ ren ρ t′
ren⇓ ρ (rs , p′) = ren⇒* ρ rs , renNF ρ p′

sub⇓ : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t t′ : Γ ⊢ A} (ψ : NNF§ σ) → t ⇓ t′ → sub σ t ⇓ sub σ t′
sub⇓ ψ (rs , p′) = sub⇒* ψ rs , subNF ψ p′


----------------------------------------------------------------------------------------------------

WN : ∀ {Γ A} → Γ ⊢ A → Set
WN t = Σ _ λ t′ → t ⇓ t′

stepWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒ t′ → WN t′ → WN t
stepWN r (t″ , rp′) = t″ , step⇓ r rp′

skipWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒ t′ → WN t → WN t′
skipWN r (t″ , rp′) = t″ , skip⇓ r rp′

uniWN : ∀ {Γ A} {t : Γ ⊢ A} (wn wn′ : WN t) → wn ≡ wn′
uniWN (t′ , rp) (t″ , rp′) with det⇓ rp rp′
... | refl                   = (_ ,_) & uni⇓ rp rp′

renWN : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ρ : Γ ⊑ Γ′) → WN t → WN (ren ρ t)
renWN ρ (t′ , rp) = ren ρ t′ , ren⇓ ρ rp

subWN : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {t : Γ ⊢ A} (ψ : NNF§ σ) → WN t → WN (sub σ t)
subWN ψ (t′ , rp) = sub _ t′ , sub⇓ ψ rp


----------------------------------------------------------------------------------------------------
