module STLC-Base-Weak-NotEtaLong where

open import STLC-Base-Properties public
open import Kit3 public


----------------------------------------------------------------------------------------------------

-- β-short not-η-long weak normal forms
mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝- : ∀ {A B} {t : A ∷ Γ ⊢ B} → NF (⌜λ⌝ t)
    nnf  : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    var-  : ∀ {A} {i : Γ ∋ A} → NNF (var i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)

data NNF* {Γ} : ∀ {Δ} → Γ ⊢* Δ → Set where
  []  : NNF* []
  _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} → NNF t → NNF* ts → NNF* (t ∷ ts)

mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF ⌜λ⌝-    ⌜λ⌝-     = refl
  uniNF (nnf p) (nnf p′) = nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
  uniNNF var-        var-          = refl
  uniNNF (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′

mutual
  NF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (NF t)
  NF? (var i)           = yes (nnf var-)
  NF? (⌜λ⌝ t)           = yes ⌜λ⌝-
  NF? (t₁ ⌜$⌝ t₂)       with NNF? t₁ | NF? t₂
  ... | yes p₁ | yes p₂   = yes (nnf (p₁ ⌜$⌝ p₂))
  ... | yes p₁ | no ¬p₂   = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _        = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₁ ↯ ¬p₁ }

  NNF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (NNF t)
  NNF? (var i)          = yes var-
  NNF? (⌜λ⌝ t)          = no λ ()
  NNF? (t₁ ⌜$⌝ t₂)      with NNF? t₁ | NF? t₂
  ... | yes p₁ | yes p₂   = yes (p₁ ⌜$⌝ p₂)
  ... | yes p₁ | no ¬p₂   = no λ { (p₁ ⌜$⌝ p₂) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _        = no λ { (p₁ ⌜$⌝ p₂) → p₁ ↯ ¬p₁ }


----------------------------------------------------------------------------------------------------

-- call-by-value reduction
infix 4 _⇒_
data _⇒_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  cong$₁ : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r : t₁ ⇒ t₁′) →
           t₁ ⌜$⌝ t₂ ⇒ t₁′ ⌜$⌝ t₂
  cong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : NF t₁) (r₂ : t₂ ⇒ t₂′) →
           t₁ ⌜$⌝ t₂ ⇒ t₁ ⌜$⌝ t₂′
  βred⊃  : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ])
             (p₂ : NF t₂) →
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

-- stability under renaming
mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NF t → NF (ren e t)
  renNF e ⌜λ⌝-    = ⌜λ⌝-
  renNF e (nnf p) = nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF t → NNF (ren e t)
  renNNF e var-        = var-
  renNNF e (p₁ ⌜$⌝ p₂) = renNNF e p₁ ⌜$⌝ renNF e p₂

ren⇒ : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (e : Γ ⊆ Γ′) → t ⇒ t′ → ren e t ⇒ ren e t′
ren⇒ e (cong$₁ r₁)               = cong$₁ (ren⇒ e r₁)
ren⇒ e (cong$₂ p₁ r₂)            = cong$₂ (renNF e p₁) (ren⇒ e r₂)
ren⇒ e (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (rencut e t₁ _ ⁻¹) (renNF e p₂)


----------------------------------------------------------------------------------------------------

-- stability under substitution
sub∋NNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} → NNF* ss → ∀ (i : Γ ∋ A) → NNF (sub∋ ss i)
sub∋NNF (p ∷ ps) zero    = p
sub∋NNF (p ∷ ps) (suc i) = sub∋NNF ps i

mutual
  subNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → NNF* ss → NF t → NF (sub ss t)
  subNF ps ⌜λ⌝-    = ⌜λ⌝-
  subNF ps (nnf p) = nnf (subNNF ps p)

  subNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → NNF* ss → NNF t → NNF (sub ss t)
  subNNF ps (var- {i = i}) = sub∋NNF ps i
  subNNF ps (p₁ ⌜$⌝ p₂)    = subNNF ps p₁ ⌜$⌝ subNF ps p₂

sub⇒ : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t t′ : Γ ⊢ A} → NNF* ss → t ⇒ t′ →
        sub ss t ⇒ sub ss t′
sub⇒ ps (cong$₁ r₁)               = cong$₁ (sub⇒ ps r₁)
sub⇒ ps (cong$₂ p₁ r₂)            = cong$₂ (subNF ps p₁) (sub⇒ ps r₂)
sub⇒ ps (βred⊃ {t₁ = t₁} refl p₂) = βred⊃ (subcut _ t₁ _ ⁻¹) (subNF ps p₂)


----------------------------------------------------------------------------------------------------

-- β-short not-η-long weak normal forms (direct)
mutual
  infix 3 _⊢≪_
  data _⊢≪_ (Γ : Ctx) : Ty → Set where
    ⌜λ⌝ : ∀ {A B} (t : A ∷ Γ ⊢ B) → Γ ⊢≪ A ⌜⊃⌝ B
    nnf : ∀ {A} (t : Γ ⊢≫ A) → Γ ⊢≪ A

  infix 3 _⊢≫_
  data _⊢≫_ (Γ : Ctx) : Ty → Set where
    var   : ∀ {A} (i : Γ ∋ A) → Γ ⊢≫ A
    _⌜$⌝_ : ∀ {A B} (t₁ : Γ ⊢≫ A ⌜⊃⌝ B) (t₂ : Γ ⊢≪ A) → Γ ⊢≫ B

-- equivalence
mutual
  ⊢≪→NF : ∀ {Γ A} → Γ ⊢≪ A → Σ (Γ ⊢ A) NF
  ⊢≪→NF (⌜λ⌝ t) = ⌜λ⌝ t , ⌜λ⌝-
  ⊢≪→NF (nnf t) with ⊢≫→NNF t
  ... | t′ , p′     = t′ , nnf p′

  ⊢≫→NNF : ∀ {Γ A} → Γ ⊢≫ A → Σ (Γ ⊢ A) NNF
  ⊢≫→NNF (var i)             = var i , var-
  ⊢≫→NNF (t₁ ⌜$⌝ t₂)         with ⊢≫→NNF t₁ | ⊢≪→NF t₂
  ... | t₁′ , p₁′ | t₂′ , p₂′    = t₁′ ⌜$⌝ t₂′ , p₁′ ⌜$⌝ p₂′

mutual
  NF→⊢≪ : ∀ {Γ A} → Σ (Γ ⊢ A) NF → Γ ⊢≪ A
  NF→⊢≪ (.(⌜λ⌝ t) , ⌜λ⌝- {t = t}) = ⌜λ⌝ t
  NF→⊢≪ (t , nnf p)               = nnf (NNF→⊢≫ (t , p))

  NNF→⊢≫ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → Γ ⊢≫ A
  NNF→⊢≫ (var i , var-)          = var i
  NNF→⊢≫ (t₁ ⌜$⌝ t₂ , p₁ ⌜$⌝ p₂) = NNF→⊢≫ (t₁ , p₁) ⌜$⌝ NF→⊢≪ (t₂ , p₂)

-- isomorphism
mutual
  id⊢≪⇄NF : ∀ {Γ A} (t : Γ ⊢≪ A) → (NF→⊢≪ ∘ ⊢≪→NF) t ≡ t
  id⊢≪⇄NF (⌜λ⌝ t) = refl
  id⊢≪⇄NF (nnf t) = nnf & id⊢≫⇄NNF t

  id⊢≫⇄NNF : ∀ {Γ A} (t : Γ ⊢≫ A) → (NNF→⊢≫ ∘ ⊢≫→NNF) t ≡ t
  id⊢≫⇄NNF (var i)     = refl
  id⊢≫⇄NNF (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & id⊢≫⇄NNF t₁ ⊗ id⊢≪⇄NF t₂

module _ where
  open ≡-Reasoning

  mutual
    idNF⇄⊢≪ : ∀ {Γ A} (tp : Σ (Γ ⊢ A) NF) → (⊢≪→NF ∘ NF→⊢≪) tp ≡ tp
    idNF⇄⊢≪ (.(⌜λ⌝ t) , ⌜λ⌝- {t = t}) = refl
    idNF⇄⊢≪ (t , nnf p)               =
      let eqₜ : fst (⊢≫→NNF (NNF→⊢≫ (t , p))) ≡ t
          eqₜ = fst & idNNF⇄⊢≫ (t , p)
          eqₚ : NF.nnf (snd (⊢≫→NNF (NNF→⊢≫ (t , p)))) ≅ NF.nnf p
          eqₚ = (NF.nnf ∘ snd) &≅ ≡→≅ (idNNF⇄⊢≫ (t , p))
        in begin
             fst (⊢≫→NNF (NNF→⊢≫ (t , p))) , nnf (snd (⊢≫→NNF (NNF→⊢≫ (t , p))))
           ≡⟨ ≅→≡ (cong₂≅ _,_ (≡→≅ eqₜ) eqₚ) ⟩
             t , nnf p
           ∎

    idNNF⇄⊢≫ : ∀ {Γ A} (tp : Σ (Γ ⊢ A) NNF) → (⊢≫→NNF ∘ NNF→⊢≫) tp ≡ tp
    idNNF⇄⊢≫ (var i , var-)          = refl
    idNNF⇄⊢≫ (t₁ ⌜$⌝ t₂ , p₁ ⌜$⌝ p₂) =
      let eqₜ : fst (⊢≫→NNF (NNF→⊢≫ (t₁ , p₁))) _⊢_.⌜$⌝ fst (⊢≪→NF (NF→⊢≪ (t₂ , p₂))) ≡ t₁ _⊢_.⌜$⌝ t₂
          eqₜ = (λ x₁ x₂ → fst x₁ ⌜$⌝ fst x₂) & idNNF⇄⊢≫ (t₁ , p₁) ⊗ idNF⇄⊢≪ (t₂ , p₂)
          eqₚ : snd (⊢≫→NNF (NNF→⊢≫ (t₁ , p₁))) NNF.⌜$⌝ snd (⊢≪→NF (NF→⊢≪ (t₂ , p₂))) ≅ p₁ NNF.⌜$⌝ p₂
          eqₚ = cong₂≅ (λ x₁ x₂ → snd x₁ NNF.⌜$⌝ snd x₂)
                  (≡→≅ (idNNF⇄⊢≫ (t₁ , p₁))) (≡→≅ (idNF⇄⊢≪ (t₂ , p₂)))
        in begin
             fst (⊢≫→NNF (NNF→⊢≫ (t₁ , p₁))) ⌜$⌝ fst (⊢≪→NF (NF→⊢≪ (t₂ , p₂))) ,
             snd (⊢≫→NNF (NNF→⊢≫ (t₁ , p₁))) ⌜$⌝ snd (⊢≪→NF (NF→⊢≪ (t₂ , p₂)))
           ≡⟨ ≅→≡ (cong₂≅ _,_ (≡→≅ eqₜ) eqₚ) ⟩
             t₁ ⌜$⌝ t₂ , p₁ ⌜$⌝ p₂
           ∎

⊢≪≃NF : ∀ {Γ A} → (Γ ⊢≪ A) ≃ (Σ (Γ ⊢ A) NF)
⊢≪≃NF = record
  { to      = ⊢≪→NF
  ; from    = NF→⊢≪
  ; from∘to = id⊢≪⇄NF
  ; to∘from = idNF⇄⊢≪
  }

⊢≫≃NNF : ∀ {Γ A} → (Γ ⊢≫ A) ≃ (Σ (Γ ⊢ A) NNF)
⊢≫≃NNF = record
  { to      = ⊢≫→NNF
  ; from    = NNF→⊢≫
  ; from∘to = id⊢≫⇄NNF
  ; to∘from = idNNF⇄⊢≫
  }


----------------------------------------------------------------------------------------------------

cong$₁⇒* : ∀ {Γ A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} → t₁ ⇒* t₁′ →
            t₁ ⌜$⌝ t₂ ⇒* t₁′ ⌜$⌝ t₂
cong$₁⇒* done        = done
cong$₁⇒* (step r rs) = step (cong$₁ r) (cong$₁⇒* rs)

cong$₂⇒* : ∀ {Γ A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} → NF t₁ → t₂ ⇒* t₂′ →
            t₁ ⌜$⌝ t₂ ⇒* t₁ ⌜$⌝ t₂′
cong$₂⇒* p₁ done        = done
cong$₂⇒* p₁ (step r rs) = step (cong$₂ p₁ r) (cong$₂⇒* p₁ rs)

ren⇒* : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (e : Γ ⊆ Γ′) → t ⇒* t′ → ren e t ⇒* ren e t′
ren⇒* e done        = done
ren⇒* e (step r rs) = step (ren⇒ e r) (ren⇒* e rs)

sub⇒* : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t t′ : Γ ⊢ A} (ps : NNF* ss) → t ⇒* t′ →
         sub ss t ⇒* sub ss t′
sub⇒* ps done        = done
sub⇒* ps (step r rs) = step (sub⇒ ps r) (sub⇒* ps rs)


----------------------------------------------------------------------------------------------------

infix 4 _⇓_
_⇓_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
t ⇓ t′ = t ⇒* t′ × NF t′

step⇓ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t′ ⇓ t″ → t ⇓ t″
step⇓ r (rs′ , p″) = step r rs′ , p″

skip⇓ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇓ t″ → t′ ⇓ t″
skip⇓ r (rs′ , p″) = skip⇒* r rs′ p″ , p″

det⇓ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇓ t′ → t ⇓ t″ → t′ ≡ t″
det⇓ (rs , p′) (rs′ , p″) = det⇒* rs p′ rs′ p″

uni⇓ : ∀ {Γ A} {t t′ : Γ ⊢ A} (n n′ : t ⇓ t′) → n ≡ n′
uni⇓ (rs , p′) (rs′ , p″) = _,_ & uni⇒* rs rs′ p′ ⊗ uniNF p′ p″

ren⇓ : ∀ {Γ Γ′ A} {t t′ : Γ ⊢ A} (e : Γ ⊆ Γ′) → t ⇓ t′ → ren e t ⇓ ren e t′
ren⇓ e (rs , p′) = ren⇒* e rs , renNF e p′

sub⇓ : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t t′ : Γ ⊢ A} (ps : NNF* ss) → t ⇓ t′ → sub ss t ⇓ sub ss t′
sub⇓ ps (rs , p′) = sub⇒* ps rs , subNF ps p′


----------------------------------------------------------------------------------------------------

WN : ∀ {Γ A} → Γ ⊢ A → Set
WN t = Σ _ λ t′ → t ⇓ t′

stepWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒ t′ → WN t′ → WN t
stepWN r (t″ , n′) = t″ , step⇓ r n′

skipWN : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒ t′ → WN t → WN t′
skipWN r (t″ , n′) = t″ , skip⇓ r n′

uniWN : ∀ {Γ A} {t : Γ ⊢ A} (wn wn′ : WN t) → wn ≡ wn′
uniWN (t′ , n) (t″ , n′) with det⇓ n n′
... | refl                 = (_ ,_) & uni⇓ n n′

renWN : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → WN t → WN (ren e t)
renWN e (t′ , n) = ren e t′ , ren⇓ e n

subWN : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} (ps : NNF* ss) → WN t → WN (sub ss t)
subWN ps (t′ , n) = sub _ t′ , sub⇓ ps n


----------------------------------------------------------------------------------------------------
