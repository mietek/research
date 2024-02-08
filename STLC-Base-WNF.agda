module STLC-Base-WNF where

open import STLC-Base public


----------------------------------------------------------------------------------------------------

-- β-short weak normal forms
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

mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NF t → NF (ren e t)
  renNF e ⌜λ⌝-    = ⌜λ⌝-
  renNF e (nnf p) = nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF t → NNF (ren e t)
  renNNF e var-        = var-
  renNNF e (p₁ ⌜$⌝ p₂) = renNNF e p₁ ⌜$⌝ renNF e p₂

sub∋NNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {i : Γ ∋ A} → NNF* ss → NNF (sub∋ ss i)
sub∋NNF {i = zero}  (p ∷ ps) = p
sub∋NNF {i = suc i} (p ∷ ps) = sub∋NNF ps

mutual
  subNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → NNF* ss → NF t → NF (sub ss t)
  subNF ps ⌜λ⌝-    = ⌜λ⌝-
  subNF ps (nnf p) = nnf (subNNF ps p)

  subNNF : ∀ {Γ Ξ A} {ss : Ξ ⊢* Γ} {t : Γ ⊢ A} → NNF* ss → NNF t → NNF (sub ss t)
  subNNF ps var-        = sub∋NNF ps
  subNNF ps (p₁ ⌜$⌝ p₂) = subNNF ps p₁ ⌜$⌝ subNF ps p₂


----------------------------------------------------------------------------------------------------

mutual
  infix 3 _⊢≪_
  data _⊢≪_ (Γ : Ctx) : Ty → Set where
    ⌜λ⌝ : ∀ {A B} (t : A ∷ Γ ⊢ B) → Γ ⊢≪ A ⌜⊃⌝ B
    nnf : ∀ {A} (t : Γ ⊢≫ A) → Γ ⊢≪ A

  infix 3 _⊢≫_
  data _⊢≫_ (Γ : Ctx) : Ty → Set where
    var   : ∀ {A} (i : Γ ∋ A) → Γ ⊢≫ A
    _⌜$⌝_ : ∀ {A B} (t₁ : Γ ⊢≫ A ⌜⊃⌝ B) (t₂ : Γ ⊢≪ A) → Γ ⊢≫ B


----------------------------------------------------------------------------------------------------

-- direct normal forms are isomorphic to predicate normal forms
private
  open ≡-Reasoning

  mutual
    toNF : ∀ {Γ A} → Γ ⊢≪ A → Σ (Γ ⊢ A) NF
    toNF (⌜λ⌝ t) = ⌜λ⌝ t , ⌜λ⌝-
    toNF (nnf t) with toNNF t
    ... | t′ , p′     = t′ , nnf p′

    toNNF : ∀ {Γ A} → Γ ⊢≫ A → Σ (Γ ⊢ A) NNF
    toNNF (var i)             = var i , var-
    toNNF (t₁ ⌜$⌝ t₂)         with toNNF t₁ | toNF t₂
    ... | t₁′ , p₁′ | t₂′ , p₂′    = t₁′ ⌜$⌝ t₂′ , p₁′ ⌜$⌝ p₂′

  mutual
    fromNF : ∀ {Γ A} → Σ (Γ ⊢ A) NF → Γ ⊢≪ A
    fromNF (.(⌜λ⌝ t) , ⌜λ⌝- {t = t}) = ⌜λ⌝ t
    fromNF (t , nnf p)               = nnf (fromNNF (t , p))

    fromNNF : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → Γ ⊢≫ A
    fromNNF (var i , var-)          = var i
    fromNNF (t₁ ⌜$⌝ t₂ , p₁ ⌜$⌝ p₂) = fromNNF (t₁ , p₁) ⌜$⌝ fromNF (t₂ , p₂)

  mutual
    from∘toNF : ∀ {Γ A} (t : Γ ⊢≪ A) → (fromNF ∘ toNF) t ≡ t
    from∘toNF (⌜λ⌝ t) = refl
    from∘toNF (nnf t) = nnf & from∘toNNF t

    from∘toNNF : ∀ {Γ A} (t : Γ ⊢≫ A) → (fromNNF ∘ toNNF) t ≡ t
    from∘toNNF (var i)     = refl
    from∘toNNF (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & from∘toNNF t₁ ⊗ from∘toNF t₂

  mutual
    to∘fromNF : ∀ {Γ A} (tp : Σ (Γ ⊢ A) NF) → (toNF ∘ fromNF) tp ≡ tp
    to∘fromNF (.(⌜λ⌝ t) , ⌜λ⌝- {t = t}) = refl
    to∘fromNF (t , nnf p)               = ≅→≡ (hcong₂ _,_
                                            (≡→≅ (cong fst (to∘fromNNF (t , p))))
                                            (hcong (NF.nnf ∘ snd) (≡→≅ (to∘fromNNF (t , p)))))

    to∘fromNNF : ∀ {Γ A} (tp : Σ (Γ ⊢ A) NNF) → (toNNF ∘ fromNNF) tp ≡ tp
    to∘fromNNF (var i , var-)          = refl
    to∘fromNNF (t₁ ⌜$⌝ t₂ , p₁ ⌜$⌝ p₂) = ≅→≡ (hcong₂ _,_
                                           (≡→≅ (cong₂ (λ x₁ x₂ → fst x₁ ⌜$⌝ fst x₂)
                                             (to∘fromNNF (t₁ , p₁))
                                             (to∘fromNF (t₂ , p₂))))
                                           (hcong₂ (λ x₁ x₂ → snd x₁ NNF.⌜$⌝ snd x₂)
                                             (≡→≅ (to∘fromNNF (t₁ , p₁)))
                                             (≡→≅ (to∘fromNF (t₂ , p₂)))))

  ⊢≪≃NF : ∀ {Γ A} → (Γ ⊢≪ A) ≃ (Σ (Γ ⊢ A) NF)
  ⊢≪≃NF = record
             { to      = toNF
             ; from    = fromNF
             ; from∘to = from∘toNF
             ; to∘from = to∘fromNF
             }

  ⊢≫≃NNF : ∀ {Γ A} → (Γ ⊢≫ A) ≃ (Σ (Γ ⊢ A) NNF)
  ⊢≫≃NNF = record
              { to      = toNNF
              ; from    = fromNNF
              ; from∘to = from∘toNNF
              ; to∘from = to∘fromNNF
              }


----------------------------------------------------------------------------------------------------
