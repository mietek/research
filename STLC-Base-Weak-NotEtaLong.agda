module STLC-Base-Weak-NotEtaLong where

open import STLC-Base public
open import Isomorphism public


----------------------------------------------------------------------------------------------------

-- β-short not-η-long weak normal forms
mutual
  data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝- : ∀ {A B} {t : A ∷ Γ ⊢ B} → NF (⌜λ⌝ t)
    nnf  : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t

  -- neutrals
  data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜v⌝-  : ∀ {A} {i : Γ ∋ A} → NNF (⌜v⌝ i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)

-- renaming
mutual
  renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NF t → NF (ren⊢ e t)
  renNF e ⌜λ⌝-    = ⌜λ⌝-
  renNF e (nnf p) = nnf (renNNF e p)

  renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF t → NNF (ren⊢ e t)
  renNNF e ⌜v⌝-        = ⌜v⌝-
  renNNF e (p₁ ⌜$⌝ p₂) = renNNF e p₁ ⌜$⌝ renNF e p₂

-- uniqueness of proofs
mutual
  uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
  uniNF ⌜λ⌝-    ⌜λ⌝-     = refl
  uniNF (nnf p) (nnf p′) = nnf & uniNNF p p′

  uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
  uniNNF ⌜v⌝-        ⌜v⌝-          = refl
  uniNNF (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′

mutual
  NF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (NF t)
  NF? (⌜v⌝ i)           = yes (nnf ⌜v⌝-)
  NF? (⌜λ⌝ t)           = yes ⌜λ⌝-
  NF? (t₁ ⌜$⌝ t₂)       with NNF? t₁ | NF? t₂
  ... | yes p₁ | yes p₂   = yes (nnf (p₁ ⌜$⌝ p₂))
  ... | yes p₁ | no ¬p₂   = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _        = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₁ ↯ ¬p₁ }

  NNF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (NNF t)
  NNF? (⌜v⌝ i)          = yes ⌜v⌝-
  NNF? (⌜λ⌝ t)          = no λ ()
  NNF? (t₁ ⌜$⌝ t₂)      with NNF? t₁ | NF? t₂
  ... | yes p₁ | yes p₂   = yes (p₁ ⌜$⌝ p₂)
  ... | yes p₁ | no ¬p₂   = no λ { (p₁ ⌜$⌝ p₂) → p₂ ↯ ¬p₂ }
  ... | no ¬p₁ | _        = no λ { (p₁ ⌜$⌝ p₂) → p₁ ↯ ¬p₁ }


----------------------------------------------------------------------------------------------------

-- β-short not-η-long weak normal forms (direct)
mutual
  infix 3 _⋘_
  data _⋘_ (Γ : Ctx) : Ty → Set where
    ⌜λ⌝ : ∀ {A B} (t : A ∷ Γ ⊢ B) → Γ ⋘ A ⌜⊃⌝ B
    nnf : ∀ {A} (t : Γ ⋙ A) → Γ ⋘ A

  infix 3 _⋙_
  data _⋙_ (Γ : Ctx) : Ty → Set where
    ⌜v⌝   : ∀ {A} (i : Γ ∋ A) → Γ ⋙ A
    _⌜$⌝_ : ∀ {A B} (t₁ : Γ ⋙ A ⌜⊃⌝ B) (t₂ : Γ ⋘ A) → Γ ⋙ B

mutual
  ⋘→NF : ∀ {Γ A} → Γ ⋘ A → Σ (Γ ⊢ A) NF
  ⋘→NF (⌜λ⌝ t) = ⌜λ⌝ t , ⌜λ⌝-
  ⋘→NF (nnf t) with ⋙→NNF t
  ... | t′ , p′    = t′ , nnf p′

  ⋙→NNF : ∀ {Γ A} → Γ ⋙ A → Σ (Γ ⊢ A) NNF
  ⋙→NNF (⌜v⌝ i)             = ⌜v⌝ i , ⌜v⌝-
  ⋙→NNF (t₁ ⌜$⌝ t₂)         with ⋙→NNF t₁ | ⋘→NF t₂
  ... | t₁′ , p₁′ | t₂′ , p₂′   = t₁′ ⌜$⌝ t₂′ , p₁′ ⌜$⌝ p₂′

mutual
  NF→⋘ : ∀ {Γ A} → Σ (Γ ⊢ A) NF → Γ ⋘ A
  NF→⋘ (.(⌜λ⌝ t) , ⌜λ⌝- {t = t}) = ⌜λ⌝ t
  NF→⋘ (t , nnf p)               = nnf (NNF→⋙ (t , p))

  NNF→⋙ : ∀ {Γ A} → Σ (Γ ⊢ A) NNF → Γ ⋙ A
  NNF→⋙ (⌜v⌝ i , ⌜v⌝-)          = ⌜v⌝ i
  NNF→⋙ (t₁ ⌜$⌝ t₂ , p₁ ⌜$⌝ p₂) = NNF→⋙ (t₁ , p₁) ⌜$⌝ NF→⋘ (t₂ , p₂)

mutual
  id⋘⇄NF : ∀ {Γ A} (t : Γ ⋘ A) → (NF→⋘ ∘ ⋘→NF) t ≡ t
  id⋘⇄NF (⌜λ⌝ t) = refl
  id⋘⇄NF (nnf t) = nnf & id⋙⇄NNF t

  id⋙⇄NNF : ∀ {Γ A} (t : Γ ⋙ A) → (NNF→⋙ ∘ ⋙→NNF) t ≡ t
  id⋙⇄NNF (⌜v⌝ i)     = refl
  id⋙⇄NNF (t₁ ⌜$⌝ t₂) = _⌜$⌝_ & id⋙⇄NNF t₁ ⊗ id⋘⇄NF t₂

module _ where
  open ≡-Reasoning

  mutual
    idNF⇄⋘ : ∀ {Γ A} (tp : Σ (Γ ⊢ A) NF) → (⋘→NF ∘ NF→⋘) tp ≡ tp
    idNF⇄⋘ (.(⌜λ⌝ t) , ⌜λ⌝- {t = t}) = refl
    idNF⇄⋘ (t , nnf p)               =
      let
        eqₜ : proj₁ (⋙→NNF (NNF→⋙ (t , p))) ≡ t
        eqₜ = cong proj₁ (idNNF⇄⋙ (t , p))

        eqₚ : nnf (proj₂ (⋙→NNF (NNF→⋙ (t , p)))) ≅ nnf p
        eqₚ = cong≅ (NF.nnf ∘ proj₂) (≡→≅ (idNNF⇄⋙ (t , p)))
      in
        begin
          proj₁ (⋙→NNF (NNF→⋙ (t , p))) , nnf (proj₂ (⋙→NNF (NNF→⋙ (t , p))))
        ≡⟨ ≅→≡ (cong₂≅ _,_ (≡→≅ eqₜ) eqₚ) ⟩
          t , nnf p
        ∎

    idNNF⇄⋙ : ∀ {Γ A} (tp : Σ (Γ ⊢ A) NNF) → (⋙→NNF ∘ NNF→⋙) tp ≡ tp
    idNNF⇄⋙ (⌜v⌝ i , ⌜v⌝-)          = refl
    idNNF⇄⋙ (t₁ ⌜$⌝ t₂ , p₁ ⌜$⌝ p₂) =
      let
        eqₜ : proj₁ (⋙→NNF (NNF→⋙ (t₁ , p₁))) ⌜$⌝ proj₁ (⋘→NF (NF→⋘ (t₂ , p₂))) ≡ t₁ ⌜$⌝ t₂
        eqₜ = cong₂ _⌜$⌝_ (cong proj₁ (idNNF⇄⋙ (t₁ , p₁))) (cong proj₁ (idNF⇄⋘ (t₂ , p₂)))

        eqₚ : proj₂ (⋙→NNF (NNF→⋙ (t₁ , p₁))) ⌜$⌝ proj₂ (⋘→NF (NF→⋘ (t₂ , p₂))) ≅ p₁ ⌜$⌝ p₂
        eqₚ = cong₂≅ (λ t₁′ t₂′ → proj₂ t₁′ NNF.⌜$⌝ proj₂ t₂′)
                (≡→≅ (idNNF⇄⋙ (t₁ , p₁))) (≡→≅ (idNF⇄⋘ (t₂ , p₂)))
      in
        begin
          proj₁ (⋙→NNF (NNF→⋙ (t₁ , p₁))) ⌜$⌝ proj₁ (⋘→NF (NF→⋘ (t₂ , p₂))) ,
          proj₂ (⋙→NNF (NNF→⋙ (t₁ , p₁))) ⌜$⌝ proj₂ (⋘→NF (NF→⋘ (t₂ , p₂)))
        ≡⟨ ≅→≡ (cong₂≅ _,_ (≡→≅ eqₜ) eqₚ) ⟩
          t₁ ⌜$⌝ t₂ , p₁ ⌜$⌝ p₂
        ∎

⋘≃NF : ∀ {Γ A} → (Γ ⋘ A) ≃ (Σ (Γ ⊢ A) NF)
⋘≃NF = record
  { to      = ⋘→NF
  ; from    = NF→⋘
  ; from∘to = id⋘⇄NF
  ; to∘from = idNF⇄⋘
  }

⋙≃NNF : ∀ {Γ A} → (Γ ⋙ A) ≃ (Σ (Γ ⊢ A) NNF)
⋙≃NNF = record
  { to      = ⋙→NNF
  ; from    = NNF→⋙
  ; from∘to = id⋙⇄NNF
  ; to∘from = idNNF⇄⋙
  }


----------------------------------------------------------------------------------------------------

-- definitional equality
infix 4 _≝_
data _≝_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  refl≝  : ∀ {A} {t : Γ ⊢ A} → t ≝ t
  sym≝   : ∀ {A} {t t′ : Γ ⊢ A} (eq : t ≝ t′) → t′ ≝ t
  trans≝ : ∀ {A} {t t′ t″ : Γ ⊢ A} (eq : t ≝ t′) (eq′ : t′ ≝ t″) → t ≝ t″
  cong$  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (eq₁ : t₁ ≝ t₁′) (eq₂ : t₂ ≝ t₂′) →
           t₁ ⌜$⌝ t₂ ≝ t₁′ ⌜$⌝ t₂′
  βred⊃  : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ]) →
           ⌜λ⌝ t₁ ⌜$⌝ t₂ ≝ t′

open ≝Kit (λ {Γ} {A} {t} → refl≝ {t = t}) sym≝ trans≝ public


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

open ⇒Kit _⇒_ public

mutual
  NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t
  NF→¬R (nnf p) r = r ↯ NNF→¬R p

  NNF→¬R : ∀ {Γ A} {t  : Γ ⊢ A} → NNF t → ¬R t
  NNF→¬R (p₁ ⌜$⌝ p₂) (cong$₁ r₁)     = r₁ ↯ NNF→¬R p₁
  NNF→¬R (p₁ ⌜$⌝ p₂) (cong$₂ p₁′ r₂) = r₂ ↯ NF→¬R p₂

open ¬RKit NF→¬R public


----------------------------------------------------------------------------------------------------

-- alternative progress from decidability of NF
module ProgAlt1 where
  ¬NF→RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ NF t → RF t
  ¬NF→RF {t = ⌜v⌝ i}         ¬p                   = nnf ⌜v⌝- ↯ ¬p
  ¬NF→RF {t = ⌜λ⌝ t}         ¬p                   = ⌜λ⌝- ↯ ¬p
  ¬NF→RF {t = t₁ ⌜$⌝ t₂}     ¬p                   with NNF? t₁ | NF? t₂
  ¬NF→RF {t = _ ⌜$⌝ _}       ¬p | yes p₁ | yes p₂   = nnf (p₁ ⌜$⌝ p₂) ↯ ¬p
  ¬NF→RF {t = _ ⌜$⌝ _}       ¬p | yes p₁ | no ¬p₂   = let _ , r₂ = ¬NF→RF ¬p₂
                                                       in  _ , cong$₂ (nnf p₁) r₂
  ¬NF→RF {t = ⌜v⌝ _ ⌜$⌝ _}   ¬p | no ¬p₁ | _        = ⌜v⌝- ↯ ¬p₁
  ¬NF→RF {t = ⌜λ⌝ _ ⌜$⌝ _}   ¬p | no ¬p₁ | yes p₂   = _ , βred⊃ refl p₂
  ¬NF→RF {t = ⌜λ⌝ _ ⌜$⌝ _}   ¬p | no ¬p₁ | no ¬p₂   = let _ , r₂ = ¬NF→RF ¬p₂
                                                       in  _ , cong$₂ ⌜λ⌝- r₂
  ¬NF→RF {t = _ ⌜$⌝ _ ⌜$⌝ _} ¬p | no ¬p₁ | _        = let _ , r₁ = ¬NF→RF λ { (nnf p₁) → p₁ ↯ ¬p₁ }
                                                       in  _ , cong$₁ r₁

  open NF?Kit NF? ¬NF→RF

-- alternative progress from decidability of RF
module ProgAlt2 where
  ¬R→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬R t → NF t
  ¬R→NF {t = ⌜v⌝ i}         ¬r               = nnf ⌜v⌝-
  ¬R→NF {t = ⌜λ⌝ t}         ¬r               = ⌜λ⌝-
  ¬R→NF {t = ⌜v⌝ _ ⌜$⌝ _}   ¬r               with ¬R→NF λ r₂ → cong$₂ (nnf ⌜v⌝-) r₂ ↯ ¬r
  ¬R→NF {t = ⌜v⌝ _ ⌜$⌝ _}   ¬r | p₂            = nnf (⌜v⌝- ⌜$⌝ p₂)
  ¬R→NF {t = ⌜λ⌝ _ ⌜$⌝ _}   ¬r               with ¬R→NF λ r₂ → cong$₂ ⌜λ⌝- r₂ ↯ ¬r
  ¬R→NF {t = ⌜λ⌝ _ ⌜$⌝ _}   ¬r | p₂            = βred⊃ refl p₂ ↯ ¬r
  ¬R→NF {t = _ ⌜$⌝ _ ⌜$⌝ _} ¬r               with ¬R→NF λ r₁ → cong$₁ r₁ ↯ ¬r
  ¬R→NF {t = _ ⌜$⌝ _ ⌜$⌝ _} ¬r | nnf p₁        with ¬R→NF λ r₁ → cong$₂ (nnf p₁) r₁ ↯ ¬r
  ¬R→NF {t = _ ⌜$⌝ _ ⌜$⌝ _} ¬r | nnf p₁ | p₂     = nnf (p₁ ⌜$⌝ p₂)

  ¬RF→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → NF t
  ¬RF→NF = ¬R→NF ∘ ¬RF→¬R

  RF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (RF t)
  RF? (⌜v⌝ i)                                       = no λ ()
  RF? (⌜λ⌝ t)                                       = no λ ()
  RF? (t₁ ⌜$⌝ t₂)                                   with RF? t₁ | RF? t₂
  RF? (_ ⌜$⌝ _)       | no ¬p₁       | yes (_ , r₂)   = yes (_ , cong$₂ (¬RF→NF ¬p₁) r₂)
  RF? (⌜v⌝ _ ⌜$⌝ _)   | no ¬p₁       | no ¬p₂         = no λ { (_ , cong$₂ p₁ r₂) → r₂ ↯ ¬RF→¬R ¬p₂ }
  RF? (⌜λ⌝ _ ⌜$⌝ _)   | no ¬p₁       | no ¬p₂         = yes (_ , βred⊃ refl (¬RF→NF ¬p₂))
  RF? (_ ⌜$⌝ _ ⌜$⌝ _) | no ¬p₁       | no ¬p₂         = no λ { (_ , cong$₁ r₁) → r₁ ↯ ¬RF→¬R ¬p₁
                                                           ; (_ , cong$₂ p₁ r₂) → r₂ ↯ ¬RF→¬R ¬p₂
                                                           }
  RF? (_ ⌜$⌝ _ ⌜$⌝ _) | yes (_ , r₁) | _              = yes (_ , cong$₁ r₁)

  open RF?Kit RF? ¬RF→NF hiding (¬R→NF)

-- progress, with decidability of NF and RF as corollaries
prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
prog⇒ (⌜v⌝ i)                = done (nnf ⌜v⌝-)
prog⇒ (⌜λ⌝ t)                = done ⌜λ⌝-
prog⇒ (t₁ ⌜$⌝ t₂)            with prog⇒ t₁ | prog⇒ t₂
... | step r₁       | _         = step (cong$₁ r₁)
... | done p₁       | step r₂   = step (cong$₂ p₁ r₂)
... | done ⌜λ⌝-     | done p₂   = step (βred⊃ refl p₂)
... | done (nnf p₁) | done p₂   = done (nnf (p₁ ⌜$⌝ p₂))

open ProgKit prog⇒ public hiding (NF?)

module _ (⚠ : Extensionality) where
  uni¬RF : ∀ {Γ A} {t : Γ ⊢ A} (¬p ¬p′ : ¬ RF t) → ¬p ≡ ¬p′
  uni¬RF = uni→ ⚠ uni𝟘

  NF≃¬RF : ∀ {Γ A} {t : Γ ⊢ A} → NF t ≃ (¬ RF t)
  NF≃¬RF = record
    { to      = NF→¬RF
    ; from    = ¬RF→NF
    ; from∘to = λ p → uniNF _ p
    ; to∘from = λ p → uni¬RF _ p
    }


----------------------------------------------------------------------------------------------------

-- determinism
det⇒ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒ t″ → t′ ≡ t″
det⇒ (cong$₁ r₁)     (cong$₁ r₁′)     = (_⌜$⌝ _) & det⇒ r₁ r₁′
det⇒ (cong$₁ r₁)     (cong$₂ p₁′ r₂′) = r₁ ↯ NF→¬R p₁′
det⇒ (cong$₂ p₁ r₂)  (cong$₁ r₁′)     = r₁′ ↯ NF→¬R p₁
det⇒ (cong$₂ p₁ r₂)  (cong$₂ p₁′ r₂′) = (_ ⌜$⌝_) & det⇒ r₂ r₂′
det⇒ (cong$₂ p₁ r₂)  (βred⊃ refl p₂′) = r₂ ↯ NF→¬R p₂′
det⇒ (βred⊃ refl p₂) (cong$₂ p₁′ r₂′) = r₂′ ↯ NF→¬R p₂
det⇒ (βred⊃ refl p₂) (βred⊃ refl p₂′) = refl

-- uniqueness of proofs
uni⇒ : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒ t′) → r ≡ r′
uni⇒ (cong$₁ r₁)     (cong$₁ r₁′)     = cong$₁ & uni⇒ r₁ r₁′
uni⇒ (cong$₁ r₁)     (cong$₂ p₁′ r₂′) = r₁ ↯ NF→¬R p₁′
uni⇒ (cong$₂ p₁ r₂)  (cong$₁ r₁′)     = r₁′ ↯ NF→¬R p₁
uni⇒ (cong$₂ p₁ r₂)  (cong$₂ p₁′ r₂′) = cong$₂ & uniNF p₁ p₁′ ⊗ uni⇒ r₂ r₂′
uni⇒ (cong$₂ p₁ r₂)  (βred⊃ eq′ p₂′)  = r₂ ↯ NF→¬R p₂′
uni⇒ (βred⊃ eq p₂)   (cong$₂ p₁′ r₂′) = r₂′ ↯ NF→¬R p₂
uni⇒ (βred⊃ refl p₂) (βred⊃ refl p₂′) = βred⊃ refl & uniNF p₂ p₂′

open ⇒*Kit NF→¬R det⇒ uni⇒ public


----------------------------------------------------------------------------------------------------
