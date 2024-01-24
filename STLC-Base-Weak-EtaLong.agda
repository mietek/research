module STLC-Base-Weak-EtaLong where

open import STLC-Base public
open import Isomorphism public
open import STLC-Base-Weak-NotEtaLong
  using (⌜λ⌝ ; nnf ; ⌜v⌝ ; _⌜$⌝_ ; module ProgAlt1)
  renaming
    ( NF to CNF
    ; NNF to CNNF
    ; renNF to renCNF
    ; renNNF to renCNNF
    ; uniNF to uniCNF
    ; uniNNF to uniCNNF
    )

-- TODO: how to define a notion of normal form that corresponds to ⇒C-irreducibility?
-- ⟹C is "guaranteed not to be a top-level eta-expansion"
-- so the notion is going to be some thing like, beta-short eta-long *except* at the very top?


----------------------------------------------------------------------------------------------------

-- -- β-short not-η-long weak normal forms (extrinsic)
-- mutual
--   data NF {Γ} : ∀ {A} → Γ ⊢ A → Set where
--     ⌜λ⌝ : ∀ {A B} {t : A ∷ Γ ⊢ B} → NF (⌜λ⌝ t)
--     nnf : ∀ {A} {t : Γ ⊢ A} (p : NNF t) → NF t
--
--   -- neutrals
--   data NNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
--     ⌜v⌝   : ∀ {A} {i : Γ ∋ A} → NNF (⌜v⌝ i)
--     _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : NNF t₁) (p₂ : NF t₂) → NNF (t₁ ⌜$⌝ t₂)
--
-- -- renaming
-- mutual
--   renNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NF t → NF (ren e t)
--   renNF e ⌜λ⌝     = ⌜λ⌝
--   renNF e (nnf p) = nnf (renNNF e p)
--
--   renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → NNF t → NNF (ren e t)
--   renNNF e ⌜v⌝         = ⌜v⌝
--   renNNF e (p₁ ⌜$⌝ p₂) = renNNF e p₁ ⌜$⌝ renNF e p₂
--
-- -- uniqueness of proofs
-- mutual
--   uniNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NF t) → p ≡ p′
--   uniNF ⌜λ⌝     ⌜λ⌝      = refl
--   uniNF (nnf p) (nnf p′) = nnf & uniNNF p p′
--
--   uniNNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : NNF t) → p ≡ p′
--   uniNNF ⌜v⌝         ⌜v⌝           = refl
--   uniNNF (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniNNF p₁ p₁′ ⊗ uniNF p₂ p₂′


----------------------------------------------------------------------------------------------------

-- β-short η-long (expanded; “E-irreducible”) weak normal forms (extrinsic)
mutual
  data ENF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜λ⌝ : ∀ {A B} {t : A ∷ Γ ⊢ B} → ENF (⌜λ⌝ t)
    nnf : ∀ {t : Γ ⊢ ⌜◦⌝} (p : ENNF t) → ENF t

  -- neutrals
  data ENNF {Γ} : ∀ {A} → Γ ⊢ A → Set where
    ⌜v⌝   : ∀ {A} {i : Γ ∋ A} → ENNF (⌜v⌝ i)
    _⌜$⌝_ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (p₁ : ENNF t₁) (p₂ : ENF t₂) → ENNF (t₁ ⌜$⌝ t₂)

-- expandability
data Exp {Γ} : ∀ {A} → Γ ⊢ A → Set where
  ⌜v⌝   : ∀ {A B} {i : Γ ∋ A ⌜⊃⌝ B} → Exp (⌜v⌝ i)
  _⌜$⌝_ : ∀ {A B C} {t₁ : Γ ⊢ A ⌜⊃⌝ B ⌜⊃⌝ C} {t₂ : Γ ⊢ A} → Exp (t₁ ⌜$⌝ t₂)

ENF→¬Exp : ∀ {Γ A} {t : Γ ⊢ A} → ENF t → ¬ Exp t
ENF→¬Exp ⌜λ⌝     ()
ENF→¬Exp (nnf p) ()

-- renaming
mutual
  renENF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → ENF t → ENF (ren e t)
  renENF e ⌜λ⌝     = ⌜λ⌝
  renENF e (nnf p) = nnf (renENNF e p)

  renENNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (e : Γ ⊆ Γ′) → ENNF t → ENNF (ren e t)
  renENNF e ⌜v⌝         = ⌜v⌝
  renENNF e (p₁ ⌜$⌝ p₂) = renENNF e p₁ ⌜$⌝ renENF e p₂

-- uniqueness of proofs
mutual
  uniENF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : ENF t) → p ≡ p′
  uniENF ⌜λ⌝     ⌜λ⌝      = refl
  uniENF (nnf p) (nnf p′) = nnf & uniENNF p p′

  uniENNF : ∀ {Γ A} {t : Γ ⊢ A} (p p′ : ENNF t) → p ≡ p′
  uniENNF ⌜v⌝         ⌜v⌝           = refl
  uniENNF (p₁ ⌜$⌝ p₂) (p₁′ ⌜$⌝ p₂′) = _⌜$⌝_ & uniENNF p₁ p₁′ ⊗ uniENF p₂ p₂′

uniExp : ∀ {Γ A} {t : Γ ⊢ A} (x x′ : Exp t) → x ≡ x′
uniExp ⌜v⌝   ⌜v⌝   = refl
uniExp _⌜$⌝_ _⌜$⌝_ = refl


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
  ηexp⊃  : ∀ {A B} {t t′ : Γ ⊢ A ⌜⊃⌝ B} (eq : t′ ≡ ⌜λ⌝ (weak t ⌜$⌝ ⌜v⌝ zero)) → t ≝ t′

open ≝Kit (λ {_} {_} {t} → refl≝ {t = t}) sym≝ trans≝ public


----------------------------------------------------------------------------------------------------

-- call-by-value restricted expansionary reduction (Ghani p.51, table 3-4)
-- NOTE: _⇒F_ renamed to _⇒E_ for expansion; _⇒I_ renamed to _⇒C_ for contraction
-- there were too many Fs already; also C goes before E!
mutual
  infix 4 _⇒C_
  data _⇒C_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    cong$₁  : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⌜⊃⌝ B} {t₂ : Γ ⊢ A} (r : t₁ ⇒C t₁′) →
              t₁ ⌜$⌝ t₂ ⇒C t₁′ ⌜$⌝ t₂
    Ccong$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : CNF t₁) (r₂ : t₂ ⇒C t₂′) →
              t₁ ⌜$⌝ t₂ ⇒C t₁ ⌜$⌝ t₂′
    Econg$₂ : ∀ {A B} {t₁ : Γ ⊢ A ⌜⊃⌝ B} {t₂ t₂′ : Γ ⊢ A} (p₁ : ENF t₁) (r₂ : t₂ ⇒E t₂′) →
              t₁ ⌜$⌝ t₂ ⇒C t₁ ⌜$⌝ t₂′
    βred⊃   : ∀ {A B} {t₁ : A ∷ Γ ⊢ B} {t₂ : Γ ⊢ A} {t′ : Γ ⊢ B} (eq : t′ ≡ t₁ [ t₂ ])
                (p₂ : CNF t₂) →
              ⌜λ⌝ t₁ ⌜$⌝ t₂ ⇒C t′

  infix 4 _⇒E_
  data _⇒E_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
    Cred  : ∀ {A} {t t′ : Γ ⊢ A} (r : t ⇒C t′) → t ⇒E t′
    ηexp⊃ : ∀ {A B} {t t′ : Γ ⊢ A ⌜⊃⌝ B} (eq : t′ ≡ ⌜λ⌝ (weak t ⌜$⌝ ⌜v⌝ zero)) (x : Exp t) →
            t ⇒E t′

module C = ⇒Kit _⇒C_
module E = ⇒Kit _⇒E_

mutual
  CNF→¬CR : ∀ {Γ A} {t : Γ ⊢ A} → CNF t → C.¬R t
  CNF→¬CR (nnf p) r = r ↯ CNNF→¬CR p

  CNNF→¬CR : ∀ {Γ A} {t : Γ ⊢ A} → CNNF t → C.¬R t
  CNNF→¬CR (p₁ ⌜$⌝ p₂) (cong$₁ r₁)                  = r₁ ↯ CNNF→¬CR p₁
  CNNF→¬CR (p₁ ⌜$⌝ p₂) (Ccong$₂ p₁′ r₂)             = r₂ ↯ CNF→¬CR p₂
  CNNF→¬CR (p₁ ⌜$⌝ p₂) (Econg$₂ p₁′ (Cred r₂))      = r₂ ↯ CNF→¬CR p₂
  CNNF→¬CR (() ⌜$⌝ p₂) (Econg$₂ ⌜λ⌝ (ηexp⊃ refl x))

mutual
  ENF→¬CR : ∀ {Γ A} {t : Γ ⊢ A} → ENF t → C.¬R t
  ENF→¬CR (nnf p) r = r ↯ ENNF→¬CR p

  ENNF→¬CR : ∀ {Γ A} {t : Γ ⊢ A} → ENNF t → C.¬R t
  ENNF→¬CR (p₁ ⌜$⌝ p₂) (cong$₁ r₁)      = r₁ ↯ ENNF→¬CR p₁
  ENNF→¬CR (p₁ ⌜$⌝ p₂) (Ccong$₂ p₁′ r₂) = r₂ ↯ ENF→¬CR p₂
  ENNF→¬CR (p₁ ⌜$⌝ p₂) (Econg$₂ p₁′ r₂) = r₂ ↯ ENF→¬ER p₂

  ENF→¬ER : ∀ {Γ A} {t : Γ ⊢ A} → ENF t → E.¬R t
  ENF→¬ER ⌜λ⌝     (ηexp⊃ refl ())
  ENF→¬ER (nnf p) r               = r ↯ ENNF→¬ER p

  ENNF→¬ER : ∀ {Γ} {t : Γ ⊢ ⌜◦⌝} → ENNF t → E.¬R t
  ENNF→¬ER p (Cred r) = r ↯ ENNF→¬CR p

module C′ = C.¬RKit CNF→¬CR
module E′ = E.¬RKit ENF→¬ER

-- uniqueness of proofs
module _ (⚠ : Extensionality) where
  uni¬CRF : ∀ {Γ A} {t : Γ ⊢ A} (¬p ¬p′ : ¬ C.RF t) → ¬p ≡ ¬p′
  uni¬CRF = uni→ ⚠ uni𝟘

  uni¬ERF : ∀ {Γ A} {t : Γ ⊢ A} (¬p ¬p′ : ¬ E.RF t) → ¬p ≡ ¬p′
  uni¬ERF = uni→ ⚠ uni𝟘


----------------------------------------------------------------------------------------------------

mutual
  ENF→CNF : ∀ {Γ A} {t : Γ ⊢ A} → ENF t → CNF t
  ENF→CNF ⌜λ⌝     = ⌜λ⌝
  ENF→CNF (nnf p) = nnf (ENNF→CNNF p)

  ENNF→CNNF : ∀ {Γ A} {t : Γ ⊢ A} → ENNF t → CNNF t
  ENNF→CNNF ⌜v⌝         = ⌜v⌝
  ENNF→CNNF (p₁ ⌜$⌝ p₂) = ENNF→CNNF p₁ ⌜$⌝ ENF→CNF p₂

¬ER→¬CR : ∀ {Γ A} {t : Γ ⊢ A} → E.¬R t → C.¬R t
¬ER→¬CR ¬r r = Cred r ↯ ¬r

¬ERF→¬CRF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ E.RF t → ¬ C.RF t
¬ERF→¬CRF ¬p (t′ , r) = (t′ , Cred r) ↯ ¬p


----------------------------------------------------------------------------------------------------

module ProgAlt1C where
  open ProgAlt1 using () renaming (NF? to CNF? ; NNF? to CNNF?)

  ¬CNF→CRF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ CNF t → C.RF t
  ¬CNF→CRF {t = ⌜v⌝ i}         ¬p                   = nnf ⌜v⌝ ↯ ¬p
  ¬CNF→CRF {t = ⌜λ⌝ t}         ¬p                   = ⌜λ⌝ ↯ ¬p
  ¬CNF→CRF {t = t₁ ⌜$⌝ t₂}     ¬p                   with CNNF? t₁ | CNF? t₂
  ¬CNF→CRF {t = _ ⌜$⌝ _}       ¬p | yes p₁ | yes p₂   = nnf (p₁ ⌜$⌝ p₂) ↯ ¬p
  ¬CNF→CRF {t = _ ⌜$⌝ _}       ¬p | yes p₁ | no ¬p₂   = let _ , r₂ = ¬CNF→CRF ¬p₂ in _ , Ccong$₂ (nnf p₁) r₂
  ¬CNF→CRF {t = ⌜v⌝ _ ⌜$⌝ _}   ¬p | no ¬p₁ | _        = ⌜v⌝ ↯ ¬p₁
  ¬CNF→CRF {t = ⌜λ⌝ _ ⌜$⌝ _}   ¬p | no ¬p₁ | yes p₂   = _ , βred⊃ refl p₂
  ¬CNF→CRF {t = ⌜λ⌝ _ ⌜$⌝ _}   ¬p | no ¬p₁ | no ¬p₂   = let _ , r₂ = ¬CNF→CRF ¬p₂ in _ , Ccong$₂ ⌜λ⌝ r₂
  ¬CNF→CRF {t = _ ⌜$⌝ _ ⌜$⌝ _} ¬p | no ¬p₁ | _        = let _ , r₁ = ¬CNF→CRF λ { (nnf p₁) → p₁ ↯ ¬p₁ } in _ , cong$₁ r₁

  open C′.NF?Kit CNF? ¬CNF→CRF using () renaming (prog⇒ to prog⇒C)

module ProgAlt2C where
  ¬CR→CNF : ∀ {Γ A} {t : Γ ⊢ A} → C.¬R t → CNF t
  ¬CR→CNF {t = ⌜v⌝ i}         ¬r               = nnf ⌜v⌝
  ¬CR→CNF {t = ⌜λ⌝ t}         ¬r               = ⌜λ⌝
  ¬CR→CNF {t = ⌜v⌝ _ ⌜$⌝ _}   ¬r               with ¬CR→CNF λ r₂ → Ccong$₂ (nnf ⌜v⌝) r₂ ↯ ¬r
  ¬CR→CNF {t = ⌜v⌝ _ ⌜$⌝ _}   ¬r | p₂            = nnf (⌜v⌝ ⌜$⌝ p₂)
  ¬CR→CNF {t = ⌜λ⌝ _ ⌜$⌝ _}   ¬r               with ¬CR→CNF λ r₂ → Ccong$₂ ⌜λ⌝ r₂ ↯ ¬r
  ¬CR→CNF {t = ⌜λ⌝ _ ⌜$⌝ _}   ¬r | p₂            = βred⊃ refl p₂ ↯ ¬r
  ¬CR→CNF {t = _ ⌜$⌝ _ ⌜$⌝ _} ¬r               with ¬CR→CNF λ r₁ → cong$₁ r₁ ↯ ¬r
  ¬CR→CNF {t = _ ⌜$⌝ _ ⌜$⌝ _} ¬r | nnf p₁        with ¬CR→CNF λ r₁ → Ccong$₂ (nnf p₁) r₁ ↯ ¬r
  ¬CR→CNF {t = _ ⌜$⌝ _ ⌜$⌝ _} ¬r | nnf p₁ | p₂     = nnf (p₁ ⌜$⌝ p₂)

  ¬CRF→CNF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ C.RF t → CNF t
  ¬CRF→CNF = ¬CR→CNF ∘ C′.¬RF→¬R

  CRF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (C.RF t)
  CRF? (⌜v⌝ i)                                       = no λ ()
  CRF? (⌜λ⌝ t)                                       = no λ ()
  CRF? (t₁ ⌜$⌝ t₂)                                   with CRF? t₁ | CRF? t₂
  CRF? (_ ⌜$⌝ _)       | no ¬p₁       | yes (_ , r₂)   = yes (_ , Ccong$₂ (¬CRF→CNF ¬p₁) r₂)
  CRF? (⌜v⌝ _ ⌜$⌝ _)   | no ¬p₁       | no ¬p₂         = no λ { (_ , Ccong$₂ p₁ r₂) → r₂ ↯ C′.¬RF→¬R ¬p₂ }
  CRF? (⌜λ⌝ _ ⌜$⌝ _)   | no ¬p₁       | no ¬p₂         = yes (_ , βred⊃ refl (¬CRF→CNF ¬p₂))
  CRF? (_ ⌜$⌝ _ ⌜$⌝ _) | no ¬p₁       | no ¬p₂         = no λ { (_ , cong$₁ r₁) → r₁ ↯ C′.¬RF→¬R ¬p₁
                                                            ; (_ , Ccong$₂ p₁ r₂) → r₂ ↯ C′.¬RF→¬R ¬p₂
                                                            }
  CRF? (_ ⌜$⌝ _ ⌜$⌝ _) | yes (_ , r₁) | _              = yes (_ , cong$₁ r₁)

  open C′.RF?Kit CRF? ¬CRF→CNF using () renaming (prog⇒ to prog⇒C)

prog⇒C : ∀ {Γ A} (t : Γ ⊢ A) → C′.Prog t
prog⇒C (⌜v⌝ i)                     = C′.done (nnf ⌜v⌝)
prog⇒C (⌜λ⌝ t)                     = C′.done ⌜λ⌝
prog⇒C (t₁ ⌜$⌝ t₂)                 with prog⇒C t₁ | prog⇒C t₂
... | C′.step r₁       | _            = C′.step (cong$₁ r₁)
... | C′.done p₁       | C′.step r₂   = C′.step (Ccong$₂ p₁ r₂)
... | C′.done ⌜λ⌝      | C′.done p₂   = C′.step (βred⊃ refl p₂)
... | C′.done (nnf p₁) | C′.done p₂   = C′.done (nnf (p₁ ⌜$⌝ p₂))

module C″ = C′.ProgKit prog⇒C

module _ (⚠ : Extensionality) where
  CNF≃¬CRF : ∀ {Γ A} {t : Γ ⊢ A} → CNF t ≃ (¬ C.RF t)
  CNF≃¬CRF = record
    { to      = C′.NF→¬RF
    ; from    = C″.¬RF→NF
    ; from∘to = λ p → uniCNF _ p
    ; to∘from = λ p → uni¬CRF ⚠ _ p
    }


----------------------------------------------------------------------------------------------------

module ProgAlt1E where
  mutual
    ENF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (ENF t)
    ENF? {A = ⌜◦⌝}     (⌜v⌝ i)     = yes (nnf ⌜v⌝)
    ENF? {A = ⌜◦⌝}     (t₁ ⌜$⌝ t₂) with ENNF? t₁ | ENF? t₂
    ... | yes p₁ | yes p₂            = yes (nnf (p₁ ⌜$⌝ p₂))
    ... | yes p₁ | no ¬p₂            = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₂ ↯ ¬p₂ }
    ... | no ¬p₁ | _                 = no λ { (nnf (p₁ ⌜$⌝ p₂)) → p₁ ↯ ¬p₁ }
    ENF? {A = _ ⌜⊃⌝ _} (⌜v⌝ i)     = no λ ()
    ENF? {A = _ ⌜⊃⌝ _} (⌜λ⌝ t)     = yes ⌜λ⌝
    ENF? {A = _ ⌜⊃⌝ _} (t₁ ⌜$⌝ t₂) = no λ ()

    ENNF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (ENNF t)
    ENNF? (⌜v⌝ i)         = yes ⌜v⌝
    ENNF? (⌜λ⌝ t)         = no λ ()
    ENNF? (t₁ ⌜$⌝ t₂)     with ENNF? t₁ | ENF? t₂
    ... | yes p₁ | yes p₂   = yes (p₁ ⌜$⌝ p₂)
    ... | yes p₁ | no ¬p₂   = no λ { (p₁ ⌜$⌝ p₂) → p₂ ↯ ¬p₂ }
    ... | no ¬p₁ | _        = no λ { (p₁ ⌜$⌝ p₂) → p₁ ↯ ¬p₁ }

--  ¬ENF→ERF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ ENF t → E.RF t
--  ¬ENF→ERF {A = ⌜◦⌝}     {⌜v⌝ i}               ¬p                                        = nnf ⌜v⌝ ↯ ¬p
--  ¬ENF→ERF {A = ⌜◦⌝}     {t₁ ⌜$⌝ t₂}           ¬p                                        with ENNF? t₁ | ENF? t₂
--  ¬ENF→ERF {A = ⌜◦⌝}     {t₁ ⌜$⌝ t₂}           ¬p | yes p₁ | yes p₂                        = nnf (p₁ ⌜$⌝ p₂) ↯ ¬p
--  ¬ENF→ERF {A = ⌜◦⌝}     {t₁ ⌜$⌝ t₂}           ¬p | yes p₁ | no ¬p₂                        = let _ , r₂ = ¬ENF→ERF {t = t₂} ¬p₂ in _ , Cred (Econg$₂ {!nnf p₁!} r₂)
--  ¬ENF→ERF {A = ⌜◦⌝}     {⌜v⌝ i ⌜$⌝ t₂}        ¬p | no ¬p₁ | _                             = ⌜v⌝ ↯ ¬p₁
--  ¬ENF→ERF {A = ⌜◦⌝}     {⌜λ⌝ t₁ ⌜$⌝ t₂}       ¬p | no ¬p₁ | yes p₂                        = _ , Cred (βred⊃ refl (ENF→CNF p₂))
--  ¬ENF→ERF {A = ⌜◦⌝}     {⌜λ⌝ t₁ ⌜$⌝ t₂}       ¬p | no ¬p₁ | no ¬p₂                        = let _ , r₂ = ¬ENF→ERF ¬p₂ in _ , Cred (Econg$₂ ⌜λ⌝ r₂)
--  ¬ENF→ERF {A = ⌜◦⌝}     {t₁@(_ ⌜$⌝ _) ⌜$⌝ t₂} ¬p | no ¬p₁ | _                             with ¬ENF→ERF {t = t₁} λ ()
--  ¬ENF→ERF {A = ⌜◦⌝}     {t₁@(_ ⌜$⌝ _) ⌜$⌝ t₂} ¬p | no ¬p₁ | _      | t₁′ , Cred r₁          = _ , Cred (cong$₁ r₁)
--  ¬ENF→ERF {A = ⌜◦⌝}     {t₁@(_ ⌜$⌝ _) ⌜$⌝ t₂} ¬p | no ¬p₁ | _      | t₁′ , ηexp⊃ refl x     = {!!}
--  ¬ENF→ERF {A = _ ⌜⊃⌝ _} {⌜v⌝ i}               ¬p                                        = _ , ηexp⊃ refl ⌜v⌝
--  ¬ENF→ERF {A = _ ⌜⊃⌝ _} {⌜λ⌝ t}               ¬p                                        = ⌜λ⌝ ↯ ¬p
--  ¬ENF→ERF {A = _ ⌜⊃⌝ _} {t₁ ⌜$⌝ t₂}           ¬p                                        = _ , ηexp⊃ refl _⌜$⌝_
--
--  open E′.NF?Kit ENF? ¬ENF→ERF using () renaming (prog⇒ to prog⇒E)

--module ProgAlt2E where
--  ¬ER→ENF : ∀ {Γ A} {t : Γ ⊢ A} → E.¬R t → ENF t
--  ¬ER→ENF {A = ⌜◦⌝}     {⌜v⌝ i}               ¬r = nnf ⌜v⌝
--  ¬ER→ENF {A = ⌜◦⌝}     {⌜v⌝ _ ⌜$⌝ t₂}        ¬r with ¬ER→ENF {t = t₂} λ r₂ → Cred (Econg$₂ {!nnf ⌜v⌝!} r₂) ↯ ¬r
--  ... | p₂                                          = nnf (⌜v⌝ ⌜$⌝ p₂)
--  ¬ER→ENF {A = ⌜◦⌝}     {⌜λ⌝ _ ⌜$⌝ t₂}        ¬r with ¬ER→ENF {t = t₂} λ r₂ → Cred (Econg$₂ ⌜λ⌝ r₂) ↯ ¬r
--  ... | p₂                                          = Cred (βred⊃ refl (ENF→CNF p₂)) ↯ ¬r
--  ¬ER→ENF {A = ⌜◦⌝}     {t₁@(_ ⌜$⌝ _) ⌜$⌝ t₂} ¬r with ¬ER→ENF {t = t₁} λ { (Cred r) → Cred (cong$₁ r) ↯ ¬r
--                                                                           ; (ηexp⊃ refl x) → {!!} ↯ ¬r
--                                                                           }
--  ¬ER→ENF {A = ⌜◦⌝}     {t₁@(_ ⌜$⌝ _) ⌜$⌝ t₂} ¬r | ()
--  ¬ER→ENF {A = _ ⌜⊃⌝ _} {⌜v⌝ i}               ¬r = ηexp⊃ refl ⌜v⌝ ↯ ¬r
--  ¬ER→ENF {A = _ ⌜⊃⌝ _} {⌜λ⌝ t}               ¬r = ⌜λ⌝
--  ¬ER→ENF {A = _ ⌜⊃⌝ _} {⌜v⌝ _ ⌜$⌝ t₂}        ¬r with ¬ER→ENF {t = t₂} λ r₂ → Cred (Econg$₂ {!nnf ⌜v⌝!} r₂) ↯ ¬r
--  ... | p₂                                          = {!nnf (⌜v⌝ ⌜$⌝ p₂)!}
--  ¬ER→ENF {A = _ ⌜⊃⌝ _} {⌜λ⌝ _ ⌜$⌝ t₂}        ¬r with ¬ER→ENF {t = t₂} λ r₂ → Cred (Econg$₂ ⌜λ⌝ r₂) ↯ ¬r
--  ... | p₂                                          = Cred (βred⊃ refl (ENF→CNF p₂)) ↯ ¬r
--  ¬ER→ENF {A = _ ⌜⊃⌝ _} {t₁@(_ ⌜$⌝ _) ⌜$⌝ t₂} ¬r with ¬ER→ENF {t = t₁} λ { (Cred r) → Cred (cong$₁ r) ↯ ¬r
--                                                                           ; (ηexp⊃ refl x) → {!!} ↯ ¬r
--                                                                           }
--  ¬ER→ENF {A = _ ⌜⊃⌝ _} {t₁@(_ ⌜$⌝ _) ⌜$⌝ t₂} ¬r | ()
--
--  ¬ERF→ENF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ E.RF t → ENF t
--  ¬ERF→ENF = ¬ER→ENF ∘ E′.¬RF→¬R
--
--  open E′.RF?Kit {!!} ¬ERF→ENF using () renaming (prog⇒ to prog⇒E)


prog⇒E : ∀ {Γ A} (t : Γ ⊢ A) → E′.Prog t
prog⇒E {A = ⌜◦⌝}     (⌜v⌝ i)                                   = E′.done (nnf ⌜v⌝)
prog⇒E {A = A ⌜⊃⌝ B} (⌜v⌝ i)                                   = E′.step (ηexp⊃ refl ⌜v⌝)
prog⇒E {A = A ⌜⊃⌝ B} (⌜λ⌝ t)                                   = E′.done ⌜λ⌝
prog⇒E {A = ⌜◦⌝}     (t₁ ⌜$⌝ t₂)                               with prog⇒C t₁ | prog⇒E t₁ | prog⇒E t₂
... | C′.step r₁       | _                         | _            = E′.step (Cred (cong$₁ r₁))
... | C′.done p₁       | E′.step (Cred r₁)         | E′.step r₂   = r₁ ↯ CNF→¬CR p₁
... | C′.done (nnf p₁) | E′.step r₁@(ηexp⊃ refl x) | E′.step r₂   = {!!}
... | C′.done p₁       | E′.done p₁′               | E′.step r₂   = E′.step (Cred (Econg$₂ p₁′ r₂))
... | C′.done ⌜λ⌝      | _                         | E′.done p₂   = E′.step (Cred (βred⊃ refl (ENF→CNF p₂)))
... | C′.done (nnf p₁) | E′.step (Cred r₁)         | E′.done p₂   = r₁ ↯ CNNF→¬CR p₁
... | C′.done (nnf p₁) | E′.step r₁@(ηexp⊃ refl x) | E′.done p₂   = {!!}
... | C′.done (nnf p₁) | E′.done ⌜λ⌝               | E′.done p₂   = E′.step (Cred (βred⊃ refl (ENF→CNF p₂)))
prog⇒E {A = A ⌜⊃⌝ B} (t₁ ⌜$⌝ t₂)                               = E′.step (ηexp⊃ refl _⌜$⌝_)




-- -- t₁ : ⌜◦⌝ ⌜⊃⌝ ⌜◦⌝ ∷ ⌜◦⌝ ∷ [] ⊢ ⌜◦⌝ ⌜⊃⌝ ⌜◦⌝
-- -- t₁ = ⌜v⌝ zero

-- -- p₁ : ENNF t₁
-- -- p₁ = ⌜v⌝

-- -- t₂ : ⌜◦⌝ ⌜⊃⌝ ⌜◦⌝ ∷ ⌜◦⌝ ∷ [] ⊢ ⌜◦⌝
-- -- t₂ = ⌜λ⌝ (⌜v⌝ zero) ⌜$⌝ (⌜v⌝ (suc zero))

-- -- ¬p₂ : ¬ ENF t₂
-- -- ¬p₂ (nnf (() ⌜$⌝ nnf ⌜v⌝))

-- -- t₂′ : ⌜◦⌝ ⌜⊃⌝ ⌜◦⌝ ∷ ⌜◦⌝ ∷ [] ⊢ ⌜◦⌝
-- -- t₂′ = ⌜v⌝ (suc zero)

-- -- p₂ : ENF t₂′
-- -- p₂ = nnf ⌜v⌝

-- -- r₂ : t₂ ⇒E t₂′
-- -- r₂ = Cred (βred⊃ refl (nnf ⌜v⌝))

-- -- t : ⌜◦⌝ ⌜⊃⌝ ⌜◦⌝ ∷ ⌜◦⌝ ∷ [] ⊢ ⌜◦⌝
-- -- t = t₁ ⌜$⌝ t₂

-- -- ¬p : ¬ ENF t
-- -- ¬p (nnf (p₁′ ⌜$⌝ p₂′)) = p₂′ ↯ ¬p₂

-- -- t′ : ⌜◦⌝ ⌜⊃⌝ ⌜◦⌝ ∷ ⌜◦⌝ ∷ [] ⊢ ⌜◦⌝
-- -- t′ = t₁ ⌜$⌝ t₂′

-- -- p′ : ENF t′
-- -- p′ = nnf (p₁ ⌜$⌝ p₂)

-- -- r : t ⇒E t′
-- -- r = Cred (Econg$₂ {!nnf p₁!} r₂)






-- -- -- -- -- -- -- -- determinism?
-- -- -- -- -- -- -- -- TODO: looks unprovable
-- -- -- -- -- -- -- -- mutual
-- -- -- -- -- -- -- --   det⇒C : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒C t′ → t ⇒C t″ → t′ ≡ t″
-- -- -- -- -- -- -- --   det⇒C (cong$₁ r₁)     (cong$₁ r₁′)      = (_⌜$⌝ _) & det⇒C r₁ r₁′
-- -- -- -- -- -- -- --   det⇒C (cong$₁ r₁)     (Ccong$₂ p₁′ r₂′) = r₁ ↯ ENF→¬CR p₁′
-- -- -- -- -- -- -- --   det⇒C (cong$₁ r₁)     (Econg$₂ p₁′ r₂′) = r₁ ↯ ENF→¬CR p₁′
-- -- -- -- -- -- -- --   det⇒C (Ccong$₂ p₁ r₂) (cong$₁ r₁′)      = r₁′ ↯ ENF→¬CR p₁
-- -- -- -- -- -- -- --   det⇒C (Ccong$₂ p₁ r₂) (Ccong$₂ p₁′ r₂′) = (_ ⌜$⌝_) & det⇒C r₂ r₂′
-- -- -- -- -- -- -- --   det⇒C (Ccong$₂ p₁ r₂) (Econg$₂ p₁′ r₂′) = (_ ⌜$⌝_) & det⇒ r₂ r₂′
-- -- -- -- -- -- -- --   det⇒C (Ccong$₂ p₁ r₂) (βred⊃ refl p₂′)  = r₂ ↯ ENF→¬CR p₂′
-- -- -- -- -- -- -- --   det⇒C (Econg$₂ p₁ r₂) (cong$₁ r₁′)      = r₁′ ↯ ENF→¬CR p₁
-- -- -- -- -- -- -- --   det⇒C (Econg$₂ p₁ r₂) (Ccong$₂ p₁′ r₂′) = (_ ⌜$⌝_) & sym (det⇒ r₂′ r₂)
-- -- -- -- -- -- -- --   det⇒C (Econg$₂ p₁ r₂) (Econg$₂ p₁′ r₂′) = (_ ⌜$⌝_) & det⇒E r₂ r₂′
-- -- -- -- -- -- -- --   det⇒C (Econg$₂ p₁ r₂) (βred⊃ refl p₂′)  = r₂ ↯ ENF→¬ER p₂′
-- -- -- -- -- -- -- --   det⇒C (βred⊃ refl p₂) (Ccong$₂ p₁′ r₂′) = r₂′ ↯ ENF→¬CR p₂
-- -- -- -- -- -- -- --   det⇒C (βred⊃ refl p₂) (Econg$₂ p₁′ r₂′) = r₂′ ↯ ENF→¬ER p₂
-- -- -- -- -- -- -- --   det⇒C (βred⊃ refl p₂) (βred⊃ refl p₂′)  = refl
-- -- -- -- -- -- -- --
-- -- -- -- -- -- -- --   det⇒E : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒E t′ → t ⇒E t″ → t′ ≡ t″
-- -- -- -- -- -- -- --   det⇒E (Cred r)       r′              = det⇒ r r′
-- -- -- -- -- -- -- --   det⇒E (ηexp⊃ refl x) (Cred r′)       = {!!}
-- -- -- -- -- -- -- --   det⇒E (ηexp⊃ refl x) (ηexp⊃ refl x′) = refl
-- -- -- -- -- -- -- --
-- -- -- -- -- -- -- --   det⇒ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒C t′ → t ⇒E t″ → t′ ≡ t″
-- -- -- -- -- -- -- --   det⇒ r (Cred r′)      = det⇒C r r′
-- -- -- -- -- -- -- --   det⇒ r (ηexp⊃ eq′ x′) = {!!}

-- -- -- -- -- -- -- -- uniqueness of proofs?
-- -- -- -- -- -- -- -- TODO: looks unprovable
-- -- -- -- -- -- -- -- mutual
-- -- -- -- -- -- -- --   uni⇒C : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒C t′) → r ≡ r′
-- -- -- -- -- -- -- --   uni⇒C (cong$₁ r₁)     (cong$₁ r₁′)      = cong$₁ & uni⇒C r₁ r₁′
-- -- -- -- -- -- -- --   uni⇒C (cong$₁ r₁)     (Ccong$₂ p₁′ r₂′) = r₁ ↯ ENF→¬CR p₁′
-- -- -- -- -- -- -- --   uni⇒C (cong$₁ r₁)     (Econg$₂ p₁′ r₂′) = r₁ ↯ ENF→¬CR p₁′
-- -- -- -- -- -- -- --   uni⇒C (Ccong$₂ p₁ r₂) (cong$₁ r₁′)      = r₁′ ↯ ENF→¬CR p₁
-- -- -- -- -- -- -- --   uni⇒C (Ccong$₂ p₁ r₂) (Ccong$₂ p₁′ r₂′) = Ccong$₂ & uniENF p₁ p₁′ ⊗ uni⇒C r₂ r₂′
-- -- -- -- -- -- -- --   uni⇒C (Ccong$₂ p₁ r₂) (Econg$₂ p₁′ r₂′) = {!!}
-- -- -- -- -- -- -- --   uni⇒C (Ccong$₂ p₁ r₂) (βred⊃ eq′ p₂′)   = r₂ ↯ ENF→¬CR p₂′
-- -- -- -- -- -- -- --   uni⇒C (Econg$₂ p₁ r₂) (cong$₁ r₁′)      = r₁′ ↯ ENF→¬CR p₁
-- -- -- -- -- -- -- --   uni⇒C (Econg$₂ p₁ r₂) (Ccong$₂ p₁′ r₂′) = {!!}
-- -- -- -- -- -- -- --   uni⇒C (Econg$₂ p₁ r₂) (Econg$₂ p₁′ r₂′) = Econg$₂ & uniENF p₁ p₁′ ⊗ uni⇒E r₂ r₂′
-- -- -- -- -- -- -- --   uni⇒C (Econg$₂ p₁ r₂) (βred⊃ eq′ p₂′)   = r₂ ↯ ENF→¬ER p₂′
-- -- -- -- -- -- -- --   uni⇒C (βred⊃ eq p₂)   (Ccong$₂ p₁′ r₂′) = r₂′ ↯ ENF→¬CR p₂
-- -- -- -- -- -- -- --   uni⇒C (βred⊃ eq p₂)   (Econg$₂ p₁′ r₂′) = r₂′ ↯ ENF→¬ER p₂
-- -- -- -- -- -- -- --   uni⇒C (βred⊃ refl p₂) (βred⊃ refl p₂′)  = βred⊃ refl & uniENF p₂ p₂′
-- -- -- -- -- -- -- --
-- -- -- -- -- -- -- --   uni⇒E : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒E t′) → r ≡ r′
-- -- -- -- -- -- -- --   uni⇒E (Cred r)       (Cred r′)       = Cred & uni⇒C r r′
-- -- -- -- -- -- -- --   uni⇒E (Cred r)       (ηexp⊃ eq′ x′)  = {!!}
-- -- -- -- -- -- -- --   uni⇒E (ηexp⊃ eq x)   (Cred r′)       = {!!}
-- -- -- -- -- -- -- --   uni⇒E (ηexp⊃ refl x) (ηexp⊃ refl x′) = ηexp⊃ refl & uniExp x x′


-- -- -- -- -- -- -- ----------------------------------------------------------------------------------------------------

-- -- -- -- -- -- -- Cred* : ∀ {Γ A} {t t′ : Γ ⊢ A} → t C.⇒* t′ → t E.⇒* t′
-- -- -- -- -- -- -- Cred* C.done        = E.done
-- -- -- -- -- -- -- Cred* (C.step r rs) = E.step (Cred r) (Cred* rs)

-- -- -- -- -- -- -- -- Ghani p.51, lemma 3.3.0 (unnumbered)
-- -- -- -- -- -- -- Lem330 : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
-- -- -- -- -- -- -- Lem330 {A = A} t t′ = t ⇒C t′
-- -- -- -- -- -- --                     ⊎ Σ (Ty × Ty) λ { (A′ , B′) →
-- -- -- -- -- -- --                         Σ (A ≡ A′ ⌜⊃⌝ B′) λ { refl →
-- -- -- -- -- -- --                           t′ ≡ ⌜λ⌝ (weak t ⌜$⌝ ⌜v⌝ zero) × Exp t } }

-- -- -- -- -- -- -- ER→lem330 : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒E t′ → Lem330 t t′
-- -- -- -- -- -- -- ER→lem330 (Cred (cong$₁ r₁))     = inj₁ (cong$₁ r₁)
-- -- -- -- -- -- -- ER→lem330 (Cred (Ccong$₂ p₁ r₂)) = inj₁ (Ccong$₂ p₁ r₂)
-- -- -- -- -- -- -- ER→lem330 (Cred (Econg$₂ p₁ r₂)) = inj₁ (Econg$₂ p₁ r₂)
-- -- -- -- -- -- -- ER→lem330 (Cred (βred⊃ eq p₂))   = inj₁ (βred⊃ eq p₂)
-- -- -- -- -- -- -- ER→lem330 (ηexp⊃ refl x)         = inj₂ (_ , refl , refl , x)

-- -- -- -- -- -- -- lem330→ER : ∀ {Γ A} {t t′ : Γ ⊢ A} → Lem330 t t′ → t ⇒E t′
-- -- -- -- -- -- -- lem330→ER (inj₁ r)                     = Cred r
-- -- -- -- -- -- -- lem330→ER (inj₂ (_ , refl , refl , x)) = ηexp⊃ refl x

-- -- -- -- -- -- -- -- local confluence; Ghani p.53, lemma 3.3.3
-- -- -- -- -- -- -- -- TODO: needs lemma 3.3.2
-- -- -- -- -- -- -- -- mutual
-- -- -- -- -- -- -- --   lconf⇒E : ∀ {Γ A} {t t₁ t₂ : Γ ⊢ A} → t ⇒E t₁ → t ⇒E t₂ →
-- -- -- -- -- -- -- --              Σ _ λ t′ → t₁ E.⇒* t′ × t₂ E.⇒* t′
-- -- -- -- -- -- -- --   lconf⇒E {t = ⌜v⌝ i}     (ηexp⊃ refl x) (ηexp⊃ refl x′) = _ , E.done , E.done
-- -- -- -- -- -- -- --   lconf⇒E {t = ⌜λ⌝ t}     (Cred r)       (Cred r′)       with lem333⇒C r r′
-- -- -- -- -- -- -- --   ... | t′ , inj₁ rs , inj₁ rs′                            = t′ , Cred* rs , Cred* rs′
-- -- -- -- -- -- -- --   ... | t′ , inj₁ rs , inj₂ rs′                            = t′ , Cred* rs , rs′
-- -- -- -- -- -- -- --   ... | t′ , inj₂ rs , inj₁ rs′                            = t′ , rs , Cred* rs′
-- -- -- -- -- -- -- --   ... | t′ , inj₂ rs , inj₂ rs′                            = t′ , rs , rs′
-- -- -- -- -- -- -- --   lconf⇒E {t = t₁ ⌜$⌝ t₂} r r′ = {!!}
-- -- -- -- -- -- -- --
-- -- -- -- -- -- -- --   lem333⇒C : ∀ {Γ A} {t t₁ t₂ : Γ ⊢ A} → t ⇒C t₁ → t ⇒C t₂ →
-- -- -- -- -- -- -- --               Σ _ λ t′ → (t₁ C.⇒* t′ ⊎ t₁ E.⇒* t′) × (t₂ C.⇒* t′ ⊎ t₂ E.⇒* t′)
-- -- -- -- -- -- -- --   lem333⇒C {t = t₁ ⌜$⌝ t₂} r r′ = {!!}


-- -- -- -- -- -- -- ----------------------------------------------------------------------------------------------------
