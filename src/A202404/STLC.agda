module A202404.STLC where

open import A202404.Prelude public


----------------------------------------------------------------------------------------------------

-- types
infixr 18 _⌜⊃⌝_
data Ty : Set where
  ⌜◦⌝   : Ty
  _⌜⊃⌝_ : ∀ (A B : Ty) → Ty

infix 4 _≟Ty_
_≟Ty_ : ∀ (A A′ : Ty) → Dec (A ≡ A′)
⌜◦⌝     ≟Ty ⌜◦⌝           = yes refl
⌜◦⌝     ≟Ty A′ ⌜⊃⌝ B′     = no λ ()
A ⌜⊃⌝ B ≟Ty ⌜◦⌝           = no λ ()
A ⌜⊃⌝ B ≟Ty A′ ⌜⊃⌝ B′     with A ≟Ty A′ | B ≟Ty B′
... | no ¬eq₁  | _          = no λ { refl → refl ↯ ¬eq₁ }
... | yes refl | no ¬eq₂    = no λ { refl → refl ↯ ¬eq₂ }
... | yes refl | yes refl   = yes refl

inj⊃₁ : ∀ {A A′ B B′} → A ⌜⊃⌝ B ≡ A′ ⌜⊃⌝ B′ → A ≡ A′
inj⊃₁ refl = refl

inj⊃₂ : ∀ {A A′ B B′} → A ⌜⊃⌝ B ≡ A′ ⌜⊃⌝ B′ → B ≡ B′
inj⊃₂ refl = refl


----------------------------------------------------------------------------------------------------

-- contexts
data Ctx : Set where
  ∙   : Ctx
  _,_ : ∀ (Γ : Ctx) (A : Ty) → Ctx

len : Ctx → ℕ
len ∙       = zero
len (Γ , A) = suc (len Γ)


----------------------------------------------------------------------------------------------------

-- variables (de Bruijn indices)
infix 3 _∋_
data _∋_ : Ctx → Ty → Set where
  zero : ∀ {Γ A} → Γ , A ∋ A
  wk∋  : ∀ {B Γ A} (i : Γ ∋ A) → Γ , B ∋ A

fin : ∀ {Γ A} → Γ ∋ A → Fin (len Γ)
fin zero    = zero
fin (wk∋ i) = suc (fin i)

get : ∀ (Γ : Ctx) (k : Fin (len Γ)) → Σ Ty λ A → Σ (Γ ∋ A) λ i → k ≡ fin i
get (Γ , A) zero    = A , zero , refl
get (Γ , B) (suc k) = let A , i , eq = get Γ k in A , wk∋ i , suc & eq

uniTy∋ : ∀ {Γ A A′ k} (i : Γ ∋ A) (i′ : Γ ∋ A′) → k ≡ fin i → k ≡ fin i′ → A ≡ A′
uniTy∋ zero    zero     refl eq′ = refl
uniTy∋ zero    (wk∋ i′) refl ()
uniTy∋ (wk∋ i) zero     refl ()
uniTy∋ (wk∋ i) (wk∋ i′) refl eq′ = uniTy∋ i i′ refl (injsuc eq′)


----------------------------------------------------------------------------------------------------

-- standard well scoped untyped terms with "check" annotations only
infixl 18 _⌜$⌝_
data Tm (n : ℕ) : Set where
  var   : Fin n → Tm n
  ⌜λ⌝   : String → Tm (suc n) → Tm n
  _⌜$⌝_ : Tm n → Tm n → Tm n
  chk   : Ty → Tm n → Tm n

-- standard intrinsically well typed terms
infix 3 _⊢_
data _⊢_ (Γ : Ctx) : Ty → Set where
  var   : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A
  ⌜λ⌝   : ∀ {A B} (x : String) (t : Γ , A ⊢ B) → Γ ⊢ A ⌜⊃⌝ B
  _⌜$⌝_ : ∀ {A B} (t₁ : Γ ⊢ A ⌜⊃⌝ B) (t₂ : Γ ⊢ A) → Γ ⊢ B

-- standard typing judgments
infix 3 _⊢_⦂_
data _⊢_⦂_ (Γ : Ctx) : Tm (len Γ) → Ty → Set where
  var   : ∀ {A i′} (i : Γ ∋ A) (eq : i′ ≡ fin i) → Γ ⊢ var i′ ⦂ A
  ⌜λ⌝   : ∀ {A B M x} (t : Γ , A ⊢ M ⦂ B) → Γ ⊢ ⌜λ⌝ x M ⦂ A ⌜⊃⌝ B
  _⌜$⌝_ : ∀ {A B M₁ M₂} (t₁ : Γ ⊢ M₁ ⦂ A ⌜⊃⌝ B) (t₂ : Γ ⊢ M₂ ⦂ A) → Γ ⊢ M₁ ⌜$⌝ M₂ ⦂ B


----------------------------------------------------------------------------------------------------

-- standard β-short η-long intrinsically well typed terms
mutual
  infix 3 _⊢_normal
  data _⊢_normal (Γ : Ctx) : Ty → Set where
    ⌜λ⌝ : ∀ {A B} (x : String) (t : Γ , A ⊢ B normal) → Γ ⊢ A ⌜⊃⌝ B normal
    neu : ∀ (t : Γ ⊢ ⌜◦⌝ neutral) → Γ ⊢ ⌜◦⌝ normal

  infix 3 _⊢_neutral
  data _⊢_neutral (Γ : Ctx) : Ty → Set where
    var   : ∀ {A} (i : Γ ∋ A) → Γ ⊢ A neutral
    _⌜$⌝_ : ∀ {A B} (t₁ : Γ ⊢ A ⌜⊃⌝ B neutral) (t₂ : Γ ⊢ A normal) → Γ ⊢ B neutral

-- standard β-short η-long typing judgments
mutual
  infix 3 _⊢_⦂_normal
  data _⊢_⦂_normal (Γ : Ctx) : Tm (len Γ) → Ty → Set where
    ⌜λ⌝ : ∀ {A B M x} (t : Γ , A ⊢ M ⦂ B normal) → Γ ⊢ ⌜λ⌝ x M ⦂ A ⌜⊃⌝ B normal
    neu : ∀ {M} (t : Γ ⊢ M ⦂ ⌜◦⌝ neutral) → Γ ⊢ M ⦂ ⌜◦⌝ normal

  infix 3 _⊢_⦂_neutral
  data _⊢_⦂_neutral (Γ : Ctx) : Tm (len Γ) → Ty → Set where
    var   : ∀ {A i′} (i : Γ ∋ A) (eq : i′ ≡ fin i) → Γ ⊢ var i′ ⦂ A neutral
    _⌜$⌝_ : ∀ {A B M₁ M₂} (t₁ : Γ ⊢ M₁ ⦂ A ⌜⊃⌝ B neutral) (t₂ : Γ ⊢ M₂ ⦂ A normal) →
              Γ ⊢ M₁ ⌜$⌝ M₂ ⦂ B neutral


----------------------------------------------------------------------------------------------------

-- bidirectional typing judgments with "infer" and "check" annotations
mutual
  infix 3 _⊢_≪_
  data _⊢_≪_ (Γ : Ctx) : Tm (len Γ) → Ty → Set where
    ⌜λ⌝ : ∀ {A B M x} (t : Γ , A ⊢ M ≪ B) → Γ ⊢ ⌜λ⌝ x M ≪ A ⌜⊃⌝ B
    inf : ∀ {A M} (t : Γ ⊢ M ≫ A) → Γ ⊢ M ≪ A

  infix 3 _⊢_≫_
  data _⊢_≫_ (Γ : Ctx) : Tm (len Γ) → Ty → Set where
    var   : ∀ {A i′} (i : Γ ∋ A) (eq : i′ ≡ fin i) → Γ ⊢ var i′ ≫ A
    _⌜$⌝_ : ∀ {A B M₁ M₂} (t₁ : Γ ⊢ M₁ ≫ A ⌜⊃⌝ B) (t₂ : Γ ⊢ M₂ ≪ A) → Γ ⊢ M₁ ⌜$⌝ M₂ ≫ B
    chk   : ∀ {A M} (t : Γ ⊢ M ≪ A) → Γ ⊢ chk A M ≫ A

uniTy≫ : ∀ {Γ M A A′} → Γ ⊢ M ≫ A → Γ ⊢ M ≫ A′ → A ≡ A′
uniTy≫ (var i eq)  (var i′ eq′)  = uniTy∋ i i′ eq eq′
uniTy≫ (t₁ ⌜$⌝ t₂) (t₁′ ⌜$⌝ t₂′) = inj⊃₂ (uniTy≫ t₁ t₁′)
uniTy≫ (chk t)     (chk t′)      = refl

mutual
  -- NOTE: we repeat ourselves here  because Agda doesn't know how to catch-all properly
  check : ∀ (Γ : Ctx) (M : Tm (len Γ)) (A : Ty) → Dec (Γ ⊢ M ≪ A)
  check Γ (⌜λ⌝ x M)   ⌜◦⌝       = no λ { (inf ()) }
  check Γ (⌜λ⌝ x M)   (A ⌜⊃⌝ B) with check (Γ , A) M B
  ... | no ¬t                     = no λ { (⌜λ⌝ t) → t ↯ ¬t }
  ... | yes t                     = yes (⌜λ⌝ t)
  check Γ M@(var _)   A         with infer Γ M
  ... | no ¬p                     = no λ { (inf t) → (A , t) ↯ ¬p }
  ... | yes (A′ , t′)             with A ≟Ty A′
  ...   | no ¬eq                    = no λ { (inf t) → uniTy≫ t t′ ↯ ¬eq }
  ...   | yes refl                  = yes (inf t′)
  check Γ M@(_ ⌜$⌝ _) A         with infer Γ M
  ... | no ¬p                     = no λ { (inf t) → (A , t) ↯ ¬p }
  ... | yes (A′ , t′)             with A ≟Ty A′
  ...   | no ¬eq                    = no λ { (inf t) → uniTy≫ t t′ ↯ ¬eq }
  ...   | yes refl                  = yes (inf t′)
  check Γ M@(chk _ _) A         with infer Γ M
  ... | no ¬p                     = no λ { (inf t) → (A , t) ↯ ¬p }
  ... | yes (A′ , t′)             with A ≟Ty A′
  ...   | no ¬eq                    = no λ { (inf t) → uniTy≫ t t′ ↯ ¬eq }
  ...   | yes refl                  = yes (inf t′)

  infer : ∀ (Γ : Ctx) (M : Tm (len Γ)) → Dec (Σ Ty λ A → Γ ⊢ M ≫ A)
  infer Γ (var k)          with get Γ k
  ... | (A , i , eq)         = yes (A , var i eq)
  infer Γ (⌜λ⌝ x M)        = no λ ()
  infer Γ (M₁ ⌜$⌝ M)       with infer Γ M₁
  ... | no ¬p                = no λ { (B , t₁ ⌜$⌝ t) → (_ ⌜⊃⌝ B , t₁) ↯ ¬p }
  ... | yes (⌜◦⌝ , t₁)       = no λ { (B , t₁′ ⌜$⌝ t) → uniTy≫ t₁ t₁′ ↯ λ () }
  ... | yes (A ⌜⊃⌝ B , t₁)   with check Γ M A
  ...   | no ¬t               = no λ { (B′ , t₁′ ⌜$⌝ t) →
                                  transport ((Γ ⊢ M ≪_) & (inj⊃₁ (uniTy≫ t₁′ t₁))) t ↯ ¬t }
  ...   | yes t               = yes (B , t₁ ⌜$⌝ t)
  infer Γ (chk A M)        with check Γ M A
  ... | no ¬t                = no λ { (.A , chk t) → t ↯ ¬t }
  ... | yes t                = yes (A , chk t)


----------------------------------------------------------------------------------------------------
