module BasicIS4.Metatheory.ClosedHilbert-TarskiClosedGabbayNanevski where

open import BasicIS4.Syntax.ClosedHilbert public
open import BasicIS4.Semantics.TarskiClosedGabbayNanevski public

open SyntacticComponent (⊢_) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A} → ⊩ A → ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} (t , f) = t
  reify {□ A}   (t , a) = t
  reify {A ∧ B} (a , b) = pair (reify a) (reify b)
  reify {⊤}    ∙       = tt


-- Additional useful equipment.

module _ {{_ : Model}} where
  ⟪const⟫ : ∀ {A B} → ⊩ A → ⊩ B ▻ A
  ⟪const⟫ a = app ck (reify a) , const a

  ⟪ap⟫′ : ∀ {A B C} → ⊩ A ▻ B ▻ C → ⊩ (A ▻ B) ▻ A ▻ C
  ⟪ap⟫′ f = app cs (reify f) , λ g →
              app (app cs (reify f)) (reify g) , ⟪ap⟫ f g

  _⟪◎⟫_ : ∀ {A B} → ⊩ □ (A ▻ B) → ⊩ □ A → ⊩ □ B
  (t , f) ⟪◎⟫ (u , a) = app (app cdist t) u , f ⟪$⟫ a

  _⟪◎⟫′_ : ∀ {A B} → ⊩ □ (A ▻ B) → ⊩ □ A ▻ □ B
  _⟪◎⟫′_ s = app cdist (reify s) , _⟪◎⟫_ s

  ⟪⇑⟫ : ∀ {A} → ⊩ □ A → ⊩ □ □ A
  ⟪⇑⟫ (t , a) = box t , (t , a)

  _⟪,⟫′_ : ∀ {A B} → ⊩ A → ⊩ B ▻ A ∧ B
  _⟪,⟫′_ a = app cpair (reify a) , _,_ a


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A} → ⊢ A → ⊨ A
eval (app t u) = eval t ⟪$⟫ eval u
eval ci        = ci , id
eval ck        = ck , ⟪const⟫
eval cs        = cs , ⟪ap⟫′
eval (box t)   = box t , eval t
eval cdist     = cdist , _⟪◎⟫′_
eval cup       = cup , ⟪⇑⟫
eval cdown     = cdown , ⟪⇓⟫
eval cpair     = cpair , _⟪,⟫′_
eval cfst      = cfst , π₁
eval csnd      = csnd , π₂
eval tt        = ∙


-- Correctness of evaluation with respect to conversion.

check : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⋙ t′ → eval t ≡ eval t′
check refl⋙           = refl
check (trans⋙ p q)    = trans (check p) (check q)
check (sym⋙ p)        = sym (check p)
check (congapp⋙ p q)  = cong₂ _⟪$⟫_ (check p) (check q)
check (congi⋙ p)      = cong id (check p)
check (congk⋙ p q)    = cong₂ const (check p) (check q)
check (congs⋙ p q r)  = cong₃ ⟪ap⟫ (check p) (check q) (check r)
check (congdist⋙ p q) = cong₂ _⟪◎⟫_ (check p) (check q)
check (congup⋙ p)     = cong ⟪⇑⟫ (check p)
check (congdown⋙ p)   = cong ⟪⇓⟫ (check p)
check (congpair⋙ p q) = cong₂ _,_ (check p) (check q)
check (congfst⋙ p)    = cong π₁ (check p)
check (congsnd⋙ p)    = cong π₂ (check p)
check beta▻ₖ⋙         = refl
check beta▻ₛ⋙         = refl
check beta□⋙          = refl
check eta□⋙           = refl
check beta∧₁⋙         = refl
check beta∧₂⋙         = refl
check eta∧⋙           = refl
check eta⊤⋙          = refl


-- The canonical model.

instance
  canon : Model
  canon = record
    { ⊩ᵅ_ = λ P → ⊢ α P
    }


-- Completeness with respect to all models, or quotation.

quot : ∀ {A} → ⊨ A → ⊢ A
quot s = reify s


-- Normalisation by evaluation.

norm : ∀ {A} → ⊢ A → ⊢ A
norm = quot ∘ eval


-- Correctness of normalisation with respect to conversion.

check′ : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⋙ t′ → norm t ≡ norm t′
check′ p = cong reify (check p)
