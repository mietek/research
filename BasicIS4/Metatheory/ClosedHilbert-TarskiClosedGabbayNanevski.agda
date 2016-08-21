module BasicIS4.Metatheory.ClosedHilbert-TarskiClosedGabbayNanevski where

open import BasicIS4.Syntax.ClosedHilbert public
open import BasicIS4.Semantics.TarskiClosedGabbayNanevski public

open ImplicitSyntax (⊢_) public


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
  ⟪K⟫ : ∀ {A B} → ⊩ A → ⊩ B ▻ A
  ⟪K⟫ a = app ck (reify a) , K a

  ⟪S⟫′ : ∀ {A B C} → ⊩ A ▻ B ▻ C → ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ f = app cs (reify f) , λ g →
             app (app cs (reify f)) (reify g) , ⟪S⟫ f g

  _⟪D⟫_ : ∀ {A B} → ⊩ □ (A ▻ B) → ⊩ □ A → ⊩ □ B
  (t , f) ⟪D⟫ (u , a) = app (app cdist t) u , f ⟪$⟫ a

  _⟪D⟫′_ : ∀ {A B} → ⊩ □ (A ▻ B) → ⊩ □ A ▻ □ B
  _⟪D⟫′_ s = app cdist (reify s) , _⟪D⟫_ s

  ⟪↑⟫ : ∀ {A} → ⊩ □ A → ⊩ □ □ A
  ⟪↑⟫ (t , a) = box t , (t , a)

  _⟪,⟫′_ : ∀ {A B} → ⊩ A → ⊩ B ▻ A ∧ B
  _⟪,⟫′_ a = app cpair (reify a) , _,_ a


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A} → ⊢ A → ⊨ A
eval (app t u) = eval t ⟪$⟫ eval u
eval ci        = ci , I
eval ck        = ck , ⟪K⟫
eval cs        = cs , ⟪S⟫′
eval (box t)   = box t , eval t
eval cdist     = cdist , _⟪D⟫′_
eval cup       = cup , ⟪↑⟫
eval cdown     = cdown , ⟪↓⟫
eval cpair     = cpair , _⟪,⟫′_
eval cfst      = cfst , π₁
eval csnd      = csnd , π₂
eval tt        = ∙


-- Correctness of evaluation with respect to conversion.

eval✓ : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⋙ t′ → eval t ≡ eval t′
eval✓ refl⋙           = refl
eval✓ (trans⋙ p q)    = trans (eval✓ p) (eval✓ q)
eval✓ (sym⋙ p)        = sym (eval✓ p)
eval✓ (congapp⋙ p q)  = cong² _⟪$⟫_ (eval✓ p) (eval✓ q)
eval✓ (congi⋙ p)      = cong I (eval✓ p)
eval✓ (congk⋙ p q)    = cong² K (eval✓ p) (eval✓ q)
eval✓ (congs⋙ p q r)  = cong³ ⟪S⟫ (eval✓ p) (eval✓ q) (eval✓ r)
eval✓ (congdist⋙ p q) = cong² _⟪D⟫_ (eval✓ p) (eval✓ q)
eval✓ (congup⋙ p)     = cong ⟪↑⟫ (eval✓ p)
eval✓ (congdown⋙ p)   = cong ⟪↓⟫ (eval✓ p)
eval✓ (congpair⋙ p q) = cong² _,_ (eval✓ p) (eval✓ q)
eval✓ (congfst⋙ p)    = cong π₁ (eval✓ p)
eval✓ (congsnd⋙ p)    = cong π₂ (eval✓ p)
eval✓ beta▻ₖ⋙         = refl
eval✓ beta▻ₛ⋙         = refl
eval✓ beta□⋙          = refl
eval✓ eta□⋙           = refl
eval✓ beta∧₁⋙         = refl
eval✓ beta∧₂⋙         = refl
eval✓ eta∧⋙           = refl
eval✓ eta⊤⋙          = refl


-- The canonical model.

private
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

norm✓ : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⋙ t′ → norm t ≡ norm t′
norm✓ p = cong reify (eval✓ p)
