module BasicIPC.Metatheory.ClosedHilbert-TarskiClosedCoquandDybjer where

open import BasicIPC.Syntax.ClosedHilbert public
open import BasicIPC.Semantics.TarskiClosedCoquandDybjer public

open SyntacticComponent (⊢_) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A} → ⊩ A → ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} (t , f) = t
  reify {A ∧ B} (a , b) = pair (reify a) (reify b)
  reify {⊤}    ∙       = tt


-- Additional useful equipment.

module _ {{_ : Model}} where
  ⟪const⟫ : ∀ {A B} → ⊩ A → ⊩ B ▻ A
  ⟪const⟫ a = app ck (reify a) , const a

  ⟪ap⟫′ : ∀ {A B C} → ⊩ A ▻ B ▻ C → ⊩ (A ▻ B) ▻ A ▻ C
  ⟪ap⟫′ f = app cs (reify f) , λ g →
              app (app cs (reify f)) (reify g) , ⟪ap⟫ f g

  _⟪,⟫′_ : ∀ {A B} → ⊩ A → ⊩ B ▻ A ∧ B
  _⟪,⟫′_ a = app cpair (reify a) , _,_ a


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A} → ⊢ A → ⊨ A
eval (app t u) = eval t ⟪$⟫ eval u
eval ci        = ci , id
eval ck        = ck , ⟪const⟫
eval cs        = cs , ⟪ap⟫′
eval cpair     = cpair , _⟪,⟫′_
eval cfst      = cfst , π₁
eval csnd      = csnd , π₂
eval tt        = ∙


-- Correctness of evaluation with respect to conversion.

eval✓ : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⋙ t′ → eval t ≡ eval t′
eval✓ refl⋙           = refl
eval✓ (trans⋙ p q)    = trans (eval✓ p) (eval✓ q)
eval✓ (sym⋙ p)        = sym (eval✓ p)
eval✓ (congapp⋙ p q)  = cong₂ _⟪$⟫_ (eval✓ p) (eval✓ q)
eval✓ (congi⋙ p)      = cong id (eval✓ p)
eval✓ (congk⋙ p q)    = cong₂ const (eval✓ p) (eval✓ q)
eval✓ (congs⋙ p q r)  = cong₃ ⟪ap⟫ (eval✓ p) (eval✓ q) (eval✓ r)
eval✓ (congpair⋙ p q) = cong₂ _,_ (eval✓ p) (eval✓ q)
eval✓ (congfst⋙ p)    = cong π₁ (eval✓ p)
eval✓ (congsnd⋙ p)    = cong π₂ (eval✓ p)
eval✓ beta▻ₖ⋙         = refl
eval✓ beta▻ₛ⋙         = refl
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
