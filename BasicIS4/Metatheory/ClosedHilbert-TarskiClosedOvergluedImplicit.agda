module BasicIS4.Metatheory.ClosedHilbert-TarskiClosedOvergluedImplicit where

open import BasicIS4.Syntax.ClosedHilbert public
open import BasicIS4.Semantics.TarskiClosedOvergluedImplicit public

open ImplicitSyntax (⊢_) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A} → ⊩ A → ⊢ A
  reify {α P}   s = syn s
  reify {A ▻ B} s = syn s
  reify {□ A}   s = syn s
  reify {A ∧ B} s = pair (reify (π₁ s)) (reify (π₂ s))
  reify {⊤}    s = tt


-- Additional useful equipment.

module _ {{_ : Model}} where
  ⟪K⟫ : ∀ {A B} → ⊩ A → ⊩ B ▻ A
  ⟪K⟫ a = app ck (reify a) ⅋ K a

  ⟪S⟫′ : ∀ {A B C} → ⊩ A ▻ B ▻ C → ⊩ (A ▻ B) ▻ A ▻ C
  ⟪S⟫′ s₁ = app cs (reify s₁) ⅋ λ s₂ →
              app (app cs (reify s₁)) (reify s₂) ⅋ ⟪S⟫ s₁ s₂

  _⟪D⟫_ : ∀ {A B} → ⊩ □ (A ▻ B) → ⊩ □ A → ⊩ □ B
  (t ⅋ s) ⟪D⟫ (u ⅋ a) = app (app cdist t) u ⅋ s ⟪$⟫ a

  _⟪D⟫′_ : ∀ {A B} → ⊩ □ (A ▻ B) → ⊩ □ A ▻ □ B
  _⟪D⟫′_ s = app cdist (reify s) ⅋ _⟪D⟫_ s

  ⟪↑⟫ : ∀ {A} → ⊩ □ A → ⊩ □ □ A
  ⟪↑⟫ s = box (syn s) ⅋ s

  _⟪,⟫′_ : ∀ {A B} → ⊩ A → ⊩ B ▻ A ∧ B
  _⟪,⟫′_ a = app cpair (reify a) ⅋ _,_ a


-- Soundness with respect to all models, or evaluation, for closed terms only.

eval₀ : ∀ {A} → ⊢ A → ⊨ A
eval₀ (app t u) = eval₀ t ⟪$⟫ eval₀ u
eval₀ ci        = ci ⅋ I
eval₀ ck        = ck ⅋ ⟪K⟫
eval₀ cs        = cs ⅋ ⟪S⟫′
eval₀ (box t)   = box t ⅋ eval₀ t
eval₀ cdist     = cdist ⅋ _⟪D⟫′_
eval₀ cup       = cup ⅋ ⟪↑⟫
eval₀ cdown     = cdown ⅋ ⟪↓⟫
eval₀ cpair     = cpair ⅋ _⟪,⟫′_
eval₀ cfst      = cfst ⅋ π₁
eval₀ csnd      = csnd ⅋ π₂
eval₀ tt        = ∙


-- Correctness of evaluation with respect to conversion.

eval₀✓ : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⋙ t′ → eval₀ t ≡ eval₀ t′
eval₀✓ refl⋙           = refl
eval₀✓ (trans⋙ p q)    = trans (eval₀✓ p) (eval₀✓ q)
eval₀✓ (sym⋙ p)        = sym (eval₀✓ p)
eval₀✓ (congapp⋙ p q)  = cong² _⟪$⟫_ (eval₀✓ p) (eval₀✓ q)
eval₀✓ (congi⋙ p)      = cong I (eval₀✓ p)
eval₀✓ (congk⋙ p q)    = cong² K (eval₀✓ p) (eval₀✓ q)
eval₀✓ (congs⋙ p q r)  = cong³ ⟪S⟫ (eval₀✓ p) (eval₀✓ q) (eval₀✓ r)
eval₀✓ (congdist⋙ p q) = cong² _⟪D⟫_ (eval₀✓ p) (eval₀✓ q)
eval₀✓ (congup⋙ p)     = cong ⟪↑⟫ (eval₀✓ p)
eval₀✓ (congdown⋙ p)   = cong ⟪↓⟫ (eval₀✓ p)
eval₀✓ (congpair⋙ p q) = cong² _,_ (eval₀✓ p) (eval₀✓ q)
eval₀✓ (congfst⋙ p)    = cong π₁ (eval₀✓ p)
eval₀✓ (congsnd⋙ p)    = cong π₂ (eval₀✓ p)
eval₀✓ beta▻ₖ⋙         = refl
eval₀✓ beta▻ₛ⋙         = refl
eval₀✓ beta□⋙          = refl
eval₀✓ eta□⋙           = refl
eval₀✓ beta∧₁⋙         = refl
eval₀✓ beta∧₂⋙         = refl
eval₀✓ eta∧⋙           = refl
eval₀✓ eta⊤⋙          = refl


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { ⊩ᵅ_ = λ P → ⊢ α P
      }


-- Completeness with respect to all models, or quotation, for closed terms only.

quot₀ : ∀ {A} → ⊨ A → ⊢ A
quot₀ s = reify s


-- Normalisation by evaluation, for closed terms only.

norm₀ : ∀ {A} → ⊢ A → ⊢ A
norm₀ = quot₀ ∘ eval₀


-- Correctness of normalisation with respect to conversion.

norm₀✓ : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⋙ t′ → norm₀ t ≡ norm₀ t′
norm₀✓ p = cong reify (eval₀✓ p)
