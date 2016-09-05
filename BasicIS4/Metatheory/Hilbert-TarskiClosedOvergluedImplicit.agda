module BasicIS4.Metatheory.Hilbert-TarskiClosedOvergluedImplicit where

open import BasicIS4.Syntax.Hilbert public
open import BasicIS4.Semantics.TarskiClosedOvergluedImplicit public

open ImplicitSyntax (∅ ⊢_) public


-- Completeness with respect to a particular model, for closed terms only.

module _ {{_ : Model}} where
  reify : ∀ {A} → ⊩ A → ∅ ⊢ A
  reify {α P}   s = syn s
  reify {A ▻ B} s = syn s
  reify {□ A}   s = syn s
  reify {A ∧ B} s = pair (reify (π₁ s)) (reify (π₂ s))
  reify {⊤}    s = unit


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


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  _⟦D⟧_ : ∀ {A B Γ} → ⊩ Γ ⇒ □ (A ▻ B) → ⊩ Γ ⇒ □ A → ⊩ Γ ⇒ □ B
  (s₁ ⟦D⟧ s₂) γ = (s₁ γ) ⟪D⟫ (s₂ γ)

  ⟦↑⟧ : ∀ {A Γ} → ⊩ Γ ⇒ □ A → ⊩ Γ ⇒ □ □ A
  ⟦↑⟧ s γ = ⟪↑⟫ (s γ)


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ ⟪$⟫ eval u γ
eval ci        γ = ci ⅋ I
eval ck        γ = ck ⅋ ⟪K⟫
eval cs        γ = cs ⅋ ⟪S⟫′
eval (box t)   γ = box t ⅋ eval t ∙
eval cdist     γ = cdist ⅋ _⟪D⟫′_
eval cup       γ = cup ⅋ ⟪↑⟫
eval cdown     γ = cdown ⅋ ⟪↓⟫
eval cpair     γ = cpair ⅋ _⟪,⟫′_
eval cfst      γ = cfst ⅋ π₁
eval csnd      γ = csnd ⅋ π₂
eval unit      γ = ∙


-- Correctness of evaluation with respect to conversion.

eval✓ : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⋙ t′ → eval t ≡ eval t′
eval✓ refl⋙                   = refl
eval✓ (trans⋙ p q)            = trans (eval✓ p) (eval✓ q)
eval✓ (sym⋙ p)                = sym (eval✓ p)
eval✓ (congapp⋙ p q)          = cong² _⟦$⟧_ (eval✓ p) (eval✓ q)
eval✓ (congi⋙ p)              = cong I (eval✓ p)
eval✓ (congk⋙ p q)            = cong² K (eval✓ p) (eval✓ q)
eval✓ (congs⋙ p q r)          = cong³ ⟦S⟧ (eval✓ p) (eval✓ q) (eval✓ r)
eval✓ (congdist⋙ p q)         = cong² _⟦D⟧_ (eval✓ p) (eval✓ q)
eval✓ (congup⋙ p)             = cong ⟦↑⟧ (eval✓ p)
eval✓ (congdown⋙ p)           = cong ⟦↓⟧ (eval✓ p)
eval✓ (congpair⋙ {A} {B} p q) = cong² (_⟦,⟧_ {A} {B}) (eval✓ p) (eval✓ q)
eval✓ (congfst⋙ {A} {B} p)    = cong (⟦π₁⟧ {A} {B}) (eval✓ p)
eval✓ (congsnd⋙ {A} {B} p)    = cong (⟦π₂⟧ {A} {B}) (eval✓ p)
eval✓ beta▻ₖ⋙                 = refl
eval✓ beta▻ₛ⋙                 = refl
eval✓ beta∧₁⋙                 = refl
eval✓ beta∧₂⋙                 = refl
eval✓ eta∧⋙                   = refl
eval✓ eta⊤⋙                  = refl


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { ⊩ᵅ_ = λ P → ∅ ⊢ α P
      }


-- Completeness with respect to all models, or quotation, for closed terms only.

quot₀ : ∀ {A} → ∅ ⊨ A → ∅ ⊢ A
quot₀ t = reify (t ∙)


-- Normalisation by evaluation, for closed terms only.

norm₀ : ∀ {A} → ∅ ⊢ A → ∅ ⊢ A
norm₀ = quot₀ ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
