module BasicIPC.Metatheory.Hilbert-TarskiClosedCoquandDybjer where

open import BasicIPC.Syntax.Hilbert public
open import BasicIPC.Semantics.TarskiClosedCoquandDybjer public

open ImplicitSyntax (⌀ ⊢_) public


-- Completeness with respect to a particular model, for closed terms only.

module _ {{_ : Model}} where
  reify : ∀ {A} → ⊩ A → ⌀ ⊢ A
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

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ ⟪$⟫ eval u γ
eval ci        γ = ci , id
eval ck        γ = ck , ⟪const⟫
eval cs        γ = cs , ⟪ap⟫′
eval cpair     γ = cpair , _⟪,⟫′_
eval cfst      γ = cfst , π₁
eval csnd      γ = csnd , π₂
eval tt        γ = ∙


-- Correctness of evaluation with respect to conversion.

eval✓ : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⋙ t′ → eval t ≡ eval t′
eval✓ refl⋙                   = refl
eval✓ (trans⋙ p q)            = trans (eval✓ p) (eval✓ q)
eval✓ (sym⋙ p)                = sym (eval✓ p)
eval✓ (congapp⋙ p q)          = cong₂ _⟦$⟧_ (eval✓ p) (eval✓ q)
eval✓ (congi⋙ p)              = cong id (eval✓ p)
eval✓ (congk⋙ p q)            = cong₂ const (eval✓ p) (eval✓ q)
eval✓ (congs⋙ p q r)          = cong₃ ⟦ap⟧ (eval✓ p) (eval✓ q) (eval✓ r)
eval✓ (congpair⋙ {A} {B} p q) = cong₂ (_⟦,⟧_ {A} {B}) (eval✓ p) (eval✓ q)
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
      { ⊩ᵅ_ = λ P → ⌀ ⊢ α P
      }


-- Completeness with respect to all models, or quotation, for closed terms only.

quot₀ : ∀ {A} → ⌀ ⊨ A → ⌀ ⊢ A
quot₀ t = reify (t ∙)


-- Normalisation by evaluation, for closed terms only.

norm₀ : ∀ {A} → ⌀ ⊢ A → ⌀ ⊢ A
norm₀ = quot₀ ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
