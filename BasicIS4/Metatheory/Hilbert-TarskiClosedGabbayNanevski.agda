module BasicIS4.Metatheory.Hilbert-TarskiClosedGabbayNanevski where

open import BasicIS4.Syntax.Hilbert public
open import BasicIS4.Semantics.TarskiClosedGabbayNanevski public

open SyntacticComponent (⌀ ⊢_) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A} → ⊩ A → ⌀ ⊢ A
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


-- Additional useful equipment, for sequents.

module _ {{_ : Model}} where
  _⟦◎⟧_ : ∀ {A B Γ} → ⊩ Γ ⇒ □ (A ▻ B) → ⊩ Γ ⇒ □ A → ⊩ Γ ⇒ □ B
  (s₁ ⟦◎⟧ s₂) γ = (s₁ γ) ⟪◎⟫ (s₂ γ)

  ⟦⇑⟧ : ∀ {A Γ} → ⊩ Γ ⇒ □ A → ⊩ Γ ⇒ □ □ A
  ⟦⇑⟧ s γ = ⟪⇑⟫ (s γ)


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ ⟪$⟫ eval u γ
eval ci        γ = ci , id
eval ck        γ = ck , ⟪const⟫
eval cs        γ = cs , ⟪ap⟫′
eval (box t)   γ = box t , eval t ∙
eval cdist     γ = cdist , _⟪◎⟫′_
eval cup       γ = cup , ⟪⇑⟫
eval cdown     γ = cdown , ⟪⇓⟫
eval cpair     γ = cpair , _⟪,⟫′_
eval cfst      γ = cfst , π₁
eval csnd      γ = csnd , π₂
eval tt        γ = ∙


-- Correctness of evaluation with respect to conversion.

check : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⋙ t′ → eval t ≡ eval t′
check refl⋙                   = refl
check (trans⋙ p q)            = trans (check p) (check q)
check (sym⋙ p)                = sym (check p)
check (congapp⋙ p q)          = cong₂ _⟦$⟧_ (check p) (check q)
check (congi⋙ p)              = cong id (check p)
check (congk⋙ p q)            = cong₂ const (check p) (check q)
check (congs⋙ p q r)          = cong₃ ⟦ap⟧ (check p) (check q) (check r)
check (congdist⋙ p q)         = cong₂ _⟦◎⟧_ (check p) (check q)
check (congup⋙ p)             = cong ⟦⇑⟧ (check p)
check (congdown⋙ p)           = cong ⟦⇓⟧ (check p)
check (congpair⋙ {A} {B} p q) = cong₂ (_⟦,⟧_ {A} {B}) (check p) (check q)
check (congfst⋙ {A} {B} p)    = cong (⟦π₁⟧ {A} {B}) (check p)
check (congsnd⋙ {A} {B} p)    = cong (⟦π₂⟧ {A} {B}) (check p)
check beta▻ₖ⋙                 = refl
check beta▻ₛ⋙                 = refl
check beta∧₁⋙                 = refl
check beta∧₂⋙                 = refl
check eta∧⋙                   = refl
check eta⊤⋙                  = refl


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { ⊩ᵅ_ = λ P → ⌀ ⊢ α P
      }


-- Completeness with respect to all models, or quotation.

quot₀ : ∀ {A} → ⌀ ⊨ A → ⌀ ⊢ A
quot₀ t = reify (t ∙)


-- Normalisation by evaluation.

norm₀ : ∀ {A} → ⌀ ⊢ A → ⌀ ⊢ A
norm₀ = quot₀ ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
