module A202103.FullSTLC-Syntax-Convertibility where

open import A202103.FullSTLC-Syntax public

------------------------------------------------------------------------------

data _≅_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where

  -- Equivalence rules.

  refl  : ∀ {A} {t : Γ ⊢ A} →
          t ≅ t

  trans : ∀ {A} {t t′ t″ : Γ ⊢ A} →
          t ≅ t′ → t′ ≅ t″ → t ≅ t″

  sym   : ∀ {A} {t t′ : Γ ⊢ A} →
          t ≅ t′ → t′ ≅ t

  -- Congruence rules.

  cong-lam    : ∀ {A B} {t t′ : Γ , A ⊢ B} →
                t ≅ t′ → lam t ≅ lam t′

  cong-app    : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⊃ B} {t₂ t₂′ : Γ ⊢ A} →
                t₁ ≅ t₁′ → t₂ ≅ t₂′ → app t₁ t₂ ≅ app t₁′ t₂′

  cong-pair   : ∀ {A B} {t₁ t₁′ : Γ ⊢ A} {t₂ t₂′ : Γ ⊢ B} →
                t₁ ≅ t₁′ → t₂ ≅ t₂′ → pair t₁ t₂ ≅ pair t₁′ t₂′

  cong-fst    : ∀ {A B} {t t′ : Γ ⊢ A ∧ B} →
                t ≅ t′ → fst t ≅ fst t′

  cong-snd    : ∀ {A B} {t t′ : Γ ⊢ A ∧ B} →
                t ≅ t′ → snd t ≅ snd t′

  cong-left   : ∀ {A B} {t t′ : Γ ⊢ A} →
                t ≅ t′ → left {B = B} t ≅ left t′

  cong-right  : ∀ {A B} {t t′ : Γ ⊢ B} →
                t ≅ t′ → right {A = A} t ≅ right t′

  cong-letsum : ∀ {A B C} {t₁ t₁′ : Γ ⊢ A ∨ B} {t₂ t₂′ : Γ , A ⊢ C} {t₃ t₃′ : Γ , B ⊢ C} →
                t₁ ≅ t₁′ → t₂ ≅ t₂′ → t₃ ≅ t₃′ → letsum t₁ t₂ t₃ ≅ letsum t₁′ t₂′ t₃′

  cong-abort  : ∀ {C} {t t′ : Γ ⊢ ⊥} →
                t ≅ t′ → abort {C = C} t ≅ abort t′

  -- Reduction rules.

  red-app-lam      : ∀ {A B} (t₁ : Γ , A ⊢ B) (t₂ : Γ ⊢ A) →
                     app (lam t₁) t₂ ≅ cut t₂ t₁

  red-fst-pair     : ∀ {A B} (t₁ : Γ ⊢ A) (t₂ : Γ ⊢ B) →
                     fst (pair t₁ t₂) ≅ t₁

  red-snd-pair     : ∀ {A B} (t₁ : Γ ⊢ A) (t₂ : Γ ⊢ B) →
                     snd (pair t₁ t₂) ≅ t₂

  red-letsum-left  : ∀ {A B C} (t₁ : Γ ⊢ A) (t₂ : Γ , A ⊢ C) (t₃ : Γ , B ⊢ C) →
                     letsum (left t₁) t₂ t₃ ≅ cut t₁ t₂

  red-letsum-right : ∀ {A B C} (t₁ : Γ ⊢ B) (t₂ : Γ , A ⊢ C) (t₃ : Γ , B ⊢ C) →
                     letsum (right t₁) t₂ t₃ ≅ cut t₁ t₃

  -- Expansion rules.

  exp-lam    : ∀ {A B} (t : Γ ⊢ A ⊃ B) →
               t ≅ lam (app (wk t) (var top))

  exp-unit   : ∀ {t : Γ ⊢ ⊤} →
               t ≅ unit

  exp-pair   : ∀ {A B} (t : Γ ⊢ A ∧ B) →
               t ≅ pair (fst t) (snd t)

  exp-letsum : ∀ {A B} (t : Γ ⊢ A ∨ B) →
               t ≅ letsum t (left (var top)) (right (var top))

  exp-abort  : ∀ (t : Γ ⊢ ⊥) →
               t ≅ abort t

≅←≡ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≡ t′ → t ≅ t′
≅←≡ refl = refl

------------------------------------------------------------------------------

-- TODO: Name.
thm₁ : ∀ {Γ Γ′ A} {t₁ t₂ : Γ ⊢ A} (η : Γ′ ⊒ Γ) →
       t₁ ≅ t₂ → ren η t₁ ≅ ren η t₂
thm₁ η refl                        = refl
thm₁ η (trans p₁ p₂)               = trans (thm₁ η p₁) (thm₁ η p₂)
thm₁ η (sym p)                     = sym (thm₁ η p)
thm₁ η (cong-lam p)                = cong-lam (thm₁ (liftr η) p)
thm₁ η (cong-app p₁ p₂)            = cong-app (thm₁ η p₁) (thm₁ η p₂)
thm₁ η (cong-pair p₁ p₂)           = cong-pair (thm₁ η p₁) (thm₁ η p₂)
thm₁ η (cong-fst p)                = cong-fst (thm₁ η p)
thm₁ η (cong-snd p)                = cong-snd (thm₁ η p)
thm₁ η (cong-left p)               = cong-left (thm₁ η p)
thm₁ η (cong-right p)              = cong-right (thm₁ η p)
thm₁ η (cong-letsum p₁ p₂ p₃)      = cong-letsum (thm₁ η p₁) (thm₁ (liftr η) p₂) (thm₁ (liftr η) p₃)
thm₁ η (cong-abort p)              = cong-abort (thm₁ η p)
thm₁ η (red-app-lam t₁ t₂)         = cast (red-app-lam (ren (liftr η) t₁) (ren η t₂))
                                          ((app _ _ ≅_) & comp-cut-ren η t₂ t₁)
thm₁ η (red-fst-pair t₁ t₂)        = red-fst-pair (ren η t₁) (ren η t₂)
thm₁ η (red-snd-pair t₁ t₂)        = red-snd-pair (ren η t₁) (ren η t₂)
thm₁ η (red-letsum-left t₁ t₂ t₃)  = cast (red-letsum-left (ren η t₁) (ren (liftr η) t₂) (ren (liftr η) t₃))
                                          ((letsum _ _ _ ≅_) & comp-cut-ren η t₁ t₂)
thm₁ η (red-letsum-right t₁ t₂ t₃) = cast (red-letsum-right (ren η t₁) (ren (liftr η) t₂) (ren (liftr η) t₃))
                                          ((letsum _ _ _ ≅_) & comp-cut-ren η t₁ t₃)
thm₁ η (exp-lam t)                 = cast (exp-lam (ren η t))
                                          ((λ t′ → ren η t ≅ lam (app t′ _)) & comp-wk-ren η t)
thm₁ η exp-unit                    = exp-unit
thm₁ η (exp-pair t)                = exp-pair (ren η t)
thm₁ η (exp-letsum t)              = exp-letsum (ren η t)
thm₁ η (exp-abort t)               = exp-abort (ren η t)

------------------------------------------------------------------------------
