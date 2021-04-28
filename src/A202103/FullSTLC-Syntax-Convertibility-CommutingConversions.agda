module A202103.FullSTLC-Syntax-Convertibility-CommutingConversions where

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

  -- Commuting conversion rules for sum types.

  comm-letsum-app    : ∀ {X Y A B} (t₁ : Γ ⊢ X ∨ Y) (t₂ : Γ , X ⊢ A ⊃ B) (t₃ : Γ , Y ⊢ A ⊃ B) (t₄ : Γ ⊢ A) →
                       letsum t₁ (app t₂ (wk t₄)) (app t₃ (wk t₄)) ≅ app (letsum t₁ t₂ t₃) t₄

  comm-letsum-fst    : ∀ {X Y A B} (t₁ : Γ ⊢ X ∨ Y) (t₂ : Γ , X ⊢ A ∧ B) (t₃ : Γ , Y ⊢ A ∧ B) →
                       letsum t₁ (fst t₂) (fst t₃) ≅ fst (letsum t₁ t₂ t₃)

  comm-letsum-snd    : ∀ {X Y A B} (t₁ : Γ ⊢ X ∨ Y) (t₂ : Γ , X ⊢ A ∧ B) (t₃ : Γ , Y ⊢ A ∧ B) →
                       letsum t₁ (snd t₂) (snd t₃) ≅ snd (letsum t₁ t₂ t₃)

  comm-letsum-abort  : ∀ {X Y C} (t₁ : Γ ⊢ X ∨ Y) (t₂ : Γ , X ⊢ ⊥) (t₃ : Γ , Y ⊢ ⊥) →
                       letsum t₁ (abort {C = C} t₂) (abort t₃) ≅ abort (letsum t₁ t₂ t₃)

  comm-letsum-letsum : ∀ {X Y A B C} (t₁ : Γ ⊢ X ∨ Y) (t₂ : Γ , X ⊢ A ∨ B) (t₃ : Γ , Y ⊢ A ∨ B)
                                     (t₄ : Γ , A ⊢ C) (t₅ : Γ , B ⊢ C) →
                       letsum t₁ (letsum t₂ (lift-wk t₄) (lift-wk t₅))
                                 (letsum t₃ (lift-wk t₄) (lift-wk t₅)) ≅ letsum (letsum t₁ t₂ t₃) t₄ t₅

  -- Commuting conversion rules for the empty type.

  comm-abort-app    : ∀ {A B} (t₁ : Γ ⊢ ⊥) (t₂ : Γ ⊢ A) →
                      abort t₁ ≅ app {B = B} (abort t₁) t₂

  comm-abort-fst    : ∀ {A B} (t : Γ ⊢ ⊥) →
                      abort t ≅ fst {A = A} {B} (abort t)

  comm-abort-snd    : ∀ {A B} (t : Γ ⊢ ⊥) →
                      abort t ≅ snd {A = A} {B} (abort t)

  comm-abort-abort  : ∀ {C} (t : Γ ⊢ ⊥) →
                      abort t ≅ abort {C = C} (abort t)

  comm-abort-letsum : ∀ {A B C} (t₁ : Γ ⊢ ⊥) (t₂ : Γ , A ⊢ C) (t₃ : Γ , B ⊢ C) →
                      abort t₁ ≅ letsum (abort t₁) t₂ t₃

≅←≡ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≡ t′ → t ≅ t′
≅←≡ refl = refl

------------------------------------------------------------------------------

-- TODO: Name.
thm₁ : ∀ {Γ Γ′ A} {t₁ t₂ : Γ ⊢ A} (η : Γ′ ⊒ Γ) →
       t₁ ≅ t₂ → ren η t₁ ≅ ren η t₂
thm₁ η refl                                = refl
thm₁ η (trans p₁ p₂)                       = trans (thm₁ η p₁) (thm₁ η p₂)
thm₁ η (sym p)                             = sym (thm₁ η p)
thm₁ η (cong-lam p)                        = cong-lam (thm₁ (liftr η) p)
thm₁ η (cong-app p₁ p₂)                    = cong-app (thm₁ η p₁) (thm₁ η p₂)
thm₁ η (cong-pair p₁ p₂)                   = cong-pair (thm₁ η p₁) (thm₁ η p₂)
thm₁ η (cong-fst p)                        = cong-fst (thm₁ η p)
thm₁ η (cong-snd p)                        = cong-snd (thm₁ η p)
thm₁ η (cong-left p)                       = cong-left (thm₁ η p)
thm₁ η (cong-right p)                      = cong-right (thm₁ η p)
thm₁ η (cong-letsum p₁ p₂ p₃)              = cong-letsum (thm₁ η p₁) (thm₁ (liftr η) p₂) (thm₁ (liftr η) p₃)
thm₁ η (cong-abort p)                      = cong-abort (thm₁ η p)

thm₁ η (red-app-lam t₁ t₂)
  = cast (red-app-lam (ren (liftr η) t₁) (ren η t₂))
         ((app _ _ ≅_) & comp-cut-ren η t₂ t₁)

thm₁ η (red-fst-pair t₁ t₂)                = red-fst-pair (ren η t₁) (ren η t₂)
thm₁ η (red-snd-pair t₁ t₂)                = red-snd-pair (ren η t₁) (ren η t₂)

thm₁ η (red-letsum-left t₁ t₂ t₃)
  = cast (red-letsum-left (ren η t₁) (ren (liftr η) t₂) (ren (liftr η) t₃))
         ((letsum _ _ _ ≅_) & comp-cut-ren η t₁ t₂)

thm₁ η (red-letsum-right t₁ t₂ t₃)
  = cast (red-letsum-right (ren η t₁) (ren (liftr η) t₂) (ren (liftr η) t₃))
         ((letsum _ _ _ ≅_) & comp-cut-ren η t₁ t₃)

thm₁ η (exp-lam t)
  = cast (exp-lam (ren η t))
         ((λ t′ → ren η t ≅ lam (app t′ _)) & comp-wk-ren η t)

thm₁ η exp-unit                            = exp-unit
thm₁ η (exp-pair t)                        = exp-pair (ren η t)
thm₁ η (exp-letsum t)                      = exp-letsum (ren η t)
thm₁ η (exp-abort t)                       = exp-abort (ren η t)

thm₁ η (comm-letsum-app t₁ t₂ t₃ t₄)
  = cast (comm-letsum-app (ren η t₁) (ren (liftr η) t₂) (ren (liftr η) t₃) (ren η t₄))
         ((λ t₄′ t₄″ → letsum _ (app _ t₄′) (app _ t₄″)
                      ≅ app (letsum _ _ _) _) & comp-wk-ren η t₄ ⊗ comp-wk-ren η t₄)

thm₁ η (comm-letsum-fst t₁ t₂ t₃)          = comm-letsum-fst (ren η t₁) (ren (liftr η) t₂) (ren (liftr η) t₃)
thm₁ η (comm-letsum-snd t₁ t₂ t₃)          = comm-letsum-snd (ren η t₁) (ren (liftr η) t₂) (ren (liftr η) t₃)
thm₁ η (comm-letsum-abort t₁ t₂ t₃)        = comm-letsum-abort (ren η t₁) (ren (liftr η) t₂) (ren (liftr η) t₃)

thm₁ η (comm-letsum-letsum t₁ t₂ t₃ t₄ t₅)
  = cast (comm-letsum-letsum (ren η t₁) (ren (liftr η) t₂) (ren (liftr η) t₃) (ren (liftr η) t₄) (ren (liftr η) t₅))
         ((λ t₄′ t₅′ t₄″ t₅″ → letsum _ (letsum _ t₄′ t₅′) (letsum _ t₄″ t₅″)
                              ≅ letsum (letsum _ _ _) _ _) & comp-lift-wk-ren η t₄ ⊗ comp-lift-wk-ren η t₅
                                                           ⊗ comp-lift-wk-ren η t₄ ⊗ comp-lift-wk-ren η t₅)

thm₁ η (comm-abort-app t₁ t₂)              = comm-abort-app (ren η t₁) (ren η t₂)
thm₁ η (comm-abort-fst t)                  = comm-abort-fst (ren η t)
thm₁ η (comm-abort-snd t)                  = comm-abort-snd (ren η t)
thm₁ η (comm-abort-abort t)                = comm-abort-abort (ren η t)
thm₁ η (comm-abort-letsum t₁ t₂ t₃)        = comm-abort-letsum (ren η t₁) (ren (liftr η) t₂) (ren (liftr η) t₃)

------------------------------------------------------------------------------
