module A202103.STLC-Syntax-Convertibility where

open import A202103.STLC-Syntax public

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

  cong-lam : ∀ {A B} {t t′ : Γ , A ⊢ B} →
             t ≅ t′ → lam t ≅ lam t′

  cong-app : ∀ {A B} {t₁ t₁′ : Γ ⊢ A ⊃ B} {t₂ t₂′ : Γ ⊢ A} →
             t₁ ≅ t₁′ → t₂ ≅ t₂′ → app t₁ t₂ ≅ app t₁′ t₂′

  -- Reduction and expansion rules.

  red-app-lam : ∀ {A B} (t₁ : Γ , A ⊢ B) (t₂ : Γ ⊢ A) →
                app (lam t₁) t₂ ≅ cut t₂ t₁

  exp-lam     : ∀ {A B} (t : Γ ⊢ A ⊃ B) →
                t ≅ lam (app (wk t) (var top))

≅←≡ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≡ t′ → t ≅ t′
≅←≡ refl = refl

------------------------------------------------------------------------------

-- TODO: Name.
thm₁ : ∀ {Γ Γ′ A} {t₁ t₂ : Γ ⊢ A} (η : Γ′ ⊒ Γ) →
       t₁ ≅ t₂ → ren η t₁ ≅ ren η t₂
thm₁ η refl                = refl
thm₁ η (trans p₁ p₂)       = trans (thm₁ η p₁) (thm₁ η p₂)
thm₁ η (sym p)             = sym (thm₁ η p)
thm₁ η (cong-lam p)        = cong-lam (thm₁ (liftr η) p)
thm₁ η (cong-app p₁ p₂)    = cong-app (thm₁ η p₁) (thm₁ η p₂)
thm₁ η (red-app-lam t₁ t₂) = cast (red-app-lam (ren (liftr η) t₁) (ren η t₂))
                                  ((app (lam (ren (liftr η) t₁)) (ren η t₂) ≅_) & comp-cut-ren η t₂ t₁)
thm₁ η (exp-lam t)         = cast (exp-lam (ren η t))
                                  ((λ t′ → ren η t ≅ lam (app t′ _)) & comp-wk-ren η t)

------------------------------------------------------------------------------
