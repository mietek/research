{-# OPTIONS --sized-types #-}

module A201607.BasicIPC.Metatheory.Hilbert-TarskiGluedClosedHilbert where

open import A201607.BasicIPC.Syntax.Hilbert public
open import A201607.BasicIPC.Semantics.TarskiGluedClosedHilbert public


-- Internalisation of syntax as syntax representation in a particular model, for closed terms only.

module _ {{_ : Model}} where
  [_]₀ : ∀ {A} → ∅ ⊢ A → [⊢] A
  [ var () ]₀
  [ app t u ]₀ = [app] [ t ]₀ [ u ]₀
  [ ci ]₀      = [ci]
  [ ck ]₀      = [ck]
  [ cs ]₀      = [cs]
  [ cpair ]₀   = [cpair]
  [ cfst ]₀    = [cfst]
  [ csnd ]₀    = [csnd]
  [ unit ]₀    = [unit]


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ ⟪$⟫ eval u γ
eval ci        γ = [ci] ⅋ I
eval ck        γ = [ck] ⅋ ⟪K⟫
eval cs        γ = [cs] ⅋ ⟪S⟫′
eval cpair     γ = [cpair] ⅋ _⟪,⟫′_
eval cfst      γ = [cfst] ⅋ π₁
eval csnd      γ = [csnd] ⅋ π₂
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
      { ⊩ᵅ_    = λ P → ∅ ⊢ α P
      ; [⊢]_   = ∅ ⊢_
      ; [app]   = app
      ; [ci]    = ci
      ; [ck]    = ck
      ; [cs]    = cs
      ; [cpair] = cpair
      ; [cfst]  = cfst
      ; [csnd]  = csnd
      ; [unit]  = unit
      }


-- Completeness with respect to all models, or quotation, for closed terms only.

quot₀ : ∀ {A} → ∅ ⊨ A → ∅ ⊢ A
quot₀ t = reifyʳ (t ∙)


-- Normalisation by evaluation, for closed terms only.

norm₀ : ∀ {A} → ∅ ⊢ A → ∅ ⊢ A
norm₀ = quot₀ ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
