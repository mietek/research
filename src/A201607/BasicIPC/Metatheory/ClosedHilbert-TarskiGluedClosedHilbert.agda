{-# OPTIONS --sized-types #-}

module A201607.BasicIPC.Metatheory.ClosedHilbert-TarskiGluedClosedHilbert where

open import A201607.BasicIPC.Syntax.ClosedHilbert public
open import A201607.BasicIPC.Semantics.TarskiGluedClosedHilbert public


-- Internalisation of syntax as syntax representation in a particular model.

module _ {{_ : Model}} where
  [_] : ∀ {A} → ⊢ A → [⊢] A
  [ app t u ] = [app] [ t ] [ u ]
  [ ci ]      = [ci]
  [ ck ]      = [ck]
  [ cs ]      = [cs]
  [ cpair ]   = [cpair]
  [ cfst ]    = [cfst]
  [ csnd ]    = [csnd]
  [ unit ]    = [unit]


-- Soundness with respect to all models, or evaluation, for closed terms only.

eval₀ : ∀ {A} → ⊢ A → ⊨ A
eval₀ (app t u) = eval₀ t ⟪$⟫ eval₀ u
eval₀ ci        = [ci] ⅋ I
eval₀ ck        = [ck] ⅋ ⟪K⟫
eval₀ cs        = [cs] ⅋ ⟪S⟫′
eval₀ cpair     = [cpair] ⅋ _⟪,⟫′_
eval₀ cfst      = [cfst] ⅋ π₁
eval₀ csnd      = [csnd] ⅋ π₂
eval₀ unit      = ∙


-- Correctness of evaluation with respect to conversion.

eval₀✓ : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⋙ t′ → eval₀ t ≡ eval₀ t′
eval₀✓ refl⋙           = refl
eval₀✓ (trans⋙ p q)    = trans (eval₀✓ p) (eval₀✓ q)
eval₀✓ (sym⋙ p)        = sym (eval₀✓ p)
eval₀✓ (congapp⋙ p q)  = cong² _⟪$⟫_ (eval₀✓ p) (eval₀✓ q)
eval₀✓ (congi⋙ p)      = cong I (eval₀✓ p)
eval₀✓ (congk⋙ p q)    = cong² K (eval₀✓ p) (eval₀✓ q)
eval₀✓ (congs⋙ p q r)  = cong³ ⟪S⟫ (eval₀✓ p) (eval₀✓ q) (eval₀✓ r)
eval₀✓ (congpair⋙ p q) = cong² _,_ (eval₀✓ p) (eval₀✓ q)
eval₀✓ (congfst⋙ p)    = cong π₁ (eval₀✓ p)
eval₀✓ (congsnd⋙ p)    = cong π₂ (eval₀✓ p)
eval₀✓ beta▻ₖ⋙         = refl
eval₀✓ beta▻ₛ⋙         = refl
eval₀✓ beta∧₁⋙         = refl
eval₀✓ beta∧₂⋙         = refl
eval₀✓ eta∧⋙           = refl
eval₀✓ eta⊤⋙          = refl


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { ⊩ᵅ_    = λ P → ⊢ α P
      ; [⊢]_   = ⊢_
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

quot₀ : ∀ {A} → ⊨ A → ⊢ A
quot₀ s = reifyʳ s


-- Normalisation by evaluation, for closed terms only.

norm₀ : ∀ {A} → ⊢ A → ⊢ A
norm₀ = quot₀ ∘ eval₀


-- Correctness of normalisation with respect to conversion.

norm₀✓ : ∀ {A} {t t′ : ⊢ A} → t ⋙ t′ → norm₀ t ≡ norm₀ t′
norm₀✓ p = cong reifyʳ (eval₀✓ p)
