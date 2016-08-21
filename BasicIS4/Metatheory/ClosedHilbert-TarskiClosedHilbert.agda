module BasicIS4.Metatheory.ClosedHilbert-TarskiClosedHilbert where

open import BasicIS4.Syntax.ClosedHilbert public
open import BasicIS4.Semantics.TarskiClosedHilbert public


-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  [_] : ∀ {A} → ⊢ A → [⊢] A
  [ app t u ] = [app] [ t ] [ u ]
  [ ci ]      = [ci]
  [ ck ]      = [ck]
  [ cs ]      = [cs]
  [ box t ]   = [box] [ t ]
  [ cdist ]   = [cdist]
  [ cup ]     = [cup]
  [ cdown ]   = [cdown]
  [ cpair ]   = [cpair]
  [ cfst ]    = [cfst]
  [ csnd ]    = [csnd]
  [ tt ]      = [tt]


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A} → ⊢ A → ⊨ A
eval (app t u) = eval t ⟪$⟫ eval u
eval ci        = [ci] , id
eval ck        = [ck] , ⟪const⟫
eval cs        = [cs] , ⟪ap⟫′
eval (box t)   = [ box t ] , eval t
eval cdist     = [cdist] , _⟪◎⟫′_
eval cup       = [cup] , ⟪⇑⟫
eval cdown     = [cdown] , ⟪⇓⟫
eval cpair     = [cpair] , _⟪,⟫′_
eval cfst      = [cfst] , π₁
eval csnd      = [csnd] , π₂
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
eval✓ (congdist⋙ p q) = cong₂ _⟪◎⟫_ (eval✓ p) (eval✓ q)
eval✓ (congup⋙ p)     = cong ⟪⇑⟫ (eval✓ p)
eval✓ (congdown⋙ p)   = cong ⟪⇓⟫ (eval✓ p)
eval✓ (congpair⋙ p q) = cong₂ _,_ (eval✓ p) (eval✓ q)
eval✓ (congfst⋙ p)    = cong π₁ (eval✓ p)
eval✓ (congsnd⋙ p)    = cong π₂ (eval✓ p)
eval✓ beta▻ₖ⋙         = refl
eval✓ beta▻ₛ⋙         = refl
eval✓ beta□⋙          = refl
eval✓ eta□⋙           = refl
eval✓ beta∧₁⋙         = refl
eval✓ beta∧₂⋙         = refl
eval✓ eta∧⋙           = refl
eval✓ eta⊤⋙          = refl


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
      ; [box]   = box
      ; [cdist] = cdist
      ; [cup]   = cup
      ; [cdown] = cdown
      ; [cpair] = cpair
      ; [cfst]  = cfst
      ; [csnd]  = csnd
      ; [tt]    = tt
      }


-- Completeness with respect to all models, or quotation.

quot : ∀ {A} → ⊨ A → ⊢ A
quot s = reifyʳ s


-- Normalisation by evaluation.

norm : ∀ {A} → ⊢ A → ⊢ A
norm = quot ∘ eval


-- Correctness of normalisation with respect to conversion.

norm✓ : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⋙ t′ → norm t ≡ norm t′
norm✓ p = cong reifyʳ (eval✓ p)
