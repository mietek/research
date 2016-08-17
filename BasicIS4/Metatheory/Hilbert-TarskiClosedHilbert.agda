module BasicIS4.Metatheory.Hilbert-TarskiClosedHilbert where

open import BasicIS4.Syntax.Hilbert public
open import BasicIS4.Semantics.TarskiClosedHilbert public


-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  reflect[] : ∀ {A} → ⌀ ⊢ A → [ A ]
  reflect[] (var ())
  reflect[] (app t u) = [app] (reflect[] t) (reflect[] u)
  reflect[] ci        = [ci]
  reflect[] ck        = [ck]
  reflect[] cs        = [cs]
  reflect[] (box t)   = [box] (reflect[] t)
  reflect[] cdist     = [cdist]
  reflect[] cup       = [cup]
  reflect[] cdown     = [cdown]
  reflect[] cpair     = [cpair]
  reflect[] cfst      = [cfst]
  reflect[] csnd      = [csnd]
  reflect[] tt        = [tt]


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → ∀ᴹ⊨ Γ ⇒ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ ⟪$⟫ eval u γ
eval ci        γ = [ci] , id
eval ck        γ = [ck] , ⟪const⟫
eval cs        γ = [cs] , ⟪ap⟫′
eval (box t)   γ = reflect[] t , eval t ∙
eval cdist     γ = [cdist] , _⟪◎⟫′_
eval cup       γ = [cup] , ⟪⇑⟫
eval cdown     γ = [cdown] , ⟪⇓⟫
eval cpair     γ = [cpair] , _⟪,⟫′_
eval cfst      γ = [cfst] , π₁
eval csnd      γ = [csnd] , π₂
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

instance
  canon : Model
  canon = record
    { ⊨ᵅ_    = λ P → ⌀ ⊢ α P
    ; [_]     = ⌀ ⊢_
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


-- Completeness with respect to all models, or quotation, for closed terms only.

quot₀ : ∀ {A} → ∀ᴹ⊨ ⌀ ⇒ A → ⌀ ⊢ A
quot₀ t = reify[] (t ∙)


-- Normalisation by evaluation, for closed terms only.

norm₀ : ∀ {A} → ⌀ ⊢ A → ⌀ ⊢ A
norm₀ = quot₀ ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
