module BasicIS4.Metatheory.ClosedHilbert-TarskiClosedHilbert where

open import BasicIS4.Syntax.ClosedHilbert public
open import BasicIS4.Semantics.TarskiClosedHilbert public


-- Soundness with respect to the syntax representation in a particular model.

module _ {{_ : Model}} where
  reflect[] : ∀ {A} → ⊢ A → [ A ]
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

eval : ∀ {A} → ⊢ A → ⊨ A
eval (app t u) = eval t ⟪$⟫ eval u
eval ci        = [ci] , id
eval ck        = [ck] , ⟪const⟫
eval cs        = [cs] , ⟪ap⟫′
eval (box t)   = reflect[] (box t) , eval t
eval cdist     = [cdist] , _⟪◎⟫′_
eval cup       = [cup] , ⟪⇑⟫
eval cdown     = [cdown] , ⟪⇓⟫
eval cpair     = [cpair] , _⟪,⟫′_
eval cfst      = [cfst] , π₁
eval csnd      = [csnd] , π₂
eval tt        = ∙


-- Correctness of evaluation with respect to conversion.

check : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⋙ t′ → eval t ≡ eval t′
check refl⋙           = refl
check (trans⋙ p q)    = trans (check p) (check q)
check (sym⋙ p)        = sym (check p)
check (congapp⋙ p q)  = cong₂ _⟪$⟫_ (check p) (check q)
check (congi⋙ p)      = cong id (check p)
check (congk⋙ p q)    = cong₂ const (check p) (check q)
check (congs⋙ p q r)  = cong₃ ⟪ap⟫ (check p) (check q) (check r)
check (congdist⋙ p q) = cong₂ _⟪◎⟫_ (check p) (check q)
check (congup⋙ p)     = cong ⟪⇑⟫ (check p)
check (congdown⋙ p)   = cong ⟪⇓⟫ (check p)
check (congpair⋙ p q) = cong₂ _,_ (check p) (check q)
check (congfst⋙ p)    = cong π₁ (check p)
check (congsnd⋙ p)    = cong π₂ (check p)
check beta▻ₖ⋙         = refl
check beta▻ₛ⋙         = refl
check beta□⋙          = refl
check eta□⋙           = refl
check beta∧₁⋙         = refl
check beta∧₂⋙         = refl
check eta∧⋙           = refl
check eta⊤⋙          = refl


-- The canonical model.

instance
  canon : Model
  canon = record
    { ⊩ᵅ_    = λ P → ⊢ α P
    ; [_]     = ⊢_
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
quot s = reify[] s


-- Normalisation by evaluation.

norm : ∀ {A} → ⊢ A → ⊢ A
norm = quot ∘ eval


-- Correctness of normalisation with respect to conversion.

check′ : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⋙ t′ → norm t ≡ norm t′
check′ p = cong reify[] (check p)
