module BasicIPC.Metatheory.Hilbert-TarskiCoquandDybjerMk1 where

open import BasicIPC.Syntax.Hilbert public
open import BasicIPC.Semantics.TarskiCoquandDybjerMk1 public


-- Completeness with respect to a particular model.

reify : ∀ {{_ : Model}} {A} → ⊨ A → [ A ]
reify {α P}   (t , s) = t
reify {A ▻ B} (t , f) = t
reify {A ∧ B} (a , b) = [app] ([app] [cpair] (reify {A} a)) (reify {B} b)
reify {⊤}    ∙       = [tt]


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → ∀ᴹ⊨ Γ ⇒ A
eval (var i)   γ = lookup i γ
eval (app t u) γ = eval t γ ⟪$⟫ eval u γ
eval ci        γ = [ci] , id
eval ck        γ = [ck] , λ a →
                     [app] [ck] (reify a) , const a
eval cs        γ = [cs] , λ f →
                     [app] [cs] (reify f) , λ g →
                       [app] ([app] [cs] (reify f)) (reify g) , ⟪ap⟫ f g
eval cpair     γ = [cpair] , λ a →
                     [app] [cpair] (reify a) , _,_ a
eval cfst      γ = [cfst] , π₁
eval csnd      γ = [csnd] , π₂
eval tt        γ = ∙


-- Correctness of evaluation with respect to conversion.

check : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
check refl⇒                   = refl
check (trans⇒ p q)            = trans (check p) (check q)
check (sym⇒ p)                = sym (check p)
check (congapp⇒ p q)          = cong₂ _⟦$⟧_ (check p) (check q)
check (congi⇒ p)              = cong id (check p)
check (congk⇒ p q)            = cong₂ const (check p) (check q)
check (congs⇒ p q r)          = cong₃ ⟦ap⟧ (check p) (check q) (check r)
check (congpair⇒ {A} {B} p q) = cong₂ (_⟦,⟧_ {A} {B}) (check p) (check q)
check (congfst⇒ {A} {B} p)    = cong (⟦π₁⟧ {A} {B}) (check p)
check (congsnd⇒ {A} {B} p)    = cong (⟦π₂⟧ {A} {B}) (check p)
check beta▻ₖ⇒                 = refl
check beta▻ₛ⇒                 = refl
check beta∧₁⇒                 = refl
check beta∧₂⇒                 = refl
check eta∧⇒                   = refl
check eta⊤⇒                  = refl


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
    ; [cpair] = cpair
    ; [cfst]  = cfst
    ; [csnd]  = csnd
    ; [tt]    = tt
    }


-- Completeness with respect to all models, or quotation.

-- TODO: Can we do better here?
quot₀ : ∀ {A} → ∀ᴹ⊨ ⌀ ⇒ A → ⌀ ⊢ A
quot₀ t = reify (t ∙)


-- Normalisation by evaluation.

-- TODO: Can we do better here?
norm₀ : ∀ {A} → ⌀ ⊢ A → ⌀ ⊢ A
norm₀ = quot₀ ∘ eval


-- TODO: Correctness of normalisation with respect to conversion.
