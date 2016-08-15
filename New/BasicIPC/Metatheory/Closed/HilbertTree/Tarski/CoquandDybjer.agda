module New.BasicIPC.Metatheory.Closed.HilbertTree.Tarski.CoquandDybjer where

open import New.BasicIPC.Syntax.Closed.HilbertTree public
open import New.BasicIPC.Semantics.Tarski.CoquandDybjer public

open SyntacticComponent (⊢_) public


-- Completeness with respect to a particular model.

reify : ∀ {{_ : Model}} {A} → ⊨ A → ⊢ A
reify {α P}   (t , s) = t
reify {A ▻ B} (t , f) = t
reify {A ∧ B} (a , b) = app (app cpair (reify a)) (reify b)
reify {⊤}    ∙       = tt


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A} → ⊢ A → ᴹ⊨ A
eval (app t u) = (eval t) $ˢ (eval u)
eval ci        = ci , id
eval ck        = ck , λ a →
                   app ck (reify a) ,
                     const a
eval cs        = cs , λ f →
                   app cs (reify f) , λ g →
                     app (app cs (reify f)) (reify g) , λ a →
                       apˢ f g a
eval cpair     = cpair , λ a →
                   app cpair (reify a) , λ b →
                     a , b
eval cfst      = cfst , π₁
eval csnd      = csnd , π₂
eval tt        = ∙


-- Correctness of evaluation with respect to conversion.

check : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
check refl⇒           = refl
check (trans⇒ p q)    = trans (check p) (check q)
check (sym⇒ p)        = sym (check p)
check (congapp⇒ p q)  = cong₂ _$ˢ_ (check p) (check q)
check (congi⇒ p)      = cong id (check p)
check (congk⇒ p q)    = cong₂ const (check p) (check q)
check (congs⇒ p q r)  = cong₃ apˢ (check p) (check q) (check r)
check (congpair⇒ p q) = cong₂ _,_ (check p) (check q)
check (congfst⇒ p)    = cong π₁ (check p)
check (congsnd⇒ p)    = cong π₂ (check p)
check beta▻ₖ⇒         = refl
check beta▻ₛ⇒         = refl
check beta∧₁⇒         = refl
check beta∧₂⇒         = refl
check eta∧⇒           = refl
check eta⊤⇒          = refl


-- The canonical model.

instance
  canon : Model
  canon = record
    { ⊨ᵅ_ = λ P → ⊢ α P
    }


-- Completeness with respect to all models, or quotation.

quot : ∀ {A} → ᴹ⊨ A → ⊢ A
quot t = reify t


-- Normalisation by evaluation.

norm : ∀ {A} → ⊢ A → ⊢ A
norm = quot ∘ eval


-- Correctness of normalisation with respect to conversion.

check′ : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⇒ t′ → norm t ≡ norm t′
check′ p = cong reify (check p)
