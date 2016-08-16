module New.BasicIS4.Metatheory.ClosedHilbert-TarskiGabbayNanevski where

open import New.BasicIS4.Syntax.ClosedHilbert public
open import New.BasicIS4.Semantics.TarskiGabbayNanevski public

open SyntacticComponent (⊢_) (app) (box) public


-- Soundness with respect to all models, or evaluation.

eval : ∀ {A} → ⊢ A → ᴹ⊨ A
eval (app t u) = (eval t) (eval u)
eval ci        = id
eval ck        = const
eval cs        = ap
eval (box t)   = t , eval t
eval cdist     = distˢ
eval cup       = upˢ
eval cdown     = downˢ
eval cpair     = _,_
eval cfst      = π₁
eval csnd      = π₂
eval tt        = ∙


-- Correctness of evaluation with respect to conversion.

check : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
check refl⇒           = refl
check (trans⇒ p q)    = trans (check p) (check q)
check (sym⇒ p)        = sym (check p)
check (congapp⇒ p q)  = cong₂ _$_ (check p) (check q)
check (congi⇒ p)      = cong id (check p)
check (congk⇒ p q)    = cong₂ const (check p) (check q)
check (congs⇒ p q r)  = cong₃ ap (check p) (check q) (check r)
check (congdist⇒ p q) = cong₂ distˢ (check p) (check q)
check (congup⇒ p)     = cong upˢ (check p)
check (congdown⇒ p)   = cong downˢ (check p)
check (congpair⇒ p q) = cong₂ _,_ (check p) (check q)
check (congfst⇒ p)    = cong π₁ (check p)
check (congsnd⇒ p)    = cong π₂ (check p)
check beta▻ₖ⇒         = refl
check beta▻ₛ⇒         = refl
check beta□⇒          = refl
check eta□⇒           = refl
check beta∧₁⇒         = refl
check beta∧₂⇒         = refl
check eta∧⇒           = refl
check eta⊤⇒          = refl
