module IPC.Hilbert.Tree.TarskiSoundness where

open import IPC.Hilbert.Tree public
open import IPC.TarskiSemantics public




module NaturalSoundness where
  open NaturalSemantics public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A} → ⊢ A → ᴹ⊨ A
  eval (app t u) = (eval t) (eval u)
  eval ci        = id
  eval ck        = const
  eval cs        = ap
  eval cpair     = _,_
  eval cfst      = π₁
  eval csnd      = π₂
  eval tt        = ∙
  eval cboom     = elim𝟘
  eval cinl      = ι₁
  eval cinr      = ι₂
  eval ccase     = elim⊎


  -- Correctness of evaluation with respect to conversion.

  check : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
  check refl⇒             = refl
  check (trans⇒ p q)      = trans (check p) (check q)
  check (sym⇒ p)          = sym (check p)
  check (congapp⇒ p q)    = cong₂ _$_ (check p) (check q)
  check (congi⇒ p)        = cong id (check p)
  check (congk⇒ p q)      = cong₂ const (check p) (check q)
  check (congs⇒ p q r)    = cong₃ ap (check p) (check q) (check r)
  check (congpair⇒ p q)   = cong₂ _,_ (check p) (check q)
  check (congfst⇒ p)      = cong π₁ (check p)
  check (congsnd⇒ p)      = cong π₂ (check p)
  check (congboom⇒ p)     = cong elim𝟘 (check p)
  check (conginl⇒ p)      = cong ι₁ (check p)
  check (conginr⇒ p)      = cong ι₂ (check p)
  check (congcase⇒ p q r) = cong₃ elim⊎ (check p) (check q) (check r)
  check beta▻ₖ⇒           = refl
  check beta▻ₛ⇒           = refl
  check beta∧₁⇒           = refl
  check beta∧₂⇒           = refl
  check eta∧⇒             = refl
  check eta⊤⇒            = refl
  check beta∨₁⇒           = refl
  check beta∨₂⇒           = refl




-- Using satisfaction with a syntactic component, inspired by Coquand and Dybjer.

module CoquandDybjerSoundness where
  open CoquandDybjerSemantics (⊢_) public


  -- Completeness with respect to a particular model.

  reify : ∀ {{_ : Model}} {A} → ⊨ A → ⊢ A
  reify {A = α P}   (t , s) = t
  reify {A = A ▻ B} (t , f) = t
  reify {A = A ∧ B} (a , b) = pair (reify {A} a) (reify {B} b)
  reify {A = ⊤}    ∙       = tt
  reify {A = ⊥}    ()
  reify {A = A ∨ B} (ι₁ a)  = inl (reify {A} a)
  reify {A = A ∨ B} (ι₂ b)  = inr (reify {B} b)


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A} → ⊢ A → ᴹ⊨ A
  eval (app t u) = (eval t) $ˢ (eval u)
  eval ci        = ci , id
  eval ck        = ck , (λ a → app ck (reify a) , const a)
  eval cs        = cs , (λ f →
                     app cs (reify f) , (λ g →
                       app (app cs (reify f)) (reify g) , (λ a →
                         apˢ f g a)))
  eval cpair     = cpair , (λ a → app cpair (reify a) , (λ b → a , b))
  eval cfst      = cfst , π₁
  eval csnd      = csnd , π₂
  eval tt        = ∙
  eval cboom     = cboom , elim𝟘
  eval cinl      = cinl , ι₁
  eval cinr      = cinr , ι₂
  eval ccase     = ccase , (λ s →
                     app ccase (reify s) , (λ f →
                       app (app ccase (reify s)) (reify f) , (λ g →
                         elim⊎ˢ s f g)))


  -- Correctness of evaluation with respect to conversion.

  check : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
  check refl⇒             = refl
  check (trans⇒ p q)      = trans (check p) (check q)
  check (sym⇒ p)          = sym (check p)
  check (congapp⇒ p q)    = cong₂ _$ˢ_ (check p) (check q)
  check (congi⇒ p)        = cong id (check p)
  check (congk⇒ p q)      = cong₂ const (check p) (check q)
  check (congs⇒ p q r)    = cong₃ apˢ (check p) (check q) (check r)
  check (congpair⇒ p q)   = cong₂ _,_ (check p) (check q)
  check (congfst⇒ p)      = cong π₁ (check p)
  check (congsnd⇒ p)      = cong π₂ (check p)
  check (congboom⇒ p)     = cong elim𝟘 (check p)
  check (conginl⇒ p)      = cong ι₁ (check p)
  check (conginr⇒ p)      = cong ι₂ (check p)
  check (congcase⇒ p q r) = cong₃ elim⊎ˢ (check p) (check q) (check r)
  check beta▻ₖ⇒           = refl
  check beta▻ₛ⇒           = refl
  check beta∧₁⇒           = refl
  check beta∧₂⇒           = refl
  check eta∧⇒             = refl
  check eta⊤⇒            = refl
  check beta∨₁⇒           = refl
  check beta∨₂⇒           = refl
