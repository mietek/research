module IPC.Hilbert.TreeWithContext.TarskiSoundness where

open import IPC.Hilbert.TreeWithContext public
open import IPC.TarskiSemantics public




module NaturalSoundness where
  open NaturalSemantics public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)   γ = lookup i γ
  eval (app t u) γ = (eval t γ) (eval u γ)
  eval ci        γ = id
  eval ck        γ = const
  eval cs        γ = ap
  eval cpair     γ = _,_
  eval cfst      γ = π₁
  eval csnd      γ = π₂
  eval tt        γ = ∙
  eval cboom     γ = elim𝟘
  eval cinl      γ = ι₁
  eval cinr      γ = ι₂
  eval ccase     γ = elim⊎


  -- Correctness of evaluation with respect to conversion.

  check : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
  check refl⇒                         = refl
  check (trans⇒ p q)                  = trans (check p) (check q)
  check (sym⇒ p)                      = sym (check p)
  check (congapp⇒ {A} {B} p q)        = cong₂ (_$ˢᶜ_ {A} {B}) (check p) (check q)
  check (congi⇒ p)                    = cong id (check p)
  check (congk⇒ p q)                  = cong₂ const (check p) (check q)
  check (congs⇒ {A} {B} {C} p q r)    = cong₃ (apˢᶜ {A} {B} {C}) (check p) (check q) (check r)
  check (congpair⇒ {A} {B} p q)       = cong₂ (_,ˢᶜ_ {A} {B}) (check p) (check q)
  check (congfst⇒ {A} {B} p)          = cong (π₁ˢᶜ {A} {B}) (check p)
  check (congsnd⇒ {A} {B} p)          = cong (π₂ˢᶜ {A} {B}) (check p)
  check (congboom⇒ {C} p)             = cong (elim𝟘ˢᶜ {C}) (check p)
  check (conginl⇒ {A} {B} p)          = cong (ι₁ˢᶜ {A} {B}) (check p)
  check (conginr⇒ {A} {B} p)          = cong (ι₂ˢᶜ {A} {B}) (check p)
  check (congcase⇒ {A} {B} {C} p q r) = cong₃ (elim⊎ˢᶜ {A} {B} {C}) (check p) (check q) (check r)
  check beta▻ₖ⇒                       = refl
  check beta▻ₛ⇒                       = refl
  check beta∧₁⇒                       = refl
  check beta∧₂⇒                       = refl
  check eta∧⇒                         = refl
  check eta⊤⇒                        = refl
  check beta∨₁⇒                       = refl
  check beta∨₂⇒                       = refl




-- Using satisfaction with a syntactic component, inspired by Coquand and Dybjer.

module CoquandDybjerSoundness where
  open CoquandDybjerSemantics (⌀ ⊢_) public


  -- Completeness with respect to a particular model.

  reify : ∀ {{_ : Model}} {A} → ⊨ A → ⌀ ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} (t , f) = t
  reify {A ∧ B} (a , b) = pair (reify {A} a) (reify {B} b)
  reify {⊤}    ∙       = tt
  reify {⊥}    ()
  reify {A ∨ B} (ι₁ a)  = inl (reify {A} a)
  reify {A ∨ B} (ι₂ b)  = inr (reify {B} b)


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)   γ = lookup i γ
  eval (app t u) γ = (eval t γ) $ˢ (eval u γ)
  eval ci        γ = ci , id
  eval ck        γ = ck , (λ a → app ck (reify a) , const a)
  eval cs        γ = cs , (λ f →
                       app cs (reify f) , (λ g →
                         app (app cs (reify f)) (reify g) , (λ a →
                           apˢ f g a)))
  eval cpair     γ = cpair , (λ a → app cpair (reify a) , (λ b → a , b))
  eval cfst      γ = cfst , π₁
  eval csnd      γ = csnd , π₂
  eval tt        γ = ∙
  eval cboom     γ = cboom , elim𝟘
  eval cinl      γ = cinl , ι₁
  eval cinr      γ = cinr , ι₂
  eval ccase     γ = ccase , (λ s →
                       app ccase (reify s) , (λ f →
                         app (app ccase (reify s)) (reify f) , (λ g →
                           elim⊎ˢ s f g)))


  -- Correctness of evaluation with respect to conversion.

  check : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
  check refl⇒                         = refl
  check (trans⇒ p q)                  = trans (check p) (check q)
  check (sym⇒ p)                      = sym (check p)
  check (congapp⇒ p q)                = cong₂ _$ˢᶜ_ (check p) (check q)
  check (congi⇒ p)                    = cong id (check p)
  check (congk⇒ p q)                  = cong₂ const (check p) (check q)
  check (congs⇒ p q r)                = cong₃ apˢᶜ (check p) (check q) (check r)
  check (congpair⇒ {A} {B} p q)       = cong₂ (_,ˢᶜ_ {A} {B}) (check p) (check q)
  check (congfst⇒ {A} {B} p)          = cong (π₁ˢᶜ {A} {B}) (check p)
  check (congsnd⇒ {A} {B} p)          = cong (π₂ˢᶜ {A} {B}) (check p)
  check (congboom⇒ {C} p)             = cong (elim𝟘ˢᶜ {C}) (check p)
  check (conginl⇒ {A} {B} p)          = cong (ι₁ˢᶜ {A} {B}) (check p)
  check (conginr⇒ {A} {B} p)          = cong (ι₂ˢᶜ {A} {B}) (check p)
  check (congcase⇒ {A} {B} {C} p q r) = cong₃ (elim⊎ˢᶜ {A} {B} {C}) (check p) (check q) (check r)
  check beta▻ₖ⇒                       = refl
  check beta▻ₛ⇒                       = refl
  check beta∧₁⇒                       = refl
  check beta∧₂⇒                       = refl
  check eta∧⇒                         = refl
  check eta⊤⇒                        = refl
  check beta∨₁⇒                       = refl
  check beta∨₂⇒                       = refl
