module BasicIS4.Hilbert.TreeWithContext.TarskiSoundness where

open import BasicIS4.Hilbert.TreeWithContext public
open import BasicIS4.TarskiSemantics public




-- Using satisfaction with a syntactic component, inspired by Gabbay and Nanevski.

module GabbayNanevskiSoundness where
  open GabbayNanevskiSemantics (⌀ ⊢_) (app) (box) public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)   γ = lookup i γ
  eval (app t u) γ = (eval t γ) (eval u γ)
  eval ci        γ = id
  eval ck        γ = const
  eval cs        γ = ap
  eval (box t)   γ = t , eval t ∙
  eval cdist     γ = distˢ
  eval cup       γ = upˢ
  eval cdown     γ = downˢ
  eval cpair     γ = _,_
  eval cfst      γ = π₁
  eval csnd      γ = π₂
  eval tt        γ = ∙


  -- Correctness of evaluation with respect to conversion.

  check : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
  check refl⇒                      = refl
  check (trans⇒ p q)               = trans (check p) (check q)
  check (sym⇒ p)                   = sym (check p)
  check (congapp⇒ {A} {B} p q)     = cong₂ (_$ˢᶜ_ {A} {B}) (check p) (check q)
  check (congi⇒ p)                 = cong id (check p)
  check (congk⇒ p q)               = cong₂ const (check p) (check q)
  check (congs⇒ {A} {B} {C} p q r) = cong₃ (apˢᶜ {A} {B} {C}) (check p) (check q) (check r)
  check (congdist⇒ p q)            = cong₂ distˢᶜ (check p) (check q)
  check (congup⇒ p)                = cong upˢᶜ (check p)
  check (congdown⇒ p)              = cong downˢᶜ (check p)
  check (congpair⇒ {A} {B} p q)    = cong₂ (_,ˢᶜ_ {A} {B}) (check p) (check q)
  check (congfst⇒ {A} {B} p)       = cong (π₁ˢᶜ {A} {B}) (check p)
  check (congsnd⇒ {A} {B} p)       = cong (π₂ˢᶜ {A} {B}) (check p)
  check beta▻ₖ⇒                    = refl
  check beta▻ₛ⇒                    = refl
  check beta∧₁⇒                    = refl
  check beta∧₂⇒                    = refl
  check eta∧⇒                      = refl
  check eta⊤⇒                     = refl




-- Using satisfaction with a syntactic component, inspired by Coquand and Dybjer.

module CoquandDybjerSoundness where
  open CoquandDybjerSemantics (⌀ ⊢_) (app) (box) public


  -- Completeness with respect to a particular model.

  reify : ∀ {{_ : Model}} {A} → ⊨ A → ⌀ ⊢ A
  reify {α P}   (t , s)  = t
  reify {A ▻ B} (t , f)  = t
  reify {□ A}   (t , □f) = box t
  reify {A ∧ B} (a , b)  = pair (reify {A} a) (reify {B} b)
  reify {⊤}    ∙        = tt


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
  eval (var i)   γ = lookup i γ
  eval (app t u) γ = (eval t γ) $ˢ (eval u γ)
  eval ci        γ = ci , id
  eval ck        γ = ck , (λ a →
                       app ck (reify a) ,
                         const a)
  eval cs        γ = cs , (λ f →
                       app cs (reify f) , (λ g →
                         app (app cs (reify f)) (reify g) , (λ a →
                           apˢ f g a)))
  eval (box t)   γ = t , eval t ∙
  eval cdist     γ = cdist , (λ □f →
                       app cdist (reify □f) , (λ □a →
                         distˢ′ □f □a))
  eval cup       γ = cup , upˢ
  eval cdown     γ = cdown , downˢ
  eval cpair     γ = cpair , (λ a →
                       app cpair (reify a) , (λ b →
                         a , b))
  eval cfst      γ = cfst , π₁
  eval csnd      γ = csnd , π₂
  eval tt        γ = ∙


  -- Correctness of evaluation with respect to conversion.

  check : ∀ {{_ : Model}} {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
  check refl⇒                   = refl
  check (trans⇒ p q)            = trans (check p) (check q)
  check (sym⇒ p)                = sym (check p)
  check (congapp⇒ p q)          = cong₂ _$ˢᶜ_ (check p) (check q)
  check (congi⇒ p)              = cong id (check p)
  check (congk⇒ p q)            = cong₂ const (check p) (check q)
  check (congs⇒ p q r)          = cong₃ apˢᶜ (check p) (check q) (check r)
  check (congdist⇒ p q)         = cong₂ distˢᶜ′ (check p) (check q)
  check (congup⇒ p)             = cong upˢᶜ (check p)
  check (congdown⇒ p)           = cong downˢᶜ (check p)
  check (congpair⇒ {A} {B} p q) = cong₂ (_,ˢᶜ_ {A} {B}) (check p) (check q)
  check (congfst⇒ {A} {B} p)    = cong (π₁ˢᶜ {A} {B}) (check p)
  check (congsnd⇒ {A} {B} p)    = cong (π₂ˢᶜ {A} {B}) (check p)
  check beta▻ₖ⇒                 = refl
  check beta▻ₛ⇒                 = refl
  check beta∧₁⇒                 = refl
  check beta∧₂⇒                 = refl
  check eta∧⇒                   = refl
  check eta⊤⇒                  = refl
