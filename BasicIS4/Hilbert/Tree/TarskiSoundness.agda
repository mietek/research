module BasicIS4.Hilbert.Tree.TarskiSoundness where

open import BasicIS4.Hilbert.Tree public
open import BasicIS4.TarskiSemantics public




-- Using satisfaction with a syntactic component, inspired by Gabbay and Nanevski.

module GabbayNanevskiSoundness where
  open GabbayNanevskiSemantics (⊢_) public


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A} → ⊢ A → ᴹ⊨ A
  eval (app t u) = (eval t) (eval u)
  eval ci        = id
  eval ck        = const
  eval cs        = ap
  eval (box t)   = t , eval t
  eval cdist     = λ { (t , f) (u , a) → app t u , f a }
  eval cup       = λ { (t , a) → box t , (t , a) }
  eval cdown     = λ { (t , a) → a }
  eval cpair     = _,_
  eval cfst      = π₁
  eval csnd      = π₂
  eval tt        = ∙


  -- Correctness of evaluation with respect to conversion.

  check : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
  check refl⇒           = refl
  check (trans⇒ p q)    = trans (check p) (check q)
  check (sym⇒ p)        = sym (check p)
  check (cong⇒app p q)  = cong₂ _$_ (check p) (check q)
  check (cong⇒dist p q) = cong₂ (λ { (t , f) (u , a) →
                             app t u , f a }) (check p) (check q)
  check (cong⇒up p)     = cong (λ { (t , a) → box t , (t , a) }) (check p)
  check (cong⇒down p)   = cong (λ { (t , a) → a }) (check p)
  check (cong⇒pair p q) = cong₂ _,_ (check p) (check q)
  check (cong⇒fst p)    = cong π₁ (check p)
  check (cong⇒snd p)    = cong π₂ (check p)
  check conv⇒k          = refl
  check conv⇒s          = refl
  check conv⇒up         = refl
  check conv⇒down       = refl
  check conv⇒pair       = refl
  check conv⇒fst        = refl
  check conv⇒snd        = refl
  check conv⇒tt         = refl




-- Using satisfaction with a syntactic component, inspired by Coquand and Dybjer.

module CoquandDybjerSoundness where
  open CoquandDybjerSemantics (⊢_) public


  -- Completeness with respect to a particular model.

  reify : ∀ {{_ : Model}} {A} → ⊨ A → ⊢ A
  reify {α P}   (t , s) = t
  reify {A ▻ B} (t , f) = t
  reify {□ A}   (t , a) = box t
  reify {A ∧ B} (a , b) = pair (reify {A} a) (reify {B} b)
  reify {⊤}    ∙       = tt


  -- Soundness with respect to all models, or evaluation.

  eval : ∀ {A} → ⊢ A → ᴹ⊨ A
  eval (app t u) = (eval t) $ˢ (eval u)
  eval ci        = ci , id
  eval ck        = ck , (λ a → app ck (reify a) , const a)
  eval cs        = cs , (λ f →
                     app cs (reify f) , (λ g →
                       app (app cs (reify f)) (reify g) , (λ a →
                         (f $ˢ a) $ˢ (g $ˢ a))))
  eval (box t)   = t , eval t
  eval cdist     = cdist , (λ { (t , f) →
                     app cdist (box t) , (λ { (u , a) →
                       app t u , f $ˢ a }) })
  eval cup       = cup , (λ { (t , a) → box t , (t , a) })
  eval cdown     = cdown , (λ { (t , a) → a })
  eval cpair     = cpair , (λ a → app cpair (reify a) , (λ b → a , b))
  eval cfst      = cfst , π₁
  eval csnd      = csnd , π₂
  eval tt        = ∙


  -- Correctness of evaluation with respect to conversion.

  check : ∀ {{_ : Model}} {A} {t t′ : ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
  check refl⇒           = refl
  check (trans⇒ p q)    = trans (check p) (check q)
  check (sym⇒ p)        = sym (check p)
  check (cong⇒app p q)  = cong₂ _$ˢ_ (check p) (check q)
  check (cong⇒dist p q) = cong₂ (λ { (t , (t′ , f)) (u , a) →
                             app t u , f a }) (check p) (check q)
  check (cong⇒up p)     = cong (λ { (t , a) → box t , (t , a) }) (check p)
  check (cong⇒down p)   = cong (λ { (t , a) → a }) (check p)
  check (cong⇒pair p q) = cong₂ _,_ (check p) (check q)
  check (cong⇒fst p)    = cong π₁ (check p)
  check (cong⇒snd p)    = cong π₂ (check p)
  check conv⇒k          = refl
  check conv⇒s          = refl
  check conv⇒up         = refl
  check conv⇒down       = refl
  check conv⇒pair       = refl
  check conv⇒fst        = refl
  check conv⇒snd        = refl
  check conv⇒tt         = refl
