module BasicIS4.ContextFree.Hilbert.Nested.TarskiSoundness where

open import BasicIS4.ContextFree.Hilbert.Nested public
open import BasicIS4.TarskiSemantics public
open TruthWithClosedBox (⊢_)


-- Soundness, or evaluation.

eval : ∀ {A} → ⊢ A → ᴹ⊨ A
eval (app t u) = (eval t) (eval u)
eval ci        = id
eval ck        = const
eval cs        = ap
eval (box t)   = t , eval t
eval cdist     = λ {(t , f) (u , a) → app t u , f a}
eval cup       = λ {(t , a) → box t , (t , a)}
eval cdown     = λ {(t , a) → a}
eval cpair     = _,_
eval cfst      = π₁
eval csnd      = π₂
eval tt        = ∙


-- Correctness of evaluation with respect to conversion.

module _ {{_ : Model}} where
  check : ∀ {A} {t t′ : ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
  check refl⇒           = refl
  check (trans⇒ p q)    = trans (check p) (check q)
  check (sym⇒ p)        = sym (check p)
  check (cong⇒app p q)  = cong₂ _$_ (check p) (check q)
  check (cong⇒dist p q) = cong₂ (λ {(t , f) (u , a) →
                             app t u , f a}) (check p) (check q)
  check (cong⇒up p)     = cong (λ {(t , a) → box t , (t , a)}) (check p)
  check (cong⇒down p)   = cong (λ {(t , a) → a}) (check p)
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
