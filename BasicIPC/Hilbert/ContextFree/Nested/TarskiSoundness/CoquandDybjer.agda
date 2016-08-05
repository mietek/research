module BasicIPC.Hilbert.ContextFree.Nested.TarskiSoundness.CoquandDybjer where

open import BasicIPC.Hilbert.ContextFree.Nested public
open import BasicIPC.TarskiSemantics.CoquandDybjer public
open Glueing (⊢_) public


-- Completeness with respect to a particular model.

module _ {{_ : Model}} where
  reify : ∀ {A} → ⊨ A → ⊢ A
  reify {α P}   s = π₁ s
  reify {A ▻ B} s = π₁ s
  reify {A ∧ B} s = pair (reify {A} (π₁ s)) (reify {B} (π₂ s))
  reify {⊤}    s = tt

  _$ˢ_ : ∀ {A B} → (⊢ A ▻ B) × (⊨ A → ⊨ B) → ⊨ A → ⊨ B
  (t , f) $ˢ a = f a


-- Soundness, or evaluation.

eval : ∀ {A} → ⊢ A → ᴹ⊨ A
eval (app t u) = (eval t) $ˢ (eval u)
eval ci        = ci , id
eval ck        = ck , (λ a → app ck (reify a) , const a)
eval cs        = cs , (λ f →
                   app cs (reify f) , (λ g →
                     app (app cs (reify f)) (reify g) , (λ a →
                       (f $ˢ a) $ˢ (g $ˢ a))))
eval cpair     = cpair , (λ a → app cpair (reify a) , (λ b → a , b))
eval cfst      = cfst , π₁
eval csnd      = csnd , π₂
eval tt        = ∙


-- Correctness of evaluation with respect to conversion.

module _ {{_ : Model}} where
  check : ∀ {A} {t t′ : ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
  check refl⇒           = refl
  check (trans⇒ p q)    = trans (check p) (check q)
  check (sym⇒ p)        = sym (check p)
  check (cong⇒app p q)  = cong₂ _$ˢ_ (check p) (check q)
  check (cong⇒pair p q) = cong₂ _,_ (check p) (check q)
  check (cong⇒fst p)    = cong π₁ (check p)
  check (cong⇒snd p)    = cong π₂ (check p)
  check conv⇒k          = refl
  check conv⇒s          = refl
  check conv⇒pair       = refl
  check conv⇒fst        = refl
  check conv⇒snd        = refl
  check conv⇒tt         = refl
