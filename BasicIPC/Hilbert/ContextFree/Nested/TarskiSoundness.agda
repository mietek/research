module BasicIPC.Hilbert.ContextFree.Nested.TarskiSoundness where

open import BasicIPC.Hilbert.ContextFree.Nested public
open import BasicIPC.TarskiSemantics public


-- Soundness, or evaluation.

eval : ∀ {A} → ⊢ A → ᴹ⊨ A
eval (app t u) = (eval t) (eval u)
eval ci        = id
eval ck        = const
eval cs        = ap
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
  check (cong⇒pair p q) = cong₂ _,_ (check p) (check q)
  check (cong⇒fst p)    = cong π₁ (check p)
  check (cong⇒snd p)    = cong π₂ (check p)
  check conv⇒k          = refl
  check conv⇒s          = refl
  check conv⇒pair       = refl
  check conv⇒fst        = refl
  check conv⇒snd        = refl
  check conv⇒tt         = refl
