module BasicIPC.Gentzen.TarskiSoundness where

open import BasicIPC.TarskiSemantics public
open import BasicIPC.Gentzen public


-- Soundness, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ a → eval t (γ , a)
eval (app t u)  γ = (eval t γ) (eval u γ)
eval (pair t u) γ = eval t γ , eval u γ
eval (fst t)    γ = π₁ (eval t γ)
eval (snd t)    γ = π₂ (eval t γ)
eval tt         γ = ∙


-- TODO: Correctness with respect to conversion.

-- module _ {{_ : Model}} where
--   coco : ∀ {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
--   coco refl⇒           = refl
--   coco (trans⇒ p q)    = trans (coco p) (coco q)
--   coco (sym⇒ p)        = sym (coco p)
--   coco (cong⇒lam p)    = cong (λ f γ a → f (γ , a)) (coco p)
--   coco (cong⇒app p q)  = cong₂ (λ f g γ → (f γ) (g γ)) (coco p) (coco q)
--   coco (cong⇒pair p q) = cong₂ (λ f g γ → f γ , g γ) (coco p) (coco q)
--   coco (cong⇒fst p)    = cong (λ f γ → π₁ (f γ)) (coco p)
--   coco (cong⇒snd p)    = cong (λ f γ → π₂ (f γ)) (coco p)
--   coco conv⇒lam        = {!refl!}
--   coco conv⇒app        = {!refl!}
--   coco conv⇒pair       = refl
--   coco conv⇒fst        = refl
--   coco conv⇒snd        = refl
--   coco conv⇒tt         = refl
