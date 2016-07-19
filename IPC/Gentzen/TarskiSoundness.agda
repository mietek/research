module IPC.Gentzen.TarskiSoundness where

open import IPC.TarskiSemantics public
open import IPC.Gentzen public


-- Soundness, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
eval (var i)      γ = lookup i γ
eval (lam t)      γ = λ a → eval t (γ , a)
eval (app t u)    γ = (eval t γ) (eval u γ)
eval (pair t u)   γ = eval t γ , eval u γ
eval (fst t)      γ = π₁ (eval t γ)
eval (snd t)      γ = π₂ (eval t γ)
eval tt           γ = ∙
eval (boom t)     γ = ◎ (eval t γ)
eval (inl t)      γ = ι₁ (eval t γ)
eval (inr t)      γ = ι₂ (eval t γ)
eval (case t u v) γ = κ (eval t γ)
                        (λ a → eval u (γ , a))
                        (λ b → eval v (γ , b))


-- TODO: Correctness with respect to conversion.

-- module _ {{_ : Model}} where
--   coco : ∀ {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
--   coco refl⇒             = refl
--   coco (trans⇒ p q)      = trans (coco p) (coco q)
--   coco (sym⇒ p)          = sym (coco p)
--   coco (cong⇒lam p)      = cong (λ f γ a → f (γ , a)) (coco p)
--   coco (cong⇒app p q)    = cong₂ (λ f g γ → (f γ) (g γ)) (coco p) (coco q)
--   coco (cong⇒pair p q)   = cong₂ (λ f g γ → f γ , g γ) (coco p) (coco q)
--   coco (cong⇒fst p)      = cong (λ f γ → π₁ (f γ)) (coco p)
--   coco (cong⇒snd p)      = cong (λ f γ → π₂ (f γ)) (coco p)
--   coco (cong⇒inl p)      = cong (λ f γ → ι₁ (f γ)) (coco p)
--   coco (cong⇒inr p)      = cong (λ f γ → ι₂ (f γ)) (coco p)
--   coco (cong⇒boom p)     = cong (λ f γ → ◎ (f γ)) (coco p)
--   coco (cong⇒case p q r) = cong₃ (λ f g h γ → κ (f γ)
--                                                   (λ a → g (γ , a))
--                                                   (λ b → h (γ , b)))
--                                   (coco p) (coco q) (coco r)
--   coco conv⇒lam          = {!refl!}
--   coco conv⇒app          = {!refl!}
--   coco conv⇒pair         = refl
--   coco conv⇒fst          = refl
--   coco conv⇒snd          = refl
--   coco conv⇒tt           = refl
