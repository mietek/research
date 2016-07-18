module BasicIPC.Gentzen.KripkeSoundness where

open import BasicIPC.KripkeSemantics public
open import BasicIPC.Gentzen public


-- Soundness, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ ξ a → eval t (ᴬᵍpair (mono⊩⋆ ξ γ) a)
eval (app t u)  γ = (eval t γ) refl≤ (eval u γ)
eval (pair t u) γ = ᴬᵍpair (eval t γ) (eval u γ)
eval (fst t)    γ = ᴬᵍfst (eval t γ)
eval (snd t)    γ = ᴬᵍsnd (eval t γ)
eval tt         γ = ᴬᵍtt


-- TODO: Correctness with respect to conversion.

-- module _ {{_ : Model}} where
--   coco : ∀ {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
--   coco refl⇒           = refl
--   coco (trans⇒ p q)    = trans (coco p) (coco q)
--   coco (sym⇒ p)        = sym (coco p)
--   coco (cong⇒lam p)    = cong {!!} (coco p)
--   coco (cong⇒app p q)  = cong₂ (λ f g γ → (f γ) refl≤ (g γ)) (coco p) (coco q)
--   coco (cong⇒pair p q) = cong₂ (λ f g γ → ᴬᵍpair (f γ) (g γ)) (coco p) (coco q)
--   coco (cong⇒fst p)    = cong (λ f γ → ᴬᵍfst (f γ)) (coco p)
--   coco (cong⇒snd p)    = cong (λ f γ → ᴬᵍsnd (f γ)) (coco p)
--   coco conv⇒lam        = {!refl!}
--   coco conv⇒app        = {!refl!}
--   coco conv⇒pair       = refl
--   coco conv⇒fst        = refl
--   coco conv⇒snd        = refl
--   coco conv⇒tt         = refl
