module IPC.Gentzen.KripkeSoundness where

open import IPC.KripkeSemantics public
open import IPC.Gentzen public


-- Soundness, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
eval (var i)                  γ = lookup i γ
eval (lam {A} {B} t)          γ = return {A ▷ B} (λ ξ a → eval t (mono⊩⋆ ξ γ , a))
eval (app {A} {B} t u)        γ = bind {A ▷ B} {B} (eval t γ)
                                    (λ ξ f → f refl≤ (eval u (mono⊩⋆ ξ γ)))
eval (pair {A} {B} t u)       γ = return {A ∧ B} (eval t γ , eval u γ)
eval (fst {A} {B} t)          γ = bind {A ∧ B} {A} (eval t γ) (λ ξ s → π₁ s)
eval (snd {A} {B} t)          γ = bind {A ∧ B} {B} (eval t γ) (λ ξ s → π₂ s)
eval tt                       γ = return {⊤} ∙
eval (boom {C} t)             γ = bind {⊥} {C} (eval t γ) (λ ξ s → elimBot s)
eval (inl {A} {B} t)          γ = return {A ∨ B} (ι₁ (eval t γ))
eval (inr {A} {B} t)          γ = return {A ∨ B} (ι₂ (eval t γ))
eval (case {A} {B} {C} t u v) γ = bind {A ∨ B} {C} (eval t γ) (λ ξ s → κ s
                                    (λ a → eval u (mono⊩⋆ ξ γ , λ ξ′ k → a ξ′ k))
                                    (λ b → eval v (mono⊩⋆ ξ γ , λ ξ′ k → b ξ′ k)))


-- TODO: Correctness with respect to conversion.

-- module _ {{_ : Model}} where
--   coco : ∀ {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
--   coco refl⇒             = refl
--   coco (trans⇒ p q)      = trans (coco p) (coco q)
--   coco (sym⇒ p)          = sym (coco p)
--   coco (cong⇒lam p)      = cong {!!} (coco p)
--   coco (cong⇒app p q)    = cong₂ {!!} (coco p) (coco q)
--   coco (cong⇒pair p q)   = cong₂ {!!} (coco p) (coco q)
--   coco (cong⇒fst p)      = cong {!!} (coco p)
--   coco (cong⇒snd p)      = cong {!!} (coco p)
--   coco (cong⇒inl p)      = cong {!!} (coco p)
--   coco (cong⇒inr p)      = cong {!!} (coco p)
--   coco (cong⇒boom p)     = cong {!!} (coco p)
--   coco (cong⇒case p q r) = cong₃ {!!} (coco p) (coco q) (coco r)
--   coco conv⇒lam          = {!!}
--   coco conv⇒app          = {!!}
--   coco conv⇒tt           = {!!}
--   coco conv⇒pair         = {!!}
--   coco conv⇒fst          = {!!}
--   coco conv⇒snd          = {!!}