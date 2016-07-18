module IPC.Gentzen.KripkeSoundness where

open import IPC.KripkeSemantics public
open import IPC.Gentzen public


-- Soundness, or evaluation.

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
eval (var i)                  γ = lookup i γ
eval {A ▷ B} (lam t)          γ = return {A ▷ B} (λ ξ a → eval t (ᴬᵍpair (mono⊩⋆ ξ γ) a))
eval (app {A} {B} t u)        γ = bind {A ▷ B} {B} (eval t γ)
                                    (λ ξ a → a refl≤ (eval u (mono⊩⋆ ξ γ)))
eval {A ∧ B} (pair t u)       γ = return {A ∧ B} (ᴬᵍpair (eval t γ) (eval u γ))
eval (fst {A} {B} t)          γ = bind {A ∧ B} {A} (eval t γ) (λ ξ s → ᴬᵍfst s)
eval (snd {A} {B} t)          γ = bind {A ∧ B} {B} (eval t γ) (λ ξ s → ᴬᵍsnd s)
eval tt                       γ = return {⊤} ᴬᵍtt
eval (boom {C} t)             γ = bind {⊥} {C} (eval t γ) (λ ξ ())
eval {A ∨ B} (inl t)          γ = return {A ∨ B} (ᴬᵍinl (eval t γ))
eval {A ∨ B} (inr t)          γ = return {A ∨ B} (ᴬᵍinr (eval t γ))
eval (case {A} {B} {C} t u v) γ = bind {A ∨ B} {C} (eval t γ) (λ ξ s → ᴬᵍcase s
                                    (λ a → eval u (ᴬᵍpair (mono⊩⋆ ξ γ) (λ ξ′ k → a ξ′ k)))
                                    (λ b → eval v (ᴬᵍpair (mono⊩⋆ ξ γ) (λ ξ′ k → b ξ′ k))))


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
