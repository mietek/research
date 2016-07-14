module BasicIPC.Gentzen.TarskiSemantics where

open import BasicIPC.Gentzen.Core public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 ⊨ᴬ_
  field
    -- Truth for atomic propositions.
    ⊨ᴬ_ : Atom → Set

open Model {{…}} public


-- Truth for propositions and contexts.

module _ {{_ : Model}} where
  infix 3 ⊨_
  ⊨_ : Ty → Set
  ⊨ ᴬ P   = ⊨ᴬ P
  ⊨ A ▷ B = ⊨ A → ⊨ B
  ⊨ ⫪    = ⊤
  ⊨ A ∧ B = ⊨ A × ⊨ B

  infix 3 ⊨⋆_
  ⊨⋆_ : Cx Ty → Set
  ⊨⋆ ⌀     = ⊤
  ⊨⋆ Γ , A = ⊨⋆ Γ × ⊨ A


-- Truth in all models.

infix 3 _ᴹ⊨_
_ᴹ⊨_ : Cx Ty → Ty → Set₁
Γ ᴹ⊨ A = ∀ {{_ : Model}} → ⊨⋆ Γ → ⊨ A


-- Soundness, or evaluation.

lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊨ A
lookup top     (γ ∙ a) = a
lookup (pop i) (γ ∙ b) = lookup i γ

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ a → eval t (γ ∙ a)
eval (app t u)  γ = (eval t γ) (eval u γ)
eval unit       γ = tt
eval (pair t u) γ = eval t γ ∙ eval u γ
eval (fst t)    γ = proj₁ (eval t γ)
eval (snd t)    γ = proj₂ (eval t γ)


-- TODO: Correctness with respect to conversion.

-- module _ {{_ : Model}} where
--   coco : ∀ {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
--   coco refl⇒           = refl
--   coco (trans⇒ p q)    = trans (coco p) (coco q)
--   coco (sym⇒ p)        = sym (coco p)
--   coco (cong⇒lam p)    = cong (λ f γ a → f (γ ∙ a)) (coco p)
--   coco (cong⇒app p q)  = cong₂ (λ f g γ → (f γ) (g γ)) (coco p) (coco q)
--   coco (cong⇒pair p q) = cong₂ (λ f g γ → f γ ∙ g γ) (coco p) (coco q)
--   coco (cong⇒fst p)    = cong (λ f γ → proj₁ (f γ)) (coco p)
--   coco (cong⇒snd p)    = cong (λ f γ → proj₂ (f γ)) (coco p)
--   coco conv⇒lam        = {!refl!}
--   coco conv⇒app        = {!refl!}
--   coco conv⇒unit       = refl
--   coco conv⇒pair       = refl
--   coco conv⇒fst        = refl
--   coco conv⇒snd        = refl
