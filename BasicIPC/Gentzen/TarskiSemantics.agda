module BasicIPC.Gentzen.TarskiSemantics where

open import BasicIPC.Gentzen.Core public


-- Intuitionistic Tarski models.

record Model : Set₁ where
  infix 3 ⊨ᵅ_
  field
    -- Truth for atomic propositions.
    ⊨ᵅ_ : Atom → Set

open Model {{…}} public


-- Truth for propositions and contexts.

module _ {{_ : Model}} where
  infix 3 ⊨_
  ⊨_ : Ty → Set
  ⊨ α P   = ⊨ᵅ P
  ⊨ A ▷ B = ⊨ A → ⊨ B
  ⊨ ⊤    = ᴬ⊤
  ⊨ A ∧ B = ⊨ A ᴬ∧ ⊨ B

  infix 3 ⊨⋆_
  ⊨⋆_ : Cx Ty → Set
  ⊨⋆ ⌀     = ᴬ⊤
  ⊨⋆ Γ , A = ⊨⋆ Γ ᴬ∧ ⊨ A


-- Truth in all models.

infix 3 _ᴹ⊨_
_ᴹ⊨_ : Cx Ty → Ty → Set₁
Γ ᴹ⊨ A = ∀ {{_ : Model}} → ⊨⋆ Γ → ⊨ A


-- Soundness, or evaluation.

lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊨ A
lookup top     γ = ᴬsnd γ
lookup (pop i) γ = lookup i (ᴬfst γ)

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊨ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ a → eval t (ᴬpair γ a)
eval (app t u)  γ = (eval t γ) (eval u γ)
eval tt         γ = ᴬtt
eval (pair t u) γ = ᴬpair (eval t γ) (eval u γ)
eval (fst t)    γ = ᴬfst (eval t γ)
eval (snd t)    γ = ᴬsnd (eval t γ)


-- TODO: Correctness with respect to conversion.

-- module _ {{_ : Model}} where
--   coco : ∀ {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
--   coco refl⇒           = refl
--   coco (trans⇒ p q)    = trans (coco p) (coco q)
--   coco (sym⇒ p)        = sym (coco p)
--   coco (cong⇒lam p)    = cong (λ f γ a → f (γ ∙ a)) (coco p)
--   coco (cong⇒app p q)  = cong₂ (λ f g γ → (f γ) (g γ)) (coco p) (coco q)
--   coco (cong⇒pair p q) = cong₂ (λ f g γ → f γ ∙ g γ) (coco p) (coco q)
--   coco (cong⇒fst p)    = cong (λ f γ → ᴬfst (f γ)) (coco p)
--   coco (cong⇒snd p)    = cong (λ f γ → ᴬsnd (f γ)) (coco p)
--   coco conv⇒lam        = {!refl!}
--   coco conv⇒app        = {!refl!}
--   coco conv⇒tt         = refl
--   coco conv⇒pair       = refl
--   coco conv⇒fst        = refl
--   coco conv⇒snd        = refl
