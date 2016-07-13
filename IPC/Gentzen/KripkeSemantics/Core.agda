module IPC.Gentzen.KripkeSemantics.Core where

open import IPC.Gentzen.Core public


-- Intuitionistic Kripke models.

record Model : Set₁ where
  infix 3 _⊩ᴬ_
  field
    World : Set

    -- Intuitionistic accessibility; preorder.
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    -- Forcing for atomic propositions; monotonic.
    _⊩ᴬ_   : World → Atom → Set
    mono⊩ᴬ : ∀ {p w w′} → w ≤ w′ → w ⊩ᴬ p → w′ ⊩ᴬ p

open Model {{…}} public


-- Truth in one model.

module _ {{_ : Model}} where
  -- Forcing for propositions.
  infix 3 _⊩ᵀ_
  _⊩ᵀ_ : World → Ty → Set
  w ⊩ᵀ ᴬ P   = w ⊩ᴬ P
  w ⊩ᵀ A ▷ B = ∀ {w′} → w ≤ w′ → w′ ⊩ᵀ A → w′ ⊩ᵀ B
  w ⊩ᵀ ⫪    = ⊤
  w ⊩ᵀ A ∧ B = w ⊩ᵀ A × w ⊩ᵀ B

  -- Forcing for contexts.
  infix 3 _⊩ᴳ_
  _⊩ᴳ_ : World → Cx Ty → Set
  w ⊩ᴳ ⌀     = ⊤
  w ⊩ᴳ Γ , A = w ⊩ᴳ Γ × w ⊩ᵀ A


  -- Monotonicity with respect to intuitionistic accessibility.

  mono⊩ᵀ : ∀ {A w w′} → w ≤ w′ → w ⊩ᵀ A → w′ ⊩ᵀ A
  mono⊩ᵀ {ᴬ P}   ξ s       = mono⊩ᴬ ξ s
  mono⊩ᵀ {A ▷ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
  mono⊩ᵀ {⫪}    ξ tt      = tt
  mono⊩ᵀ {A ∧ B} ξ (a ∙ b) = mono⊩ᵀ {A} ξ a ∙ mono⊩ᵀ {B} ξ b

  mono⊩ᴳ : ∀ {Γ w w′} → w ≤ w′ → w ⊩ᴳ Γ → w′ ⊩ᴳ Γ
  mono⊩ᴳ {⌀}     ξ tt      = tt
  mono⊩ᴳ {Γ , A} ξ (γ ∙ a) = mono⊩ᴳ {Γ} ξ γ ∙ mono⊩ᵀ {A} ξ a


-- Truth in all models.

infix 3 _⊩_
_⊩_ : Cx Ty → Ty → Set₁
Γ ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩ᴳ Γ → w ⊩ᵀ A


-- Soundness with respect to all models, or evaluation.

lookup : ∀ {A Γ} → A ∈ Γ → Γ ⊩ A
lookup top     (γ ∙ a) = a
lookup (pop i) (γ ∙ b) = lookup i γ

eval : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ ξ a → eval t (mono⊩ᴳ ξ γ ∙ a)
eval (app t u)  γ = (eval t γ) refl≤ (eval u γ)
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
--   coco (cong⇒lam p)    = cong {!!} (coco p)
--   coco (cong⇒app p q)  = cong₂ (λ f g γ → (f γ) refl≤ (g γ)) (coco p) (coco q)
--   coco (cong⇒pair p q) = cong₂ (λ f g γ → f γ ∙ g γ) (coco p) (coco q)
--   coco (cong⇒fst p)    = cong (λ f γ → proj₁ (f γ)) (coco p)
--   coco (cong⇒snd p)    = cong (λ f γ → proj₂ (f γ)) (coco p)
--   coco conv⇒lam        = {!refl!}
--   coco conv⇒app        = {!refl!}
--   coco conv⇒unit       = refl
--   coco conv⇒pair       = refl
--   coco conv⇒fst        = refl
--   coco conv⇒snd        = refl
