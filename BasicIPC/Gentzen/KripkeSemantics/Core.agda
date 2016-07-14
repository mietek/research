module BasicIPC.Gentzen.KripkeSemantics.Core where

open import BasicIPC.Gentzen.Core public


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


-- Forcing for propositions and contexts.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Ty → Set
  w ⊩ ᴬ P   = w ⊩ᴬ P
  w ⊩ A ▷ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ ⫪    = ⊤
  w ⊩ A ∧ B = w ⊩ A × w ⊩ B

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ⌀     = ⊤
  w ⊩⋆ Γ , A = w ⊩⋆ Γ × w ⊩ A


  -- Monotonicity with respect to intuitionistic accessibility.

  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {ᴬ P}   ξ s       = mono⊩ᴬ ξ s
  mono⊩ {A ▷ B} ξ f       = λ ξ′ a → f (trans≤ ξ ξ′) a
  mono⊩ {⫪}    ξ tt      = tt
  mono⊩ {A ∧ B} ξ (a ∙ b) = mono⊩ {A} ξ a ∙ mono⊩ {B} ξ b

  mono⊩⋆ : ∀ {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono⊩⋆ {⌀}     ξ tt      = tt
  mono⊩⋆ {Γ , A} ξ (γ ∙ a) = mono⊩⋆ {Γ} ξ γ ∙ mono⊩ {A} ξ a


-- Forcing in all models.

infix 3 _ᴹ⊩_
_ᴹ⊩_ : Cx Ty → Ty → Set₁
Γ ᴹ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩ A


-- Soundness, or evaluation.

lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊩ A
lookup top     (γ ∙ a) = a
lookup (pop i) (γ ∙ b) = lookup i γ

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ ξ a → eval t (mono⊩⋆ ξ γ ∙ a)
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
