module BasicIPC.Gentzen.KripkeSemantics.Core where

open import BasicIPC.Gentzen.Core public


-- Intuitionistic Kripke models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    World : Set

    -- Intuitionistic accessibility; preorder.
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_   : World → Atom → Set
    mono⊩ᵅ : ∀ {p w w′} → w ≤ w′ → w ⊩ᵅ p → w′ ⊩ᵅ p

open Model {{…}} public


-- Forcing for propositions and contexts.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Ty → Set
  w ⊩ α P   = w ⊩ᵅ P
  w ⊩ A ▷ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ A ∧ B = w ⊩ A ᴬ∧ w ⊩ B
  w ⊩ ⊤    = ᴬ⊤

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ⌀     = ᴬ⊤
  w ⊩⋆ Γ , A = w ⊩⋆ Γ ᴬ∧ w ⊩ A


  -- Monotonicity with respect to intuitionistic accessibility.

  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}   ξ s = mono⊩ᵅ ξ s
  mono⊩ {A ▷ B} ξ s = λ ξ′ a → s (trans≤ ξ ξ′) a
  mono⊩ {A ∧ B} ξ s = ᴬpair (mono⊩ {A} ξ (ᴬfst s)) (mono⊩ {B} ξ (ᴬsnd s))
  mono⊩ {⊤}    ξ s = ᴬtt

  mono⊩⋆ : ∀ {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono⊩⋆ {⌀}     ξ γ = ᴬtt
  mono⊩⋆ {Γ , A} ξ γ = ᴬpair (mono⊩⋆ {Γ} ξ (ᴬfst γ)) (mono⊩ {A} ξ (ᴬsnd γ))


-- Forcing in all models.

infix 3 _ᴹ⊩_
_ᴹ⊩_ : Cx Ty → Ty → Set₁
Γ ᴹ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩ A


-- Soundness, or evaluation.

lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊩ A
lookup top     γ = ᴬsnd γ
lookup (pop i) γ = lookup i (ᴬfst γ)

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
eval (var i)    γ = lookup i γ
eval (lam t)    γ = λ ξ a → eval t (ᴬpair (mono⊩⋆ ξ γ) a)
eval (app t u)  γ = (eval t γ) refl≤ (eval u γ)
eval (pair t u) γ = ᴬpair (eval t γ) (eval u γ)
eval (fst t)    γ = ᴬfst (eval t γ)
eval (snd t)    γ = ᴬsnd (eval t γ)
eval tt         γ = ᴬtt


-- TODO: Correctness with respect to conversion.

-- module _ {{_ : Model}} where
--   coco : ∀ {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → eval t ≡ eval t′
--   coco refl⇒           = refl
--   coco (trans⇒ p q)    = trans (coco p) (coco q)
--   coco (sym⇒ p)        = sym (coco p)
--   coco (cong⇒lam p)    = cong {!!} (coco p)
--   coco (cong⇒app p q)  = cong₂ (λ f g γ → (f γ) refl≤ (g γ)) (coco p) (coco q)
--   coco (cong⇒pair p q) = cong₂ (λ f g γ → f γ ∙ g γ) (coco p) (coco q)
--   coco (cong⇒fst p)    = cong (λ f γ → ᴬfst (f γ)) (coco p)
--   coco (cong⇒snd p)    = cong (λ f γ → ᴬsnd (f γ)) (coco p)
--   coco conv⇒lam        = {!refl!}
--   coco conv⇒app        = {!refl!}
--   coco conv⇒pair       = refl
--   coco conv⇒fst        = refl
--   coco conv⇒snd        = refl
--   coco conv⇒tt         = refl
