module IPC.Gentzen.KripkeSemantics.Core where

open import IPC.Gentzen.Core public


-- Intuitionistic Kripke-CPS models, following Ilik.

record Model : Set₁ where
  infix 3 _⊪ᵅ_
  field
    World : Set

    -- Intuitionistic accessibility; preorder.
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    -- Strong forcing for atomic propositions; monotonic.
    _⊪ᵅ_   : World → Atom → Set
    mono⊪ᵅ : ∀ {p w w′} → w ≤ w′ → w ⊪ᵅ p → w′ ⊪ᵅ p

    -- Exploding for propositions.
    _‼_ : World → Ty → Set

open Model {{…}} public


-- Strong forcing for propositions; forcing for propositions and contexts.

module _ {{_ : Model}} where
  mutual
    infix 3 _⊪_
    _⊪_ : World → Ty → Set
    w ⊪ α P   = w ⊪ᵅ P
    w ⊪ A ▷ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
    w ⊪ A ∧ B = w ⊩ A ᴬ∧ w ⊩ B
    w ⊪ ⊤    = ᴬ⊤
    w ⊪ ⊥    = ᴬ⊥
    w ⊪ A ∨ B = w ⊩ A ᴬ∨ w ⊩ B

    infix 3 _⊩_
    _⊩_ : World → Ty → Set
    w ⊩ A = ∀ {w′ C} → w ≤ w′ → (∀ {w″} → w′ ≤ w″ → w″ ⊪ A → w″ ‼ C) → w′ ‼ C

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ⌀     = ᴬ⊤
  w ⊩⋆ Γ , A = w ⊩⋆ Γ ᴬ∧ w ⊩ A


  -- Monotonicity with respect to intuitionistic accessibility.

  mutual
    mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
    mono⊩ ξ a = λ ξ′ k′ → a (trans≤ ξ ξ′) k′

    mono⊪ : ∀ {A w w′} → w ≤ w′ → w ⊪ A → w′ ⊪ A
    mono⊪ {α P}   ξ s = mono⊪ᵅ ξ s
    mono⊪ {A ▷ B} ξ s = λ ξ′ a → s (trans≤ ξ ξ′) a
    mono⊪ {A ∧ B} ξ s = ᴬpair (mono⊩ {A} ξ (ᴬfst s)) (mono⊩ {B} ξ (ᴬsnd s))
    mono⊪ {⊤}    ξ s = ᴬtt
    mono⊪ {⊥}    ξ ()
    mono⊪ {A ∨ B} ξ (ᴬinl a) = ᴬinl (mono⊩ {A} ξ a)
    mono⊪ {A ∨ B} ξ (ᴬinr b) = ᴬinr (mono⊩ {B} ξ b)

  mono⊩⋆ : ∀ {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono⊩⋆ {⌀}     ξ γ = ᴬtt
  mono⊩⋆ {Γ , A} ξ γ = ᴬpair (mono⊩⋆ {Γ} ξ (ᴬfst γ)) (mono⊩ {A} ξ (ᴬsnd γ))


  -- The CPS monad.

  return : ∀ {A w} → w ⊪ A → w ⊩ A
  return {A} a = λ ξ k → k refl≤ (mono⊪ {A} ξ a)

  bind : ∀ {A B w} → w ⊩ A → (∀ {w′} → w ≤ w′ → w′ ⊪ A → w′ ⊩ B) → w ⊩ B
  bind a k = λ ξ k′ → a ξ (λ ξ′ a′ → k (trans≤ ξ ξ′) a′ refl≤ (λ ξ″ a″ → k′ (trans≤ ξ′ ξ″) a″))


-- Forcing in all models.

infix 3 _ᴹ⊩_
_ᴹ⊩_ : Cx Ty → Ty → Set₁
Γ ᴹ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩ A


-- Soundness, or evaluation.

lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊩ A
lookup top     γ = ᴬsnd γ
lookup (pop i) γ = lookup i (ᴬfst γ)

eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
eval (var i)                  γ = lookup i γ
eval {A ▷ B} (lam t)          γ = return {A ▷ B} (λ ξ a → eval t (ᴬpair (mono⊩⋆ ξ γ) a))
eval (app {A} {B} t u)        γ = bind {A ▷ B} {B} (eval t γ)
                                    (λ ξ a → a refl≤ (eval u (mono⊩⋆ ξ γ)))
eval {A ∧ B} (pair t u)       γ = return {A ∧ B} (ᴬpair (eval t γ) (eval u γ))
eval (fst {A} {B} t)          γ = bind {A ∧ B} {A} (eval t γ) (λ ξ s → ᴬfst s)
eval (snd {A} {B} t)          γ = bind {A ∧ B} {B} (eval t γ) (λ ξ s → ᴬsnd s)
eval tt                       γ = return {⊤} ᴬtt
eval (boom {C} t)             γ = bind {⊥} {C} (eval t γ) (λ ξ ())
eval {A ∨ B} (inl t)          γ = return {A ∨ B} (ᴬinl (eval t γ))
eval {A ∨ B} (inr t)          γ = return {A ∨ B} (ᴬinr (eval t γ))
eval (case {A} {B} {C} t u v) γ = bind {A ∨ B} {C} (eval t γ) (λ ξ s → ᴬcase s
                                    (λ a → eval u (ᴬpair (mono⊩⋆ ξ γ) (λ ξ′ k → a ξ′ k)))
                                    (λ b → eval v (ᴬpair (mono⊩⋆ ξ γ) (λ ξ′ k → b ξ′ k))))


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
