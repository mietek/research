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
    mono⊪ᵅ : ∀ {P w w′} → w ≤ w′ → w ⊪ᵅ P → w′ ⊪ᵅ P

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
    w ⊪ A ∧ B = w ⊩ A ᴬᵍ∧ w ⊩ B
    w ⊪ ⊤    = ᴬᵍ⊤
    w ⊪ ⊥    = ᴬᵍ⊥
    w ⊪ A ∨ B = w ⊩ A ᴬᵍ∨ w ⊩ B

    infix 3 _⊩_
    _⊩_ : World → Ty → Set
    w ⊩ A = ∀ {w′ C} → w ≤ w′ → (∀ {w″} → w′ ≤ w″ → w″ ⊪ A → w″ ‼ C) → w′ ‼ C

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ⌀     = ᴬᵍ⊤
  w ⊩⋆ Γ , A = w ⊩⋆ Γ ᴬᵍ∧ w ⊩ A


  -- Monotonicity with respect to intuitionistic accessibility.

  mutual
    mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
    mono⊩ ξ a = λ ξ′ k′ → a (trans≤ ξ ξ′) k′

    mono⊪ : ∀ {A w w′} → w ≤ w′ → w ⊪ A → w′ ⊪ A
    mono⊪ {α P}   ξ s = mono⊪ᵅ ξ s
    mono⊪ {A ▷ B} ξ s = λ ξ′ a → s (trans≤ ξ ξ′) a
    mono⊪ {A ∧ B} ξ s = ᴬᵍpair (mono⊩ {A} ξ (ᴬᵍfst s)) (mono⊩ {B} ξ (ᴬᵍsnd s))
    mono⊪ {⊤}    ξ s = ᴬᵍtt
    mono⊪ {⊥}    ξ ()
    mono⊪ {A ∨ B} ξ (ᴬᵍinl a) = ᴬᵍinl (mono⊩ {A} ξ a)
    mono⊪ {A ∨ B} ξ (ᴬᵍinr b) = ᴬᵍinr (mono⊩ {B} ξ b)

  mono⊩⋆ : ∀ {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono⊩⋆ {⌀}     ξ γ = ᴬᵍtt
  mono⊩⋆ {Γ , A} ξ γ = ᴬᵍpair (mono⊩⋆ {Γ} ξ (ᴬᵍfst γ)) (mono⊩ {A} ξ (ᴬᵍsnd γ))


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
lookup top     γ = ᴬᵍsnd γ
lookup (pop i) γ = lookup i (ᴬᵍfst γ)

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
