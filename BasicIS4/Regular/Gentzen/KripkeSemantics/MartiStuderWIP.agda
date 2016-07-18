module BasicIS4.Regular.Gentzen.KripkeSemantics.MartiStuderWIP where

open import BasicIS4.Regular.Gentzen.Core public


-- Extended intuitionistic Kripke models, following Marti and Studer.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    World : Set

    -- Intuitionistic accessibility; preorder.
    _≤_    : World → World → Set
    refl≤  : ∀ {w} → w ≤ w
    trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″

    -- Modal accessibility; preorder.
    _R_    : World → World → Set
    reflR  : ∀ {w} → w R w
    transR : ∀ {w w′ w″} → w R w′ → w′ R w″ → w R w″

    -- Forcing for atomic propositions; monotonic.
    _⊩ᵅ_   : World → Atom → Set
    mono⊩ᵅ : ∀ {P w w′} → w ≤ w′ → w ⊩ᵅ P → w′ ⊩ᵅ P

    -- NEW:
    cutR : ∀ {x w w′} → w ≤ w′ → w′ R x → w R x

  ≤→R : ∀ {w w′} → w ≤ w′ → w R w′
  ≤→R ξ = cutR ξ reflR

open Model {{…}} public


-- Forcing for propositions and contexts.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Ty → Set
  w ⊩ α P   = w ⊩ᵅ P
  w ⊩ A ▷ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ A ∧ B = w ⊩ A ᴬᵍ∧ w ⊩ B
  w ⊩ □ A   = ∀ {w′} → w R w′ → w′ ⊩ A
  w ⊩ ⊤    = ᴬᵍ⊤

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Cx Ty → Set
  w ⊩⋆ ⌀     = ᴬᵍ⊤
  w ⊩⋆ Γ , A = w ⊩⋆ Γ ᴬᵍ∧ w ⊩ A


  -- Monotonicity with respect to intuitionistic accessibility.

  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}   ξ s = mono⊩ᵅ ξ s
  mono⊩ {A ▷ B} ξ s = λ ξ′ a → s (trans≤ ξ ξ′) a
  mono⊩ {A ∧ B} ξ s = ᴬᵍpair (mono⊩ {A} ξ (ᴬᵍfst s)) (mono⊩ {B} ξ (ᴬᵍsnd s))
  mono⊩ {□ A}   ξ s = λ ζ → s (transR (≤→R ξ) ζ)
  mono⊩ {⊤}    ξ s = ᴬᵍtt

  mono⊩⋆ : ∀ {Γ w w′} → w ≤ w′ → w ⊩⋆ Γ → w′ ⊩⋆ Γ
  mono⊩⋆ {⌀}     ξ γ = ᴬᵍtt
  mono⊩⋆ {Γ , A} ξ γ = ᴬᵍpair (mono⊩⋆ {Γ} ξ (ᴬᵍfst γ)) (mono⊩ {A} ξ (ᴬᵍsnd γ))


  -- NOTE: This is almost certainly false.
  postulate
    mmono⊩ : ∀ {A w w′} → w R w′ → w ⊩ A → w′ ⊩ A


-- Forcing in all models.

infix 3 _ᴹ⊩_
_ᴹ⊩_ : Cx Ty → Ty → Set₁
Γ ᴹ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩ A

infix 3 _ᴹ⊩⋆_
_ᴹ⊩⋆_ : Cx Ty → Cx Ty → Set₁
Γ ᴹ⊩⋆ Π = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩⋆ Π


-- Soundness, or evaluation.

lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊩ A
lookup top     γ = ᴬᵍsnd γ
lookup (pop i) γ = lookup i (ᴬᵍfst γ)

-- NOTE: We seem to require mmono⊩ which is almost certainly false.
mutual
  eval : ∀ {A Γ} → Γ ⊢ A → Γ ᴹ⊩ A
  eval (var i)         γ = lookup i γ
  eval (lam t)         γ = λ ξ a → eval t (ᴬᵍpair (mono⊩⋆ ξ γ) a)
  eval (app t u)       γ = (eval t γ) refl≤ (eval u γ)
  eval {□ A} (multibox ts u) γ = λ ζ →
--    -- NOTE: Cutting this fails the termination check.
--    let v  = multicut⊢ ts u
--        v′ = eval v γ
--    in mmono⊩ {A} ζ v′
    let δ  = eval⋆ ts γ
        v′ = eval u δ
    in mmono⊩ {A} ζ v′
  eval (down t)        γ = (eval t γ) reflR
  eval (pair t u)      γ = ᴬᵍpair (eval t γ) (eval u γ)
  eval (fst t)         γ = ᴬᵍfst (eval t γ)
  eval (snd t)         γ = ᴬᵍsnd (eval t γ)
  eval tt              γ = ᴬᵍtt

  eval⋆ : ∀ {Π Γ} → Γ ⊢⋆ Π → Γ ᴹ⊩⋆ Π
  eval⋆ {⌀}     ᴬᵍtt          γ = ᴬᵍtt
  eval⋆ {Π , A} (ᴬᵍpair ts t) γ = ᴬᵍpair (eval⋆ ts γ) (eval t γ)

{-
Goal: w′ ⊩ A
————————————
v′ : w ⊩ A
δ  : w ⊩⋆ (□⋆ Π)
————————————
-- v′ : w ⊩ A
-- v  : Γ ⊢ A
————————————
ζ  : w R w′
γ  : w ⊩⋆ Γ
u  : (□⋆ Π) ⊢ A
ts : Γ ⊢⋆ (□⋆ Π)
————————————
w′ : World
w  : World
Π  : Cx Ty
Γ  : Cx Ty
A  : Ty
-}
