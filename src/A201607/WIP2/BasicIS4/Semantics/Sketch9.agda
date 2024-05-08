module A201607.WIP2.BasicIS4.Semantics.Sketch9 where

open import A201607.Common.Semantics public
open import A201607.BasicIS4.Syntax.Common public


record Model : Set₁ where
  infix 3 _[∈]_ _[⊢]_
  infix 5 _[+]_
  field
    World : Set

    [∅] : World

    _≤[_]_   : World → Cx² Ty Ty → World → Set
    refl≤[]  : ∀ {w} → w ≤[ ∅ ⁏ ∅ ] w
    trans≤[] : ∀ {Γ Γ′ Δ Δ′ w w′ w″} → w ≤[ Γ ⁏ Δ ] w′ → w′ ≤[ Γ′ ⁏ Δ′ ] w″ → w ≤[ Γ ⧺ Γ′ ⁏ Δ ⧺ Δ′ ] w″

    _[+]_ : World → Cx² Ty Ty → World
    _[∈]_ : Cx² Ty Ty → World → Set

    _[⊢]_   : World → Ty → Set

--  mono[⊢] : ∀ {A w w′} → w ≤ w′ → w [⊢] A → w′ [⊢] A

    [var]    : ∀ {A w}   → (∅ , A ⁏ ∅) [∈] w → w [⊢] A

--  [lam]    : ∀ {A B w} → w [+] (∅ , A ⁏ ∅) [⊢] B → w [⊢] A ▻ B
    [lam]    : ∀ {A B w w′} → w ≤[ ∅ , A ⁏ ∅ ] w′ → w′ [⊢] B → w [⊢] A ▻ B

    [app]    : ∀ {A B w} → w [⊢] A ▻ B → w [⊢] A → w [⊢] B

    [mvar]   : ∀ {A w}   → (∅ ⁏ ∅ , A) [∈] w → w [⊢] A

--  [box]    : ∀ {Γ Δ A} → [∅] [+] (∅ ⁏ Δ) [⊢] A → [∅] [+] (Γ ⁏ Δ) [⊢] □ A
    [box]    : ∀ {A Γ Δ w w′} → [∅] ≤[ ∅ ⁏ Δ ] w → w [⊢] A → [∅] ≤[ Γ ⁏ Δ ] w′ → w′ [⊢] □ A

    [unbox]  : ∀ {A C w} → w [⊢] □ A → w [+] (∅ ⁏ ∅ , A) [⊢] C → w [⊢] C
    [pair]   : ∀ {A B w} → w [⊢] A → w [⊢] B → w [⊢] A ∧ B
    [fst]    : ∀ {A B w} → w [⊢] A ∧ B → w [⊢] A
    [snd]    : ∀ {A B w} → w [⊢] A ∧ B → w [⊢] B
    [unit]   : ∀ {w}     → w [⊢] ⊤

  _≤_ : World → World → Set
  w ≤ w′ = Σ (Cx² Ty Ty) λ { (Γ ⁏ Δ) → w ≤[ Γ ⁏ Δ ] w′ }

  refl≤ : ∀ {w} → w ≤ w
  refl≤ = (∅ ⁏ ∅) , refl≤[]

  trans≤ : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″
  trans≤ ((Γ ⁏ Δ) , ξ) ((Γ′ ⁏ Δ′) , ξ′) = (Γ ⧺ Γ′ ⁏ Δ ⧺ Δ′) , trans≤[] ξ ξ′
