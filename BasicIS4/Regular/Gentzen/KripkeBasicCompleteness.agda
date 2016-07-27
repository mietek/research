module BasicIS4.Regular.Gentzen.KripkeBasicCompleteness where

open import BasicIS4.Regular.Gentzen.KripkeSoundness public
open import BasicIS4.KripkeSemantics.Ono public


-- Equipment for the canonical model.

-- FIXME ↓ FIXME ↓ FIXME -----------------------------------------------------
--
-- Following Alechina, et al.:
--
-- “Lemma 1 (Saturation).  Let a be an element of the algebra, and (Γ , Θ) an
--  a-consistent theory.  Then (Γ , Θ) has a saturated a-consistent extension
--  (Γ* , Θ) such that Γ* is a prime filter and Γ ⊆ Γ*.
--
--  In the proof of the saturation lemma and the following proof of the
--  Stone representation theorem we abbreviate consistency of a theory (Γ , Θ)
--  as Γ ≰ ◇Θ, and a-consistency by Γ ≰ a + ◇Θ, remembering that only in the
--  second case we permit the choice from Θ to be empty, in which the disjunct
--  ◇Θ disappears rather than being taken as ◇⊥.”
--
-- “Theorem 3 (Representation for CS4).  Let 𝒜 be a CS4-modal algebra.  Then
--  the Stone representation of 𝒜, SR(𝒜) = (W* , R* , ≤* , ⊨*) is a Kripke
--  model for CS4, where
--  1. W* is the set of all pairs (Γ , Θ) where Γ ⊆ 𝒜 is a prime filter, and
--     Θ ⊆ 𝒜 an arbitrary set of elements such that for all finite, nonempty,
--     choices of elements c₁ , … , cₙ ∈ Θ, ◇(c₁ + ⋯ + cₙ) ∉ Γ.
--  2. (Γ , Θ) ≤* (Γ′ , Θ′) iff Γ ⊆ Γ′
--  3. (Γ , Θ) R* (Γ′ , Θ′) iff ∀ a. □a ∈ Γ ⇒ a ∈ Γ′ and Θ ⊆ Θ′.
--  4. For all a ∈ A, (Γ , Θ) ⊨* a iff a ∈ Γ.”

record PrimeFilter (Γ : Cx Ty) : Set where

record Thing (Γ Θ : Cx Ty) : Set where
  field
    _/primeFilter : PrimeFilter Γ

-- FIXME ↑ FIXME ↑ FIXME -----------------------------------------------------


infix 4 _⁏_
record Worldᶜ : Set where
  constructor _⁏_
  field
    _/Γ         : Cx Ty
    _/Θ         : Cx Ty
    {{_/thing}} : Thing _/Γ _/Θ

  open Thing _/thing public

open Worldᶜ public

infix 3 _≤ᶜ_
_≤ᶜ_ : Worldᶜ → Worldᶜ → Set
w ≤ᶜ w′ = w /Γ ⊆ w′ /Γ

infix 3 _Rᶜ_
_Rᶜ_ : Worldᶜ → Worldᶜ → Set
w Rᶜ w′ = ∀ {A} → w /Γ ⊢ □ A → w′ /Γ ⊢ A × w /Θ ⊆ w′ /Θ


-- FIXME ↓ FIXME ↓ FIXME -----------------------------------------------------
--
-- lem₁ seems fine.
--
-- lem₂ looks very suspicious.  Is it supposed to be internalisation?

lem₁ : ∀ {A Γ} {{_ : PrimeFilter Γ}} → Γ ⊢ □ A → Γ ⊢ A
lem₁ = down

postulate
  lem₂ : ∀ {A Γ} {{_ : PrimeFilter Γ}} → Γ ⊢ A → Γ ⊢ □ A
  lem₃ : ∀ {Γ″ Θ″ Γ Θ Γ′ Θ′}
         {{_ : Thing Γ″ Θ″}} {{_ : Thing Γ Θ}} {{_ : Thing Γ′ Θ′}}
         → Γ ⊆ Γ′ → Θ′ ⊆ Θ″ → Θ ⊆ Θ″
  lem₄ : ∀ {A Γ Θ} {{_ : Thing Γ Θ}} → Thing (Γ , A) Θ
  lem₅ : ∀ {Γ Θ Ξ} {{_ : Thing Γ Θ}} {{_ : Thing ⌀ Ξ}} → Γ ⁏ Θ Rᶜ ⌀ ⁏ Ξ

-- FIXME ↑ FIXME ↑ FIXME -----------------------------------------------------


-- The canonical model.

weak≤ᶜ : ∀ {Θ A Γ} {{_ : Thing Γ Θ}} → Γ ⁏ Θ ≤ᶜ _⁏_ (Γ , A) Θ {{lem₄}}
weak≤ᶜ = weak⊆

reflRᶜ : ∀ {w} → w Rᶜ w
reflRᶜ {w} = λ i → lem₁ {{w /primeFilter}} i , refl⊆

transRᶜ : ∀ {w w′ w″} → w Rᶜ w′ → w′ Rᶜ w″ → w Rᶜ w″
transRᶜ {w′ = w′} ψ ψ′ = λ i →
  let i′ , ζ  = ψ i
      i″ , ζ′ = ψ′ (lem₂ {{w′ /primeFilter}} i′)
  in  i″ , trans⊆ ζ ζ′

zigRᶜ : ∀ {v′ w w′} → w′ Rᶜ v′ → w ≤ᶜ w′ → w Rᶜ v′
zigRᶜ {v′} {w} {w′} ψ ξ = λ i →
  let i′ , ζ = ψ (mono⊢ ξ i)
  in  i′ , lem₃ {{v′ /thing}} {{w /thing}} {{w′ /thing}} ξ ζ

instance
  canon : Model
  canon = record
    { World   = Worldᶜ
    ; _≤_     = _≤ᶜ_
    ; refl≤   = refl⊆
    ; trans≤  = trans⊆
    ; _R_     = _Rᶜ_
    ; reflR   = reflRᶜ
    ; transR  = transRᶜ
    ; _⊩ᵅ_   = λ w P → w /Γ ⊢ α P
    ; mono⊩ᵅ = mono⊢
    ; zigR    = zigRᶜ
    }


-- Soundness and completeness with respect to the canonical model.

mutual
  reflect : ∀ {A Γ Θ} {{_ : Thing Γ Θ}} → Γ ⊢ A → Γ ⁏ Θ ⊩ A
  reflect {α P}   t = t
  reflect {A ▷ B} t = λ ξ a → reflect {B} (app (mono⊢ ξ t) (reify {A} a))
  reflect {□ A}   t = λ ζ →
    let t′ , ξ = ζ t
    in  reflect {A} t′
  reflect {A ∧ B} t = reflect {A} (fst t) , reflect {B} (snd t)
  reflect {⊤}    t = ∙

  reify : ∀ {A Θ Γ} {{_ : Thing Γ Θ}} → Γ ⁏ Θ ⊩ A → Γ ⊢ A
  reify {α P}       s = s
  reify {A ▷ B} {Θ} s = lam (reify {B} {Θ} (s (weak≤ᶜ {Θ}) (reflect {A} v₀)))
  reify {□ A}   {Θ} s = box (reify {A} {Θ} (s lem₅))
  reify {A ∧ B}     s = pair (reify {A} (π₁ s)) (reify {B} (π₂ s))
  reify {⊤}        s = tt

reflect⋆ : ∀ {Π Γ Θ} {{_ : Thing Γ Θ}} → Γ ⊢⋆ Π → Γ ⁏ Θ ⊩⋆ Π
reflect⋆ {⌀}     ∙        = ∙
reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t

reify⋆ : ∀ {Π Γ Θ} {{_ : Thing Γ Θ}} → Γ ⁏ Θ ⊩⋆ Π → Γ ⊢⋆ Π
reify⋆ {⌀}     ∙        = ∙
reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ Θ} {{_ : Thing Γ Θ}} → Γ ⁏ Θ ⊩⋆ Γ
refl⊩⋆ = reflect⋆ refl⊢⋆

trans⊩⋆ : ∀ {Γ Θ Γ′ Θ′ Γ″} {{_ : Thing Γ Θ}} {{_ : Thing Γ′ Θ′}}
           → Γ ⁏ Θ ⊩⋆ Γ′ → Γ′ ⁏ Θ′ ⊩⋆ Γ″ → Γ ⁏ Θ ⊩⋆ Γ″
trans⊩⋆ ts us = reflect⋆ (trans⊢⋆ (reify⋆ ts) (reify⋆ us))


-- Completeness, or quotation.

-- FIXME ↓ FIXME ↓ FIXME -----------------------------------------------------
--
-- What should Θ be here?  Should we have a different definition of _ᴹ⊩_?
--
-- Currently, we have:
-- _ᴹ⊩_ : Cx Ty → Ty → Set₁
-- Γ ᴹ⊩ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩ A
--
-- Perhaps we should have:
-- _⁏_ᴹ⊩′_ : Cx Ty → Cx Ty → Ty → Set₁
-- Γ ⁏ Θ ᴹ⊩′ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩⋆ Θ → w ⊩ A
--
-- But then, how would that affect soundness?

quot : ∀ {A Γ} → Γ ᴹ⊩ A → Γ ⊢ A
quot t = reify {Θ = ⌀} (t refl⊩⋆)

-- FIXME ↑ FIXME ↑ FIXME -----------------------------------------------------


-- Normalisation by evaluation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ Ono.eval
