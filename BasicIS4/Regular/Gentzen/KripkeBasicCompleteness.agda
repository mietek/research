module BasicIS4.Regular.Gentzen.KripkeBasicCompleteness where

open import BasicIS4.Regular.Gentzen.KripkeSoundness public
open import BasicIS4.KripkeSemantics.Ono public


-- Prime filters, following Alechina, et al.

PrimeFilter : Cx Ty → Set
PrimeFilter Γ = ∃ (λ Δ → Γ ≡ □⋆ Δ)

onomPF : ∀ {Γ Γ′} → Γ ⊆ Γ′ → PrimeFilter Γ′ → PrimeFilter Γ
onomPF {⌀}     η        (⌀ , refl)       = ⌀ , refl
onomPF {Γ , A} ()       (⌀ , refl)
onomPF         (skip η) ((Δ , A) , refl) = onomPF η (_ , refl)
onomPF         (keep η) ((Δ , A) , refl) with onomPF η (_ , refl)
onomPF         (keep η) ((Δ , A) , refl) | Δ′ , refl = (Δ′ , A) , refl


-- Worlds.

record Worldᶜ : Set where
  constructor _&_
  field
    _/Γ : Cx Ty
    _/Φ : PrimeFilter _/Γ

open Worldᶜ public


-- Intuitionistic accessibility.

infix 3 _≤ᶜ_
_≤ᶜ_ : Worldᶜ → Worldᶜ → Set
w ≤ᶜ w′ = w /Γ ⊆ w′ /Γ

refl≤ᶜ : ∀ {w} → w ≤ᶜ w
refl≤ᶜ = refl⊆

trans≤ᶜ : ∀ {w w′ w″} → w ≤ᶜ w′ → w′ ≤ᶜ w″ → w ≤ᶜ w″
trans≤ᶜ = trans⊆


-- Modal accessibility.

infix 3 _Rᶜ_
_Rᶜ_ : Worldᶜ → Worldᶜ → Set
w Rᶜ w′ = ∀ {A} → w /Γ ⊢ □ A → w′ /Γ ⊢ A

reflRᶜ : ∀ {w} → w Rᶜ w
reflRᶜ = down

transRᶜ : ∀ {w w′ w″} → w Rᶜ w′ → w′ Rᶜ w″ → w Rᶜ w″
transRᶜ ζ ζ′ = ζ′ ∘ ζ ∘ up

zigRᶜ : ∀ {v′ w w′} → w′ Rᶜ v′ → w ≤ᶜ w′ → w Rᶜ v′
zigRᶜ ζ ξ = ζ ∘ mono⊢ ξ


-- The canonical model.

instance
  canon : Model
  canon = record
    { World   = Worldᶜ
    ; _≤_     = _≤ᶜ_
    ; refl≤   = λ {w} → refl≤ᶜ {w}
    ; trans≤  = λ {w} {w′} {w″} → trans≤ᶜ {w} {w′} {w″}
    ; _R_     = _Rᶜ_
    ; reflR   = λ {w} → reflRᶜ {w}
    ; transR  = λ {w} {w′} {w″} → transRᶜ {w} {w′} {w″}
    ; _⊩ᵅ_   = λ w P → w /Γ ⊢ α P
    ; mono⊩ᵅ = mono⊢
    ; zigR    = λ {v′} {w} {w′} → zigRᶜ {v′} {w} {w′}
    }


-- NOTE: This is almost certainly false.
postulate
  oops : ∀ {Δ A} {{_ : PrimeFilter (□⋆ Δ)}} → PrimeFilter (□⋆ Δ , A)


-- Soundness and completeness with respect to the canonical model.

-- TODO: Report {{_}} as a bug.

mutual
  reflect : ∀ {A Γ} {{Φ : PrimeFilter Γ}} → Γ ⊢ A → Γ & Φ ⊩ A
  reflect {α P}   t = t
  reflect {A ▷ B} t = λ ξ a → reflect {B} {{_}} (app (mono⊢ ξ t) (reify {A} a))
  reflect {□ A}   t = λ ζ → reflect {A} {{_}} (ζ t)
  reflect {A ∧ B} t = reflect {A} (fst t) , reflect {B} (snd t)
  reflect {⊤}    t = ∙

  reify : ∀ {A Γ} {{Φ : PrimeFilter Γ}} → Γ & Φ ⊩ A → Γ ⊢ A
  reify {α P}                s = s
  reify {A ▷ B} {{Δ , refl}} s = lam (reify {B} {{oops {{Δ , refl}}}} (s weak⊆ (reflect {A} v₀)))
  reify {□ A}   {{Δ , refl}} s = multibox refl⊢⋆ (reify {A} {{Δ , refl}} (s (reflRᶜ {(□⋆ Δ) & (Δ , refl)})))
  reify {A ∧ B}              s = pair (reify {A} (π₁ s)) (reify {B} (π₂ s))
  reify {⊤}                 s = tt

  reflect⋆ : ∀ {Π Γ} {{Φ : PrimeFilter Γ}} → Γ ⊢⋆ Π → Γ & Φ ⊩⋆ Π
  reflect⋆ {⌀}     ∙        = ∙
  reflect⋆ {Π , A} (ts , t) = reflect⋆ ts , reflect t

  reify⋆ : ∀ {Π Γ} {{Φ : PrimeFilter Γ}} → Γ & Φ ⊩⋆ Π → Γ ⊢⋆ Π
  reify⋆ {⌀}     ∙        = ∙
  reify⋆ {Π , A} (ts , t) = reify⋆ ts , reify t


-- Reflexivity and transitivity.

refl⊩⋆ : ∀ {Γ} {{Φ : PrimeFilter Γ}} → Γ & Φ ⊩⋆ Γ
refl⊩⋆ = reflect⋆ refl⊢⋆

trans⊩⋆ : ∀ {Γ Γ′ Γ″} {{Φ : PrimeFilter Γ}} {{Φ′ : PrimeFilter Γ′}}
           → Γ & Φ ⊩⋆ Γ′ → Γ′ & Φ′ ⊩⋆ Γ″ → Γ & Φ ⊩⋆ Γ″
trans⊩⋆ ts us = reflect⋆ (trans⊢⋆ (reify⋆ ts) (reify⋆ us))


-- Completeness, or quotation.

quot : ∀ {A Γ} {{Φ : PrimeFilter Γ}} → Γ ᴹ⊩ A → Γ ⊢ A
quot t = reify (t refl⊩⋆)


-- Normalisation by evaluation.

norm : ∀ {A Γ} {{Φ : PrimeFilter Γ}} → Γ ⊢ A → Γ ⊢ A
norm = quot ∘ Ono.eval
