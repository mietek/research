module A201605.AbelChapmanExtended.StrongBisimilarity where

open import Function using (_∘_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans)
open import Size using (Size ; Size<_ ; ∞)
import Relation.Binary.PreorderReasoning as PR

open import A201605.AbelChapmanExtended.Delay




mutual
  data _≈_ {i A} : Delay ∞ A → Delay ∞ A → Set where
    ≈now   :                (a : A)         → now a    ≈ now a
    ≈later : ∀ {a∞ a∞′} → a∞ ∞≈⟨ i ⟩≈ a∞′ → later a∞ ≈ later a∞′

  _≈⟨_⟩≈_ : ∀ {A} → Delay ∞ A → Size → Delay ∞ A → Set
  _≈⟨_⟩≈_ {A} a? i a?′ = _≈_ {i} {A} a? a?′

  record _∞≈⟨_⟩≈_ {A} (a∞ : ∞Delay ∞ A) (i : Size) (a∞′ : ∞Delay ∞ A) : Set where
    coinductive
    field
      ≈force : {j : Size< i} → force a∞ ≈⟨ j ⟩≈ force a∞′

_∞≈_ : ∀ {i A} → ∞Delay ∞ A → ∞Delay ∞ A → Set
_∞≈_ {i} {A} a∞ a∞′ = _∞≈⟨_⟩≈_ {A} a∞ i a∞′

infix 5 _≈⟨_⟩≈_ _∞≈⟨_⟩≈_ _∞≈_

open _∞≈⟨_⟩≈_ public


mutual
  ≈refl : ∀ {i A} {a? : Delay ∞ A} → a? ≈⟨ i ⟩≈ a?
  ≈refl {a? = now a}    = ≈now a
  ≈refl {a? = later a∞} = ≈later ∞≈refl

  ∞≈refl : ∀ {i A} {a∞ : ∞Delay ∞ A} → a∞ ∞≈⟨ i ⟩≈ a∞
  ≈force (∞≈refl) = ≈refl


mutual
  ≈sym : ∀ {i A} {a? a?′ : Delay ∞ A} → a? ≈⟨ i ⟩≈ a?′ → a?′ ≈⟨ i ⟩≈ a?
  ≈sym (≈now a)      = ≈now a
  ≈sym (≈later a≈a′) = ≈later (∞≈sym a≈a′)

  ∞≈sym : ∀ {i A} {a∞ a∞′ : ∞Delay ∞ A} → a∞ ∞≈⟨ i ⟩≈ a∞′ → a∞′ ∞≈⟨ i ⟩≈ a∞
  ≈force (∞≈sym a≈a′) = ≈sym (≈force a≈a′)


mutual
  ≈trans : ∀ {i A} {a? a?′ a?″ : Delay ∞ A} →
           a? ≈⟨ i ⟩≈ a?′ → a?′ ≈⟨ i ⟩≈ a?″ → a? ≈⟨ i ⟩≈ a?″
  ≈trans (≈now a)      (≈now .a)      = ≈now a
  ≈trans (≈later a≈a′) (≈later a′≈a″) = ≈later (∞≈trans a≈a′ a′≈a″)

  ∞≈trans : ∀ {i A} {a∞ a∞′ a∞″ : ∞Delay ∞ A} →
            a∞ ∞≈⟨ i ⟩≈ a∞′ → a∞′ ∞≈⟨ i ⟩≈ a∞″ → a∞ ∞≈⟨ i ⟩≈ a∞″
  ≈force (∞≈trans a≈a′ a′≈a″) = ≈trans (≈force a≈a′) (≈force a′≈a″)


mutual
  bind-assoc : ∀ {i A B C} (a? : Delay ∞ A) →
               {f : A → Delay ∞ B} {g : B → Delay ∞ C} →
               ((a? >>= f) >>= g) ≈⟨ i ⟩≈ (a? >>= λ a → f a >>= g)
  bind-assoc (now a)    = ≈refl
  bind-assoc (later a∞) = ≈later (∞bind-assoc a∞)

  ∞bind-assoc : ∀ {i A B C} (a∞ : ∞Delay ∞ A) →
                {f : A → Delay ∞ B} {g : B → Delay ∞ C} →
                ((a∞ ∞>>= f) ∞>>= g) ∞≈⟨ i ⟩≈ (a∞ ∞>>= λ a → f a >>= g)
  ≈force (∞bind-assoc a∞) = bind-assoc (force a∞)


mutual
  bind-cong-l : ∀ {i A B} {a? a?′ : Delay ∞ A} →
                a? ≈⟨ i ⟩≈ a?′ → {f : A → Delay ∞ B} →
                (a? >>= f) ≈⟨ i ⟩≈ (a?′ >>= f)
  bind-cong-l (≈now a)      = ≈refl
  bind-cong-l (≈later a≈a′) = ≈later (∞bind-cong-l a≈a′)

  ∞bind-cong-l : ∀ {i A B} {a∞ a∞′ : ∞Delay ∞ A} →
                 a∞ ∞≈⟨ i ⟩≈ a∞′ → {f : A → Delay ∞ B} →
                 (a∞ ∞>>= f) ∞≈⟨ i ⟩≈ (a∞′ ∞>>= f)
  ≈force (∞bind-cong-l a≈a′) = bind-cong-l (≈force a≈a′)


mutual
  bind-cong-r : ∀ {i A B} (a? : Delay ∞ A) {f g : A → Delay ∞ B} →
                (∀ a → (f a) ≈⟨ i ⟩≈ (g a)) →
                (a? >>= f) ≈⟨ i ⟩≈ (a? >>= g)
  bind-cong-r (now a)    h = h a
  bind-cong-r (later a∞) h = ≈later (∞bind-cong-r a∞ h)

  ∞bind-cong-r : ∀ {i A B} (a∞ : ∞Delay ∞ A) {f g : A → Delay ∞ B} →
                 (∀ a → (f a) ≈⟨ i ⟩≈ (g a)) →
                 (a∞ ∞>>= f) ∞≈⟨ i ⟩≈ (a∞ ∞>>= g)
  ≈force (∞bind-cong-r a∞ h) = bind-cong-r (force a∞) h


≈setoid : (i : Size) (A : Set) → Setoid _ _
≈setoid i A = record
  { Carrier       = Delay ∞ A
  ; _≈_           = _≈_ {i}
  ; isEquivalence = record
    { refl  = ≈refl
    ; sym   = ≈sym
    ; trans = ≈trans
    }
  }

∞≈setoid : (i : Size) (A : Set) → Setoid _ _
∞≈setoid i A = record
  { Carrier       = ∞Delay ∞ A
  ; _≈_           = _∞≈_ {i}
  ; isEquivalence = record
    { refl  = ∞≈refl
    ; sym   = ∞≈sym
    ; trans = ∞≈trans
    }
  }

module ≈-Reasoning {i A} where
  open PR (Setoid.preorder (≈setoid i A)) public
    using (_∎)
    renaming (_≈⟨⟩_ to _≡⟨⟩_ ; _≈⟨_⟩_ to _≡⟨_⟩_ ; _∼⟨_⟩_ to _≈⟨_⟩_ ; begin_ to proof_)

module ∞≈-Reasoning {i A} where
  open PR (Setoid.preorder (∞≈setoid i A)) public
    using (_∎)
    renaming (_≈⟨⟩_ to _≡⟨⟩_ ; _≈⟨_⟩_ to _≡⟨_⟩_ ; _∼⟨_⟩_ to _∞≈⟨_⟩_ ; begin_ to proof_)




sym-bind-assoc : ∀ {i A B C} (a? : Delay ∞ A) →
                 {f : A → Delay ∞ B} {g : B → Delay ∞ C} →
                 (a? >>= λ a → f a >>= g) ≈⟨ i ⟩≈ ((a? >>= f) >>= g)
sym-bind-assoc a? = ≈sym (bind-assoc a?)

syntax bind-assoc     a?             = ⋘ a?
syntax sym-bind-assoc a?             = ⋙ a?
syntax bind-cong-r    a? (λ a → b?) = a ⇚ a? ⁏ b?
syntax bind-cong-l    a≈a′           = ∵ a≈a′

infix 35 bind-assoc  sym-bind-assoc
infix 30 bind-cong-r bind-cong-l
