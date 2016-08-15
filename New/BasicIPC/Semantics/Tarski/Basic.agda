-- Basic Tarski-style denotational semantics.

module New.BasicIPC.Semantics.Tarski.Basic where

open import New.BasicIPC.Syntax.Common public


-- Tarski models.

record Model : Set₁ where
  infix 3 ⊨ᵅ_
  field
    -- Satisfaction for atomic propositions.
    ⊨ᵅ_ : Atom → Set

open Model {{…}} public


-- Satisfaction in a particular model.

infix 3 ⊨_
⊨_ : ∀ {{_ : Model}} → Ty → Set
⊨ α P   = ⊨ᵅ P
⊨ A ▻ B = ⊨ A → ⊨ B
⊨ A ∧ B = ⊨ A × ⊨ B
⊨ ⊤    = 𝟙

infix 3 ⊨⋆_
⊨⋆_ : ∀ {{_ : Model}} → Cx Ty → Set
⊨⋆ ⌀     = 𝟙
⊨⋆ Γ , A = ⊨⋆ Γ × ⊨ A


-- Satisfaction in all models.

infix 3 ᴹ⊨_
ᴹ⊨_ : Ty → Set₁
ᴹ⊨ A = ∀ {{_ : Model}} → ⊨ A

infix 3 _ᴹ⊨_
_ᴹ⊨_ : Cx Ty → Ty → Set₁
Γ ᴹ⊨ A = ∀ {{_ : Model}} → ⊨⋆ Γ → ⊨ A

infix 3 _ᴹ⊨⋆_
_ᴹ⊨⋆_ : Cx Ty → Cx Ty → Set₁
Γ ᴹ⊨⋆ Π = ∀ {{_ : Model}} → ⊨⋆ Γ → ⊨⋆ Π


-- Additional useful equipment.

λˢ : ∀ {{_ : Model}} {A B Γ}
     → (⊨⋆ Γ × ⊨ A → ⊨ B)
     → ⊨⋆ Γ → ⊨ A → ⊨ B
λˢ f γ = λ a → f (γ , a)

_$ˢᶜ_ : ∀ {{_ : Model}} {A B Γ}
        → (⊨⋆ Γ → ⊨ A → ⊨ B)
        → (⊨⋆ Γ → ⊨ A)
        → ⊨⋆ Γ → ⊨ B
(f $ˢᶜ g) γ = (f γ) (g γ)

apˢᶜ : ∀ {{_ : Model}} {A B C Γ}
       → (⊨⋆ Γ → ⊨ A → ⊨ B → ⊨ C)
       → (⊨⋆ Γ → ⊨ A → ⊨ B)
       → (⊨⋆ Γ → ⊨ A)
       → ⊨⋆ Γ → ⊨ C
apˢᶜ f g a γ = ((f γ) (a γ)) ((g γ) (a γ))

_,ˢᶜ_ : ∀ {{_ : Model}} {A B Γ}
        → (⊨⋆ Γ → ⊨ A)
        → (⊨⋆ Γ → ⊨ B)
        → ⊨⋆ Γ → ⊨ A × ⊨ B
(a ,ˢᶜ b) γ = a γ , b γ

π₁ˢᶜ : ∀ {{_ : Model}} {A B Γ}
       → (⊨⋆ Γ → ⊨ A × ⊨ B)
       → ⊨⋆ Γ → ⊨ A
π₁ˢᶜ s γ = π₁ (s γ)

π₂ˢᶜ : ∀ {{_ : Model}} {A B Γ}
       → (⊨⋆ Γ → ⊨ A × ⊨ B)
       → ⊨⋆ Γ → ⊨ B
π₂ˢᶜ s γ = π₂ (s γ)

lookup : ∀ {A Γ} → A ∈ Γ → Γ ᴹ⊨ A
lookup top     (γ , a) = a
lookup (pop i) (γ , b) = lookup i γ
