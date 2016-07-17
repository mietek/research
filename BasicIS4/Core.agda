module BasicIS4.Core where

open import Common.Context public


-- Propositions of intuitionistic modal logic S4, without disjunction, falsehood, or possibility.

infixl 7 _∧_
infixr 5 _▷_
data Ty : Set where
  α_  : Atom → Ty
  _▷_ : Ty → Ty → Ty
  □_  : Ty → Ty
  _∧_ : Ty → Ty → Ty
  ⊤  : Ty

infix 5 _⨝_
_⨝_ : Ty → Ty → Ty
A ⨝ B = (A ▷ B) ∧ (B ▷ A)


-- Additional useful propositions.

infixr 5 _▷⋯▷_
_▷⋯▷_ : Cx Ty → Ty → Ty
⌀       ▷⋯▷ B = B
(Π , A) ▷⋯▷ B = Π ▷⋯▷ (A ▷ B)

□⋆_ : Cx Ty → Cx Ty
□⋆ ⌀       = ⌀
□⋆ (Π , A) = □⋆ Π , □ A

dist□⋆ₗ : ∀ Π Π′ → □⋆ (Π ⧺ Π′) ≡ (□⋆ Π) ⧺ (□⋆ Π′)
dist□⋆ₗ Π ⌀        = refl
dist□⋆ₗ Π (Π′ , A) = cong₂ _,_ (dist□⋆ₗ Π Π′) refl
