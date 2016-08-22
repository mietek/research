module BasicILP.Indirect where

open import Common.Context public


-- Propositions of intuitionistic logic of proofs, without ∨, ⊥, or +.

infixr 9 _⦂_
infixl 8 _∧_
infixr 6 _▻_
data Ty (X : Set) : Set where
  α_  : Atom → Ty X
  _▻_ : Ty X → Ty X → Ty X
  _⦂_ : X → Ty X → Ty X
  _∧_ : Ty X → Ty X → Ty X
  ⊤  : Ty X

module _ {X : Set} where
  infix 6 _▻◅_
  _▻◅_ : Ty X → Ty X → Ty X
  A ▻◅ B = (A ▻ B) ∧ (B ▻ A)


  -- Additional useful propositions.

  _⦂⋆_ : ∀ {n} → VCx X n → VCx (Ty X) n → Cx (Ty X)
  ⌀        ⦂⋆ ⌀       = ⌀
  (TS , T) ⦂⋆ (Ξ , A) = (TS ⦂⋆ Ξ) , (T ⦂ A)
