module BasicILP.Indirect where

open import Common.Context public


-- Propositions of intuitionistic logic of proofs, without ∨, ⊥, or +.

infixl 7 _∧_
infixr 6 _⦂_
infixr 5 _▷_
data Ty (X : Set) : Set where
  α_  : Atom → Ty X
  _▷_ : Ty X → Ty X → Ty X
  _⦂_ : X → Ty X → Ty X
  _∧_ : Ty X → Ty X → Ty X
  ⊤  : Ty X

module _ {X : Set} where
  infix 5 _⨝_
  _⨝_ : Ty X → Ty X → Ty X
  A ⨝ B = (A ▷ B) ∧ (B ▷ A)


  -- Additional useful propositions.

  _⦂⋆_ : ∀ {n} → VCx X n → VCx (Ty X) n → Cx (Ty X)
  ⌀        ⦂⋆ ⌀       = ⌀
  (𝓉𝓈 , 𝓉) ⦂⋆ (Π , A) = (𝓉𝓈 ⦂⋆ Π) , (𝓉 ⦂ A)
