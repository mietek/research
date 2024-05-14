module A201602.LFFOL where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _<_)
open import Data.Product
  using (Σ; _×_)
open import Data.Sum
  using (_⊎_)
open import Relation.Binary.PropositionalEquality
  using (_≡_)
open import Relation.Nullary
  using (¬_)


Var : Set
Var = ℕ

data ι : Set where
  ‘zero’ : ι
  ‘suc’  : ι → ι
  _‘+’_  : ι → ι → ι
  _‘*’_  : ι → ι → ι

data o : Set where
  _‘≡’_ : ι → ι → o
  _‘<’_ : ι → ι → o
  ‘¬’_  : o → o
  _‘∧’_ : o → o → o
  _‘∨’_ : o → o → o
  _‘→’_ : o → o → o
  ‘∀’_  : (ι → o) → o
  ‘∃’_  : (ι → o) → o

δ⟦_⟧ι : ι → ℕ
δ⟦ ‘zero’  ⟧ι = zero
δ⟦ ‘suc’ t ⟧ι = suc δ⟦ t ⟧ι
δ⟦ t ‘+’ u ⟧ι = δ⟦ t ⟧ι + δ⟦ u ⟧ι
δ⟦ t ‘*’ u ⟧ι = δ⟦ t ⟧ι * δ⟦ u ⟧ι

δ⟦_⟧o : o → Set
δ⟦ t ‘≡’ u ⟧o = δ⟦ t ⟧ι ≡ δ⟦ u ⟧ι
δ⟦ t ‘<’ u ⟧o = δ⟦ t ⟧ι < δ⟦ u ⟧ι
δ⟦ ‘¬’ φ   ⟧o = ¬ δ⟦ φ ⟧o
δ⟦ φ ‘∧’ ψ ⟧o = δ⟦ φ ⟧o × δ⟦ ψ ⟧o
δ⟦ φ ‘∨’ ψ ⟧o = δ⟦ φ ⟧o ⊎ δ⟦ ψ ⟧o
δ⟦ φ ‘→’ ψ ⟧o = δ⟦ φ ⟧o → δ⟦ ψ ⟧o
δ⟦ ‘∀’ f   ⟧o = ∀{x : ι} → δ⟦ f x ⟧o
δ⟦ ‘∃’ f   ⟧o = Σ ι (λ x → δ⟦ f x ⟧o)
