{-# OPTIONS --sized-types #-}

module A201605.AbelChapmanExtended.Delay where

open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (ℕ ; zero ; suc)
open import Size using (Size ; Size<_ ; ∞)

open import A201605.Prelude




mutual
  data Delay (i : Size) (A : Set) : Set where
    now   : (a : A)           → Delay i A
    later : (a∞ : ∞Delay i A) → Delay i A

  record ∞Delay (i : Size) (A : Set) : Set where
    coinductive
    field
      force : {j : Size< i} → Delay j A

open ∞Delay public


mutual
  bind : ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
  bind (now a)    f = f a
  bind (later a∞) f = later (∞bind a∞ f)

  ∞bind : ∀ {i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
  force (∞bind a∞ f) = bind (force a∞) f


delayMonad : ∀ {i} → RawMonad (Delay i)
delayMonad {i} = record
  { return = now
  ; _>>=_  = bind {i}
  }

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i}) public
    using (_>>=_) renaming (_⊛_ to _<*>_)


_<$>_ : ∀ {i A B} → (A → B) → Delay i A → Delay i B
f <$> a? = a? >>= λ a → now (f a)

_∞>>=_ : ∀ {i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
_∞>>=_ = ∞bind

_∞<$>_ : ∀ {i A B} → (A → B) → ∞Delay i A → ∞Delay i B
f ∞<$> a∞ = a∞ ∞>>= λ a → now (f a)

infixl 1 _∞>>=_
infixl 15 _<$>_ _∞<$>_




syntax bind  a? (λ a → b?) = a  ← a? ⁏ b?
syntax ∞bind a∞ (λ a → b?) = a ∞← a∞ ⁏ b?

infix 10 bind ∞bind
