module A201605.Prelude where

open import Data.Product using (_×_ ; _,_)
open import Data.Unit using (⊤)
import Function
open Function using (_∘_ ; const ; flip)
open import Level using (Level ; _⊔_) renaming (suc to lsuc)
open import Relation.Binary using (IsEquivalence ; IsPreorder ; Preorder ; Setoid)
import Relation.Binary.PropositionalEquality as PE
open PE using (_≡_)


-- TODO: gone from stdlib?
module _ {c ℓ} (s : Setoid c ℓ) where
  open Setoid s

  isPreorder : IsPreorder _≡_ (Setoid._≈_ s)
  isPreorder = record
      { isEquivalence = PE.isEquivalence
      ; reflexive     = reflexive
      ; trans         = IsEquivalence.trans isEquivalence
      }

  preorder : Preorder c c ℓ
  preorder = record
      { isPreorder = isPreorder
      }

-- TODO: omg, stdlib
module PR {p₁ p₂ p₃} (P : Preorder p₁ p₂ p₃) where
  open import Relation.Binary.PropositionalEquality as P using (_≡_)
  open Preorder P

  infix  4 _IsRelatedTo_
  infix  3 _∎
  infixr 2 _∼⟨_⟩_ _≈⟨_⟩_ _≈⟨⟩_ _≡⟨_⟩_
  infix  1 begin_

  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

  data _IsRelatedTo_ (x y : Carrier) : Set p₃ where
    relTo : (x∼y : x ∼ y) → x IsRelatedTo y

  begin_ : ∀ {x y} → x IsRelatedTo y → x ∼ y
  begin relTo x∼y = x∼y

  _∼⟨_⟩_ : ∀ x {y z} → x ∼ y → y IsRelatedTo z → x IsRelatedTo z
  _ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)

  _≈⟨_⟩_ : ∀ x {y z} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≈⟨ x≈y ⟩ relTo y∼z = relTo (trans (reflexive x≈y) y∼z)

  _≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≡⟨ P.refl ⟩ x∼z = x∼z

  _≈⟨⟩_ : ∀ x {y} → x IsRelatedTo y → x IsRelatedTo y
  _ ≈⟨⟩ x∼y = x∼y

  _∎ : ∀ x → x IsRelatedTo x
  _∎ _ = relTo (reflexive (Eq.refl))


-- TODO: ugh, stdlib
module UghStdlib where
  IFun : ∀ {i} → Set i → (ℓ : Level) → Set _
  IFun I ℓ = I → I → Set ℓ → Set ℓ

  record RawFunctor {ℓ} (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
    infixl 4 _<$>_ _<$_
    infixl 1 _<&>_

    field
      _<$>_ : ∀ {A B} → (A → B) → F A → F B

    _<$_ : ∀ {A B} → A → F B → F A
    x <$ y = const x <$> y

    _<&>_ : ∀ {A B} → F A → (A → B) → F B
    _<&>_ = flip _<$>_

  record RawIApplicative {i f} {I : Set i} (F : IFun I f) :
                         Set (i ⊔ lsuc f) where
    infixl 4 _⊛_ _<⊛_ _⊛>_
    infix  4 _⊗_

    field
      pure : ∀ {i A} → A → F i i A
      _⊛_  : ∀ {i j k A B} → F i j (A → B) → F j k A → F i k B

    rawFunctor : ∀ {i j} → RawFunctor (F i j)
    rawFunctor = record
      { _<$>_ = λ g x → pure g ⊛ x
      }

    private
      open module RF {i j : I} =
             RawFunctor (rawFunctor {i = i} {j = j})
             public

    _<⊛_ : ∀ {i j k A B} → F i j A → F j k B → F i k A
    x <⊛ y = const <$> x ⊛ y

    _⊛>_ : ∀ {i j k A B} → F i j A → F j k B → F i k B
    x ⊛> y = flip const <$> x ⊛ y

    _⊗_ : ∀ {i j k A B} → F i j A → F j k B → F i k (A × B)
    x ⊗ y = (_,_) <$> x ⊛ y

    zipWith : ∀ {i j k A B C} → (A → B → C) → F i j A → F j k B → F i k C
    zipWith f x y = f <$> x ⊛ y

  record RawIMonad {i f} {I : Set i} (M : IFun I f) :
                   Set (i ⊔ lsuc f) where
    infixl 1 _>>=_ _>>_ _>=>_
    infixr 1 _=<<_ _<=<_

    field
      return : ∀ {i A} → A → M i i A
      _>>=_  : ∀ {i j k A B} → M i j A → (A → M j k B) → M i k B

    _>>_ : ∀ {i j k A B} → M i j A → M j k B → M i k B
    m₁ >> m₂ = m₁ >>= λ _ → m₂

    _=<<_ : ∀ {i j k A B} → (A → M j k B) → M i j A → M i k B
    f =<< c = c >>= f

    _>=>_ : ∀ {i j k a} {A : Set a} {B C} →
            (A → M i j B) → (B → M j k C) → (A → M i k C)
    f >=> g = _=<<_ g ∘ f

    _<=<_ : ∀ {i j k B C a} {A : Set a} →
            (B → M j k C) → (A → M i j B) → (A → M i k C)
    g <=< f = f >=> g

    join : ∀ {i j k A} → M i j (M j k A) → M i k A
    join m = m >>= Function.id

    rawIApplicative : RawIApplicative M
    rawIApplicative = record
      { pure = return
      ; _⊛_  = λ f x → f >>= λ f' → x >>= λ x' → return (f' x')
      }

    open RawIApplicative rawIApplicative public

  RawMonad : ∀ {f} → (Set f → Set f) → Set _
  RawMonad M = RawIMonad {I = ⊤} (λ _ _ → M)

  module RawMonad {f} {M : Set f → Set f}
                  (Mon : RawMonad M) where
    open RawIMonad Mon public

open UghStdlib using (RawMonad) public
