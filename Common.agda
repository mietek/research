module Common where

import Axiom.Extensionality.Propositional as A

open import Data.List public
  using (List ; [] ; _∷_)

open import Data.Nat public
  using (ℕ ; zero ; suc)

open import Data.Product public
  using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)

open import Data.Sum public
  using (_⊎_ ; inj₁ ; inj₂)

open import Data.Unit public
  using ()
  renaming (⊤ to 𝟙 ; tt to unit)

open import Function public
  using (_∘_ ; _$_ ; flip ; id)

open import Level public
  using (Level ; _⊔_ ; Setω)
  renaming (zero to ℓzero ; suc to ℓsuc)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; refl ; cong ; cong₂ ; cong-app ; subst ; sym ; trans ; module ≡-Reasoning)

open import Relation.Binary.HeterogeneousEquality public
  using (_≅_)
  renaming (≡-to-≅ to ≡→≅ ; ≅-to-≡ to ≅→≡ ; cong to cong≅ ; cong₂ to cong₂≅)


----------------------------------------------------------------------------------------------------

Extensionality : Setω
Extensionality = ∀ {𝓍 𝓎} → A.Extensionality 𝓍 𝓎

Extensionality′ : Setω
Extensionality′ = ∀ {𝓍 𝓎} → A.ExtensionalityImplicit 𝓍 𝓎

implify : Extensionality → Extensionality′
implify ⚠ = A.implicit-extensionality ⚠


----------------------------------------------------------------------------------------------------

record Irrelevant {𝓍} (X : Set 𝓍) : Set 𝓍 where
  field .irrelevant : X

open Irrelevant public

private
  data Empty : Set where

𝟘 : Set
𝟘 = Irrelevant Empty

{-# DISPLAY Irrelevant Empty = 𝟘 #-}

abort : ∀ {𝓍} {X : Set 𝓍} → 𝟘 → X
abort ()

infix 3 ¬_
¬_ : ∀ {𝓍} → Set 𝓍 → Set 𝓍
¬ X = X → 𝟘

_↯_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → X → ¬ X → Y
x ↯ ¬x = abort (¬x x)

data Dec {𝓍} (X : Set 𝓍) : Set 𝓍 where
  yes : X → Dec X
  no  : ¬ X → Dec X


----------------------------------------------------------------------------------------------------

-- uniqueness of proofs for empty
uni𝟘 : ∀ (z z′ : 𝟘) → z ≡ z′
uni𝟘 () ()

-- uniqueness of proofs for negations
uni¬ : ∀ {𝓍} {X : Set 𝓍} → ∀ (f f′ : ¬ X) → f ≡ f′
uni¬ f f′ = refl

-- uniqueness of proofs for functions
module _ (⚠ : Extensionality) where
  uni→ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → (∀ (y y′ : Y) → y ≡ y′) → ∀ (f f′ : X → Y) → f ≡ f′
  uni→ uniY f f′ = ⚠ λ x → uniY (f x) (f′ x)

-- uniqueness of proofs for propositional equality
uni≡ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} (eq eq′ : x ≡ x′) → eq ≡ eq′
uni≡ refl refl = refl


----------------------------------------------------------------------------------------------------

coe : ∀ {𝓍} {X Y : Set 𝓍} → X ≡ Y → X → Y
coe = subst id

infixl 9 _&_
_&_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (f : X → Y) {x x′ : X} → x ≡ x′ → f x ≡ f x′
_&_ = cong

infixl 8 _⊗_
_⊗_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {f g : X → Y} {x y : X} → f ≡ g → x ≡ y → f x ≡ g y
refl ⊗ refl = refl

infix 9 _⁻¹
_⁻¹ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} → x ≡ x′ → x′ ≡ x
_⁻¹ = sym

infixr 4 _⋮_
_⋮_ : ∀ {𝓍} {X : Set 𝓍} {x x′ x″ : X} → x ≡ x′ → x′ ≡ x″ → x ≡ x″
_⋮_ = trans

cong-app′ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} {f g : ∀ {x : X} → Y x} →
            (λ {x : X} → f {x}) ≡ (λ {x : X} → g {x}) → (∀ {x : X} → f {x} ≡ g {x})
cong-app′ refl {x} = refl


----------------------------------------------------------------------------------------------------

recℕ : ∀ {𝓍} {X : Set 𝓍} → ℕ → X → (ℕ → X → X) → X
recℕ zero    z s = z
recℕ (suc n) z s = s n (recℕ n z s)


----------------------------------------------------------------------------------------------------

module _ {𝓍} {X : Set 𝓍} where
  -- intrinsically well-typed de Bruijn indices
  infix 4 _∋_
  data _∋_ : List X → X → Set 𝓍 where
    zero : ∀ {Γ A} → A ∷ Γ ∋ A
    suc  : ∀ {Γ A B} (i : Γ ∋ A) → B ∷ Γ ∋ A

  injsuc : ∀ {Γ} {A B : X} {i i′ : Γ ∋ A} → _∋_.suc {B = B} i ≡ suc i′ → i ≡ i′
  injsuc refl = refl

  -- order-preserving embeddings
  infix 4 _⊆_
  data _⊆_ : List X → List X → Set 𝓍 where
    stop : [] ⊆ []
    drop : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) → Γ ⊆ A ∷ Γ′
    keep : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) → A ∷ Γ ⊆ A ∷ Γ′

  id⊆ : ∀ {Γ} → Γ ⊆ Γ
  id⊆ {[]}    = stop
  id⊆ {A ∷ Γ} = keep id⊆

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ = id⊆

  wk⊆ : ∀ {Γ A} → Γ ⊆ A ∷ Γ
  wk⊆ = drop id⊆

  _∘⊆_ : ∀ {Γ Γ′ Γ″} → Γ′ ⊆ Γ″ → Γ ⊆ Γ′ → Γ ⊆ Γ″
  stop      ∘⊆ e        = e
  (drop e′) ∘⊆ e        = drop (e′ ∘⊆ e)
  (keep e′) ∘⊆ (drop e) = drop (e′ ∘⊆ e)
  (keep e′) ∘⊆ (keep e) = keep (e′ ∘⊆ e)

  trans⊆ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  trans⊆ = flip _∘⊆_

  -- renaming of indices
  ren∋ : ∀ {Γ Γ′} {A : X} → Γ ⊆ Γ′ → Γ ∋ A → Γ′ ∋ A
  ren∋ stop     i       = i
  ren∋ (drop e) i       = suc (ren∋ e i)
  ren∋ (keep e) zero    = zero
  ren∋ (keep e) (suc i) = suc (ren∋ e i)

  weak∋ : ∀ {Γ} {A B : X} → Γ ∋ B → A ∷ Γ ∋ B
  weak∋ i = ren∋ wk⊆ i

  injren∋ : ∀ {Γ Γ′} {A : X} {e : Γ ⊆ Γ′} {i i′ : Γ ∋ A} → ren∋ e i ≡ ren∋ e i′ → i ≡ i′
  injren∋ {e = stop}   {i}     {i′}     eq   = eq
  injren∋ {e = drop e} {i}     {i′}     eq   = injren∋ (injsuc eq)
  injren∋ {e = keep e} {zero}  {zero}   refl = refl
  injren∋ {e = keep e} {suc i} {suc i′} eq   = suc & (injren∋ (injsuc eq))

  -- TODO: delete?
  unren∋ : ∀ {Γ Γ′} {A : X} (e : Γ ⊆ Γ′) (i′ : Γ′ ∋ A) → Dec (Σ (Γ ∋ A) λ i → i′ ≡ ren∋ e i)
  unren∋ stop     i′       = yes (i′ , refl)
  unren∋ (drop e) zero     = no λ ()
  unren∋ (drop e) (suc i′) with unren∋ e i′
  ... | no ¬p                = no λ { (i , refl) → (i , refl) ↯ ¬p }
  ... | yes (i , refl)       = yes (i , refl)
  unren∋ (keep e) zero     = yes (zero , refl)
  unren∋ (keep e) (suc i′) with unren∋ e i′
  ... | no ¬p                = no λ { (suc i , refl) → (i , refl) ↯ ¬p }
  ... | yes (i , refl)       = yes (suc i , refl)

  infix 4 _≟∋_
  _≟∋_ : ∀ {Γ A} (i i′ : Γ ∋ A) → Dec (i ≡ i′)
  zero  ≟∋ zero   = yes refl
  zero  ≟∋ suc i′ = no λ ()
  suc i ≟∋ zero   = no λ ()
  suc i ≟∋ suc i′ with i ≟∋ i′
  ... | yes refl    = yes refl
  ... | no ¬eq      = no λ { refl → refl ↯ ¬eq }


----------------------------------------------------------------------------------------------------
