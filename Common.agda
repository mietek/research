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

module CtxKit (Ty : Set) where
  Ctx : Set
  Ctx = List Ty


----------------------------------------------------------------------------------------------------

  module ⊢*Kit
    (Tm : Ctx → Ty → Set)
      where
    private
      infix 3 _⊢_
      _⊢_ = Tm

    ty : ∀ {Γ A} → Γ ⊢ A → Ty
    ty {A = A} t = A

    -- simultaneous substitutions
    infix 3 _⊢*_
    data _⊢*_ (Γ : Ctx) : Ctx → Set where
      []  : Γ ⊢* []
      _∷_ : ∀ {A Δ} (t : Γ ⊢ A) (ts : Γ ⊢* Δ) → Γ ⊢* A ∷ Δ


----------------------------------------------------------------------------------------------------

    module RenKit
      (⌜v⌝ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A)
      (ren : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A)
        where
      weak : ∀ {Γ A B} → Γ ⊢ B → A ∷ Γ ⊢ B
      weak t = ren wk⊆ t

      -- Kovacs: flip _ₛ∘ₑ_
      rens : ∀ {Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⊢* Δ → Γ′ ⊢* Δ
      rens e []       = []
      rens e (t ∷ ts) = ren e t ∷ rens e ts

      weaks : ∀ {Γ Δ A} → Γ ⊢* Δ → A ∷ Γ ⊢* Δ
      weaks ts = rens wk⊆ ts

      lifts : ∀ {Γ Δ A} → Γ ⊢* Δ → A ∷ Γ ⊢* A ∷ Δ
      lifts ts = ⌜v⌝ zero ∷ weaks ts

      -- Kovacs: ⌜_⌝ᵒᵖᵉ
      vars : ∀ {Γ Γ′} → Γ ⊆ Γ′ → Γ′ ⊢* Γ
      vars stop     = []
      vars (drop e) = weaks (vars e)
      vars (keep e) = lifts (vars e)

      -- TODO: check if varying this affects anything
      ids : ∀ {Γ} → Γ ⊢* Γ
      ids {[]}    = []
      ids {A ∷ Γ} = lifts ids
      -- ids = vars id⊆

      refls : ∀ {Γ} → Γ ⊢* Γ
      refls = ids

      -- substitution of indices
      sub∋ : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ∋ A → Ξ ⊢ A
      sub∋ (s ∷ ss) zero    = s
      sub∋ (s ∷ ss) (suc i) = sub∋ ss i


----------------------------------------------------------------------------------------------------

      module SubKit
        (sub : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ⊢ A → Ξ ⊢ A)
          where
        -- Kovacs: flip _∘ₛ_
        subs : ∀ {Γ Ξ Δ} → Ξ ⊢* Γ → Γ ⊢* Δ → Ξ ⊢* Δ
        subs ss []       = []
        subs ss (t ∷ ts) = sub ss t ∷ subs ss ts

        transs : ∀ {Γ Ξ Δ} → Ξ ⊢* Γ → Γ ⊢* Δ → Ξ ⊢* Δ
        transs = subs

        _∘s_ : ∀ {Γ Ξ Δ} → Γ ⊢* Δ → Ξ ⊢* Γ → Ξ ⊢* Δ
        _∘s_ = flip transs

        _[_] : ∀ {Γ A B} → A ∷ Γ ⊢ B → Γ ⊢ A → Γ ⊢ B
        t [ s ] = sub (s ∷ ids) t

        _[_∣_] : ∀ {Γ A B C} → B ∷ A ∷ Γ ⊢ C → Γ ⊢ A → Γ ⊢ B → Γ ⊢ C
        t [ s₁ ∣ s₂ ] = sub (s₂ ∷ s₁ ∷ ids) t

        -- Kovacs: _ₑ∘ₛ_; flip?
        gets : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⊢* Δ′ → Γ ⊢* Δ
        gets stop     ts       = ts
        gets (drop e) (t ∷ ts) = gets e ts
        gets (keep e) (t ∷ ts) = t ∷ gets e ts


----------------------------------------------------------------------------------------------------

    module NFKit
      (NF  : ∀ {Γ A} → Γ ⊢ A → Set)
      (NNF : ∀ {Γ A} → Γ ⊢ A → Set)
        where
      data NF* {Γ} : ∀ {Δ} → Γ ⊢* Δ → Set where
        []  : NF* []
        _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} → NF t → NF* ts → NF* (t ∷ ts)

      data NNF* {Γ} : ∀ {Δ} → Γ ⊢* Δ → Set where
        []  : NNF* []
        _∷_ : ∀ {A Δ} {t : Γ ⊢ A} {ts : Γ ⊢* Δ} → NNF t → NNF* ts → NNF* (t ∷ ts)


----------------------------------------------------------------------------------------------------

    module ≝Kit
      {_≝_    : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set}
      (refl≝  : ∀ {Γ A} {t : Γ ⊢ A} → t ≝ t)
      (sym≝   : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → t′ ≝ t)
      (trans≝ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ≝ t′ → t′ ≝ t″ → t ≝ t″)
        where
      ≡→≝ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≡ t′ → t ≝ t′
      ≡→≝ refl = refl≝

      module ≝-Reasoning where
        infix 1 begin_
        begin_ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → t ≝ t′
        begin_ deq = deq

        infixr 2 _≝⟨_⟩_
        _≝⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ≝ t′ → t′ ≝ t″ → t ≝ t″
        t ≝⟨ deq ⟩ deq′ = trans≝ deq deq′

        infixr 2 _≝˘⟨_⟩_
        _≝˘⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t′ ≝ t → t′ ≝ t″ → t ≝ t″
        t ≝˘⟨ deq ⟩ deq′ = trans≝ (sym≝ deq) deq′

        infixr 2 _≡⟨⟩_
        _≡⟨⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′} → t ≝ t′ → t ≝ t′
        t ≡⟨⟩ deq = deq

        infixr 2 _≡⟨_⟩_
        _≡⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ≡ t′ → t′ ≝ t″ → t ≝ t″
        t ≡⟨ eq ⟩ deq′ = trans≝ (≡→≝ eq) deq′

        infixr 2 _≡˘⟨_⟩_
        _≡˘⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t′ ≡ t → t′ ≝ t″ → t ≝ t″
        t ≡˘⟨ eq ⟩ deq′ = trans≝ (≡→≝ (sym eq)) deq′

        infix 3 _∎
        _∎ : ∀ {Γ A} (t : Γ ⊢ A) → t ≝ t
        t ∎ = refl≝


----------------------------------------------------------------------------------------------------

    module ⇒Kit
      (Red : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set)
        where
      private
        infix 4 _⇒_
        _⇒_ = Red

      -- reducible forms
      RF : ∀ {Γ A} → Γ ⊢ A → Set
      RF t = Σ _ λ t′ → t ⇒ t′

      -- irreducible forms
      ¬R : ∀ {Γ A} → Γ ⊢ A → Set
      ¬R t = ∀ {t′} → ¬ t ⇒ t′

      -- iterated reduction
      infix 4 _⇒*_
      data _⇒*_ {Γ A} : Γ ⊢ A → Γ ⊢ A → Set where
        done : ∀ {t} → t ⇒* t
        step : ∀ {t t′ t″} (r : t ⇒ t′) (rs : t′ ⇒* t″) → t ⇒* t″

      trans⇒* : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒* t′ → t′ ⇒* t″ → t ⇒* t″
      trans⇒* done        rs′ = rs′
      trans⇒* (step r rs) rs′ = step r (trans⇒* rs rs′)

      ≡→⇒* : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≡ t′ → t ⇒* t′
      ≡→⇒* refl = done

      module ⇒-Reasoning where
        infix 1 begin_
        begin_ : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ⇒* t′ → t ⇒* t′
        begin_ rs = rs

        infixr 2 _⇒*⟨_⟩_
        _⇒*⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ⇒* t′ → t′ ⇒* t″ → t ⇒* t″
        t ⇒*⟨ rs ⟩ rs′ = trans⇒* rs rs′

        infixr 2 _⇒⟨_⟩_
        _⇒⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ⇒ t′ → t′ ⇒* t″ → t ⇒* t″
        t ⇒⟨ r ⟩ rs = step r rs

        infixr 2 _≡⟨⟩_
        _≡⟨⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′} → t ⇒* t′ → t ⇒* t′
        t ≡⟨⟩ rs = rs

        infixr 2 _≡⟨_⟩_
        _≡⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t ≡ t′ → t′ ⇒* t″ → t ⇒* t″
        t ≡⟨ eq ⟩ rs′ = trans⇒* (≡→⇒* eq) rs′

        infixr 2 _≡˘⟨_⟩_
        _≡˘⟨_⟩_ : ∀ {Γ A} (t : Γ ⊢ A) {t′ t″} → t′ ≡ t → t′ ⇒* t″ → t ⇒* t″
        t ≡˘⟨ eq ⟩ rs′ = trans⇒* (≡→⇒* (sym eq)) rs′

        infix 3 _∎
        _∎ : ∀ {Γ A} (t : Γ ⊢ A) → t ⇒* t
        t ∎ = done

      module _ (⚠ : Extensionality) where
        uni¬RF : ∀ {Γ A} {t : Γ ⊢ A} (¬p ¬p′ : ¬ RF t) → ¬p ≡ ¬p′
        uni¬RF = uni→ ⚠ uni𝟘


----------------------------------------------------------------------------------------------------

      module ¬RKit
        {NF      : ∀ {Γ A} → Γ ⊢ A → Set}
        (NF→¬R  : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t)
          where
        ¬RF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → ¬R t
        ¬RF→¬R ¬p r = (_ , r) ↯ ¬p

        ¬R→¬RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬R t → ¬ RF t
        ¬R→¬RF ¬r (_ , r) = r ↯ ¬r

        RF→¬NF : ∀ {Γ A} {t : Γ ⊢ A} → RF t → ¬ NF t
        RF→¬NF (_ , r) p = r ↯ NF→¬R p

        NF→¬RF : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬ RF t
        NF→¬RF = ¬R→¬RF ∘ NF→¬R

        -- progress
        data Prog {Γ A} (t : Γ ⊢ A) : Set where
          done : NF t → Prog t
          step : ∀ {t′ : Γ ⊢ A} → t ⇒ t′ → Prog t

        -- NOTE: the above is slightly more convenient than the equivalent below
        -- step : Σ (Γ ⊢ A) (λ t′ → t ⇒ t′) → Prog t

        recProg : ∀ {𝓍} {X : Set 𝓍} {Γ A} {t : Γ ⊢ A} → Prog t → (NF t → X) → (RF t → X) → X
        recProg (done p) f₁ f₂ = f₁ p
        recProg (step r) f₁ f₂ = f₂ (_ , r)


----------------------------------------------------------------------------------------------------

        module ProgKit
          (prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t)
            where
          NF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (NF t)
          NF? t = recProg (prog⇒ t) yes (no ∘ RF→¬NF)

          RF? : ∀ {Γ A} (t : Γ ⊢ A) → Dec (RF t)
          RF? t = recProg (prog⇒ t) (no ∘ NF→¬RF) yes

          ¬NF→RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ NF t → RF t
          ¬NF→RF ¬p = recProg (prog⇒ _) (_↯ ¬p) id

          ¬RF→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → NF t
          ¬RF→NF ¬p = recProg (prog⇒ _) id (_↯ ¬p)

          ¬R→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬R t → NF t
          ¬R→NF = ¬RF→NF ∘ ¬R→¬RF

        module NF?Kit
          (NF?     : ∀ {Γ A} (t : Γ ⊢ A) → Dec (NF t))
          (¬NF→RF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ NF t → RF t)
            where
          prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
          prog⇒ t    with NF? t
          ... | yes p   = done p
          ... | no ¬p   = let _ , r = ¬NF→RF ¬p
                            in step r

          open ProgKit prog⇒ public hiding (NF? ; ¬NF→RF)

        module RF?Kit
          (RF?     : ∀ {Γ A} (t : Γ ⊢ A) → Dec (RF t))
          (¬RF→NF : ∀ {Γ A} {t : Γ ⊢ A} → ¬ RF t → NF t)
            where
          prog⇒ : ∀ {Γ A} (t : Γ ⊢ A) → Prog t
          prog⇒ t          with RF? t
          ... | yes (_ , r)   = step r
          ... | no ¬p         = done (¬RF→NF ¬p)

          open ProgKit prog⇒ public hiding (RF? ; ¬RF→NF)


----------------------------------------------------------------------------------------------------

      module ⇒*Kit
        {NF     : ∀ {Γ A} → Γ ⊢ A → Set}
        (NF→¬R : ∀ {Γ A} {t : Γ ⊢ A} → NF t → ¬R t)
        (det⇒  : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒ t″ → t′ ≡ t″)
        (uni⇒  : ∀ {Γ A} {t t′ : Γ ⊢ A} (r r′ : t ⇒ t′) → r ≡ r′)
          where
        skip⇒* : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒ t′ → t ⇒* t″ → NF t″ → t′ ⇒* t″
        skip⇒* r done          p″ = r ↯ NF→¬R p″
        skip⇒* r (step r′ rs′) p″ with det⇒ r r′
        ... | refl                  = rs′

        -- determinism
        det⇒* : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ⇒* t′ → NF t′ → t ⇒* t″ → NF t″ → t′ ≡ t″
        det⇒* done        p′ done          p″ = refl
        det⇒* done        p′ (step r′ rs′) p″ = r′ ↯ NF→¬R p′
        det⇒* (step r rs) p′ rs′           p″ = det⇒* rs p′ (skip⇒* r rs′ p″) p″

        -- uniqueness of proofs
        uni⇒* : ∀ {Γ A} {t t′ : Γ ⊢ A} (rs rs′ : t ⇒* t′) → NF t′ → rs ≡ rs′
        uni⇒* done        done          p′ = refl
        uni⇒* done        (step r′ rs′) p′ = r′ ↯ NF→¬R p′
        uni⇒* (step r rs) done          p′ = r ↯ NF→¬R p′
        uni⇒* (step r rs) (step r′ rs′) p′ with det⇒ r r′
        ... | refl                            = step & uni⇒ r r′ ⊗ uni⇒* rs rs′ p′

        -- local confluence
        lconf⇒ : ∀ {Γ A} {t t₁ t₂ : Γ ⊢ A} → t ⇒ t₁ → t ⇒ t₂ →
                  Σ _ λ t′ → t₁ ⇒* t′ × t₂ ⇒* t′
        lconf⇒ r r′ with det⇒ r r′
        ... | refl     = _ , done , done

        -- global confluence
        gconf⇒ : ∀ {Γ A} {t t₁ t₂ : Γ ⊢ A} → t ⇒* t₁ → t ⇒* t₂ →
                  Σ _ λ t′ → t₁ ⇒* t′ × t₂ ⇒* t′
        gconf⇒ done        rs′           = _ , rs′ , done
        gconf⇒ (step r rs) done          = _ , done , step r rs
        gconf⇒ (step r rs) (step r′ rs′) with det⇒ r r′
        ... | refl                          = gconf⇒ rs rs′


----------------------------------------------------------------------------------------------------

  module ⊩Kit
    (_⊩_ : Ctx → Ty → Set)
    (vren : ∀ {W W′ A} → W ⊆ W′ → W ⊩ A → W′ ⊩ A)
      where
    -- semantic environments
    infix 3 _⊩*_
    data _⊩*_ (W : Ctx) : Ctx → Set where
      []  : W ⊩* []
      _∷_ : ∀ {Δ A} (v : W ⊩ A) (vs : W ⊩* Δ) → W ⊩* A ∷ Δ

    vrens : ∀ {W W′ Δ} → W ⊆ W′ → W ⊩* Δ → W′ ⊩* Δ
    vrens e []       = []
    vrens e (v ∷ vs) = vren e v ∷ vrens e vs

    infix 3 _⊨_
    _⊨_ : Ctx → Ty → Set
    Γ ⊨ A = ∀ {W : Ctx} → W ⊩* Γ → W ⊩ A

    ⟦_⟧∋ : ∀ {Γ A} → Γ ∋ A → Γ ⊨ A
    ⟦ zero  ⟧∋ (v ∷ vs) = v
    ⟦ suc i ⟧∋ (v ∷ vs) = ⟦ i ⟧∋ vs


----------------------------------------------------------------------------------------------------

  module ModelKit
    {Model : Set₁}
    {World : Model → Set}
    {_≤_   : ∀ (ℳ : Model) → World ℳ → World ℳ → Set}
    (_⊩_  : ∀ {ℳ} → World ℳ → Ty → Set)
    (vren : ∀ {ℳ W W′ A} → _≤_ ℳ W W′ → W ⊩ A → W′ ⊩ A)
      where
    module _ {ℳ : Model} where
      -- semantic environments
      infix 3 _⊩*_
      data _⊩*_ (W : World ℳ) : Ctx → Set where
        []  : W ⊩* []
        _∷_ : ∀ {Δ A} (v : W ⊩ A) (vs : W ⊩* Δ) → W ⊩* A ∷ Δ

      vrens : ∀ {W W′ Δ} → _≤_ ℳ W W′ → W ⊩* Δ → W′ ⊩* Δ
      vrens e []       = []
      vrens e (v ∷ vs) = vren e v ∷ vrens e vs

    infix 3 _/_⊩_
    _/_⊩_ : ∀ (ℳ : Model) (W : World ℳ) → Ty → Set
    ℳ / W ⊩ A = _⊩_ {ℳ} W A

    infix 3 _/_⊩*_
    _/_⊩*_ : ∀ (ℳ : Model) (W : World ℳ) → Ctx → Set
    ℳ / W ⊩* Δ = _⊩*_ {ℳ} W Δ

    infix 3 _⊨_
    _⊨_ : Ctx → Ty → Set₁
    Γ ⊨ A = ∀ {ℳ : Model} {W : World ℳ} → ℳ / W ⊩* Γ → ℳ / W ⊩ A

    ⟦_⟧∋ : ∀ {Γ A} → Γ ∋ A → Γ ⊨ A
    ⟦ zero  ⟧∋ (v ∷ vs) = v
    ⟦ suc i ⟧∋ (v ∷ vs) = ⟦ i ⟧∋ vs


----------------------------------------------------------------------------------------------------

  module SplitModelKit
    {BaseModel  : Set₁}
    {SplitModel : BaseModel → Set₁}
    {World      : ∀ {ℳ◦} → SplitModel ℳ◦ → Set}
    {_≤_        : ∀ {ℳ◦} (ℳ : SplitModel ℳ◦) → World ℳ → World ℳ → Set}
    (_⊩_       : ∀ {ℳ◦} (ℳ : SplitModel ℳ◦) → World ℳ → Ty → Set)
    (vren       : ∀ {ℳ◦} {ℳ : SplitModel ℳ◦} {W W′ A} → _≤_ ℳ W W′ → _⊩_ ℳ W A → _⊩_ ℳ W′ A)
      where
    module _ {ℳ◦} {ℳ : SplitModel ℳ◦} where
      -- semantic environments
      infix 3 _⊩*_
      data _⊩*_ (W : World ℳ) : Ctx → Set where
        []  : W ⊩* []
        _∷_ : ∀ {Δ A} (v : _⊩_ ℳ W A) (vs : W ⊩* Δ) → W ⊩* A ∷ Δ

      vrens : ∀ {W W′ Δ} → _≤_ ℳ W W′ → W ⊩* Δ → W′ ⊩* Δ
      vrens e []       = []
      vrens e (v ∷ vs) = vren e v ∷ vrens e vs

    infix 3 _/_⊩_
    _/_⊩_ : ∀ {ℳ◦} (ℳ : SplitModel ℳ◦) (W : World ℳ) → Ty → Set
    ℳ / W ⊩ A = _⊩_ ℳ W A

    infix 3 _/_⊩*_
    _/_⊩*_ : ∀ {ℳ◦} (ℳ : SplitModel ℳ◦) (W : World ℳ) → Ctx → Set
    ℳ / W ⊩* Δ = _⊩*_ {ℳ = ℳ} W Δ

    infix 3 _⊨_
    _⊨_ : Ctx → Ty → Set₁
    Γ ⊨ A = ∀ {ℳ◦} {ℳ : SplitModel ℳ◦} {W : World ℳ} → ℳ / W ⊩* Γ → ℳ / W ⊩ A

    ⟦_⟧∋ : ∀ {Γ A} → Γ ∋ A → Γ ⊨ A
    ⟦ zero  ⟧∋ (v ∷ vs) = v
    ⟦ suc i ⟧∋ (v ∷ vs) = ⟦ i ⟧∋ vs



----------------------------------------------------------------------------------------------------
