module Common where

open import Data.Empty public
  using (⊥)
  renaming (⊥-elim to abort)

open import Data.List public
  using (List ; [] ; _∷_)

open import Data.Nat public
  using (ℕ ; zero ; suc)

open import Data.Product public
  using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)

open import Data.Sum public
  using (_⊎_ ; inj₁ ; inj₂)

open import Data.Unit public
  using (⊤)
  renaming (tt to unit)

open import Function public
  using (_∘_ ; _$_ ; flip ; id)

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; refl ; cong ; subst ; sym ; trans ; module ≡-Reasoning)

open import Relation.Nullary public
  using (¬_ ; Dec ; yes ; no)

open import Relation.Nullary.Decidable public
  using (True ; fromWitness ; toWitness)

open import Relation.Nullary.Negation public
  using ()
  renaming (contradiction to _↯_)


----------------------------------------------------------------------------------------------------

-- _≡_ has unique proofs
uni≡ : ∀ {𝓍} {X : Set 𝓍} {x x′ : X} (eq eq′ : x ≡ x′) → eq ≡ eq′
uni≡ refl refl = refl

coe : ∀ {𝓍} {X Y : Set 𝓍} (eq : X ≡ Y) (x : X) → Y
coe = subst id

infixl 9 _&_
_&_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (f : X → Y) {x x′ : X} (eq : x ≡ x′) →
      f x ≡ f x′
_&_ = cong

infixl 8 _⊗_
_⊗_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {f g : X → Y} {x y : X} (eq₁ : f ≡ g) (eq₂ : x ≡ y) →
      f x ≡ g y
refl ⊗ refl = refl

recℕ : ∀ {𝓍} {X : Set 𝓍} (n : ℕ) (z : X) (s : ∀ (n : ℕ) (x : X) → X) → X
recℕ zero    z s = z
recℕ (suc n) z s = s n (recℕ n z s)


----------------------------------------------------------------------------------------------------

module _ {𝓍} {X : Set 𝓍} where
  -- intrinsically well-typed de Bruijn indices
  infix 4 _∋_
  data _∋_ : ∀ (Γ : List X) (A : X) → Set 𝓍 where
    zero : ∀ {Γ A} → A ∷ Γ ∋ A
    suc  : ∀ {Γ A B} (i : Γ ∋ A) → B ∷ Γ ∋ A

  -- order-preserving embeddings
  infix 4 _⊆_
  data _⊆_ : ∀ (Γ Γ′ : List X) → Set 𝓍 where
    stop : [] ⊆ []
    drop : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) → Γ ⊆ A ∷ Γ′
    keep : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) → A ∷ Γ ⊆ A ∷ Γ′

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ {[]}    = stop
  refl⊆ {A ∷ Γ} = keep refl⊆

  trans⊆ : ∀ {Γ Γ′ Γ″} (e : Γ ⊆ Γ′) (e′ : Γ′ ⊆ Γ″) → Γ ⊆ Γ″
  trans⊆ e        stop      = e
  trans⊆ e        (drop e′) = drop (trans⊆ e e′)
  trans⊆ (drop e) (keep e′) = drop (trans⊆ e e′)
  trans⊆ (keep e) (keep e′) = keep (trans⊆ e e′)

  wk⊆ : ∀ {Γ A} → Γ ⊆ A ∷ Γ
  wk⊆ = drop refl⊆

  -- renaming of indices
  ren∋ : ∀ {Γ Γ′} {A : X} (e : Γ ⊆ Γ′) (i : Γ ∋ A) → Γ′ ∋ A
  ren∋ stop     i       = i
  ren∋ (drop e) i       = suc (ren∋ e i)
  ren∋ (keep e) zero    = zero
  ren∋ (keep e) (suc i) = suc (ren∋ e i)

  infix 4 _≟∋_
  _≟∋_ : ∀ {Γ A} (i i′ : Γ ∋ A) → Dec (i ≡ i′)
  zero  ≟∋ zero   = yes refl
  zero  ≟∋ suc i′ = no λ ()
  suc i ≟∋ zero   = no λ ()
  suc i ≟∋ suc i′ with i ≟∋ i′
  ... | yes refl    = yes refl
  ... | no ¬eq      = no λ { refl → refl ↯ ¬eq }


----------------------------------------------------------------------------------------------------

module CtxKit (Ty : Set)
  where
  Ctx : Set
  Ctx = List Ty


----------------------------------------------------------------------------------------------------

  module ⊢*Kit
      (Tm : ∀ (Γ : Ctx) (A : Ty) → Set)
    where
    private
      infix 3 _⊢_
      _⊢_ = Tm

    -- simultaneous substitutions
    infix 3 _⊢*_
    data _⊢*_ (Γ : Ctx) : ∀ (Δ : Ctx) → Set where
      []  : Γ ⊢* []
      _∷_ : ∀ {A Δ} (d : Γ ⊢ A) (ds : Γ ⊢* Δ) → Γ ⊢* A ∷ Δ


----------------------------------------------------------------------------------------------------

    module RenKit
        (`v  : ∀ {Γ A} (i : Γ ∋ A) → Γ ⊢ A)
        (ren : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (d : Γ ⊢ A) → Γ′ ⊢ A)
      where
      weak : ∀ {Γ A B} (d : Γ ⊢ B) → A ∷ Γ ⊢ B
      weak d = ren wk⊆ d

      ren* : ∀ {Γ Γ′ Δ} (e : Γ ⊆ Γ′) (ds : Γ ⊢* Δ) → Γ′ ⊢* Δ
      ren* e []       = []
      ren* e (d ∷ ds) = ren e d ∷ ren* e ds

      weak* : ∀ {Γ Δ A} (ds : Γ ⊢* Δ) → A ∷ Γ ⊢* Δ
      weak* ds = ren* wk⊆ ds

      lift* : ∀ {Γ Δ A} (ds : Γ ⊢* Δ) → A ∷ Γ ⊢* A ∷ Δ
      lift* ds = `v zero ∷ weak* ds

      refl* : ∀ {Γ} → Γ ⊢* Γ
      refl* {[]}    = []
      refl* {A ∷ Γ} = lift* refl*

      -- substitution of indices
      sub∋ : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (i : Γ ∋ A) → Ξ ⊢ A
      sub∋ (s ∷ ss) zero    = s
      sub∋ (s ∷ ss) (suc i) = sub∋ ss i


----------------------------------------------------------------------------------------------------

      module SubKit
          (sub : ∀ {Γ Ξ A} (ss : Ξ ⊢* Γ) (d : Γ ⊢ A) → Ξ ⊢ A)
        where
        sub* : ∀ {Γ Ξ Δ} (ss : Ξ ⊢* Γ) (ds : Γ ⊢* Δ) → Ξ ⊢* Δ
        sub* ss []       = []
        sub* ss (d ∷ ds) = sub ss d ∷ sub* ss ds

        _[_] : ∀ {Γ A B} (d : A ∷ Γ ⊢ B) (s : Γ ⊢ A) → Γ ⊢ B
        d [ s ] = sub (s ∷ refl*) d

        _[_∣_] : ∀ {Γ A B C} (d : B ∷ A ∷ Γ ⊢ C) (s₁ : Γ ⊢ A) (s₂ : Γ ⊢ B) → Γ ⊢ C
        d [ s₁ ∣ s₂ ] = sub (s₂ ∷ s₁ ∷ refl*) d

        get* : ∀ {Γ Δ Δ′} (e : Δ ⊆ Δ′) (ds : Γ ⊢* Δ′) → Γ ⊢* Δ
        get* stop     ds       = ds
        get* (drop e) (d ∷ ds) = get* e ds
        get* (keep e) (d ∷ ds) = d ∷ get* e ds


----------------------------------------------------------------------------------------------------

    module ≝Kit
        {_≝_    : ∀ {Γ A} (d d′ : Γ ⊢ A) → Set}
        (refl≝  : ∀ {Γ A} {d : Γ ⊢ A} → d ≝ d)
        (sym≝   : ∀ {Γ A} {d d′ : Γ ⊢ A} (eq : d ≝ d′) → d′ ≝ d)
        (trans≝ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (eq : d ≝ d′) (p′ : d′ ≝ d″) → d ≝ d″)
      where
      ≡→≝ : ∀ {Γ A} {d d′ : Γ ⊢ A} (eq : d ≡ d′) → d ≝ d′
      ≡→≝ refl = refl≝

      module ≝-Reasoning where
        infix 1 begin_
        begin_ : ∀ {Γ A} {d d′ : Γ ⊢ A} (eq : d ≝ d′) → d ≝ d′
        begin_ eq = eq

        infixr 2 _≝⟨⟩_
        _≝⟨⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′} (eq : d ≝ d′) → d ≝ d′
        d ≝⟨⟩ eq = eq

        infixr 2 _≝⟨_⟩_
        _≝⟨_⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′ d″} (eq : d ≝ d′) (eq′ : d′ ≝ d″) → d ≝ d″
        d ≝⟨ eq ⟩ eq′ = trans≝ eq eq′

        infixr 2 _≝˘⟨_⟩_
        _≝˘⟨_⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′ d″} (eq : d′ ≝ d) (eq′ : d′ ≝ d″) → d ≝ d″
        d ≝˘⟨ eq ⟩ eq′ = trans≝ (sym≝ eq) eq′

        infixr 2 _≡⟨_⟩_
        _≡⟨_⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′ d″} (eq : d ≡ d′) (eq′ : d′ ≝ d″) → d ≝ d″
        d ≡⟨ eq ⟩ eq′ = trans≝ (≡→≝ eq) eq′

        infixr 2 _≡˘⟨_⟩_
        _≡˘⟨_⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′ d″} (eq : d′ ≡ d) (eq′ : d′ ≝ d″) → d ≝ d″
        d ≡˘⟨ eq ⟩ eq′ = trans≝ (≡→≝ (sym eq)) eq′

        infix 3 _∎
        _∎ : ∀ {Γ A} (d : Γ ⊢ A) → d ≝ d
        d ∎ = refl≝


----------------------------------------------------------------------------------------------------

    module ⟹Kit
        (Red : ∀ {Γ A} (d d′ : Γ ⊢ A) → Set)
      where
      private
        infix 4 _⟹_
        _⟹_ = Red

      -- d is in convertible form
      RF : ∀ {Γ A} (d : Γ ⊢ A) → Set
      RF d = Σ _ λ d′ → d ⟹ d′

      -- d is in inconvertible form
      ¬R : ∀ {Γ A} (d : Γ ⊢ A) → Set
      ¬R d = ∀ {d′} → ¬ d ⟹ d′

      ¬RF→¬R : ∀ {Γ A} {d : Γ ⊢ A} (¬rf : ¬ RF d) → ¬R d
      ¬RF→¬R ¬p r = (_ , r) ↯ ¬p

      ¬R→¬RF : ∀ {Γ A} {d : Γ ⊢ A} (¬r : ¬R d) → ¬ RF d
      ¬R→¬RF ¬r (_ , r) = r ↯ ¬r

      pattern rf p = inj₁ p
      pattern nf p = inj₂ p


----------------------------------------------------------------------------------------------------

      module RF⊎NFKit
          {NF     : ∀ {Γ A} (d : Γ ⊢ A) → Set}
          (NF→¬R : ∀ {Γ A} {d : Γ ⊢ A} (p : NF d) → ¬R d)
          (RF⊎NF  : ∀ {Γ A} (d : Γ ⊢ A) → RF d ⊎ NF d)
        where
        ¬R→NF : ∀ {Γ A} {d : Γ ⊢ A} (¬r : ¬R d) → NF d
        ¬R→NF {d = d} ¬r with RF⊎NF d
        ... | rf p          = p ↯ ¬R→¬RF ¬r
        ... | nf p          = p

        ¬NF→RF : ∀ {Γ A} {d : Γ ⊢ A} (¬p : ¬ NF d) → RF d
        ¬NF→RF {d = d} ¬p with RF⊎NF d
        ... | rf p           = p
        ... | nf p           = p ↯ ¬p

        RF→¬NF : ∀ {Γ A} {d : Γ ⊢ A} (rf : RF d) → ¬ NF d
        RF→¬NF (d′ , r) p = r ↯ NF→¬R p

        ¬RF→NF : ∀ {Γ A} {d : Γ ⊢ A} (¬rf : ¬ RF d) → NF d
        ¬RF→NF = ¬R→NF ∘ ¬RF→¬R

        NF→¬RF : ∀ {Γ A} {d : Γ ⊢ A} (wnf : NF d) → ¬ RF d
        NF→¬RF = ¬R→¬RF ∘ NF→¬R


----------------------------------------------------------------------------------------------------

        module ⟹*Kit
            (det⟹ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (r : d ⟹ d′) (r′ : d ⟹ d″) → d′ ≡ d″)
          where
          -- iterated reduction
          infix 4 _⟹*_
          data _⟹*_ {Γ} : ∀ {A} (d : Γ ⊢ A) (d′ : Γ ⊢ A) → Set where
            done : ∀ {A} {d : Γ ⊢ A} → d ⟹* d
            step : ∀ {A} {d d′ d″ : Γ ⊢ A} (r : d ⟹ d′) (rs : d′ ⟹* d″) → d ⟹* d″

          trans⟹* : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (rs : d ⟹* d′) (rs′ : d′ ⟹* d″) → d ⟹* d″
          trans⟹* done        rs′ = rs′
          trans⟹* (step r rs) rs′ = step r (trans⟹* rs rs′)

          -- _⟹_ has the diamond property
          dia⟹ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (r : d ⟹ d′) (r′ : d ⟹ d″) →
                   Σ (Γ ⊢ A) λ d‴ → d′ ⟹* d‴ × d″ ⟹* d‴
          dia⟹ r r′ with det⟹ r r′
          ... | refl    = _ , done , done

          -- _⟹_ is confluent
          conf⟹ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (rs : d ⟹* d′) (rs′ : d ⟹* d″) →
                    Σ (Γ ⊢ A) λ d‴ → d′ ⟹* d‴ × d″ ⟹* d‴
          conf⟹ done        rs′           = _ , rs′ , done
          conf⟹ (step r rs) done          = _ , done , step r rs
          conf⟹ (step r rs) (step r′ rs′) with det⟹ r r′
          ... | refl                          = conf⟹ rs rs′

          skip⟹ : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (p″ : NF d″) (r : d ⟹ d′) (rs′ : d ⟹* d″) →
                    d′ ⟹* d″
          skip⟹ p″ r done          = r ↯ NF→¬R p″
          skip⟹ p″ r (step r′ rs′) with det⟹ r r′
          ... | refl                   = rs′

          -- _⟹*_ is deterministic
          det⟹* : ∀ {Γ A} {d d′ d″ : Γ ⊢ A} (p′ : NF d′) (p″ : NF d″) (rs : d ⟹* d′)
                      (rs′ : d ⟹* d″) →
                    d′ ≡ d″
          det⟹* p′ p″ done        done          = refl
          det⟹* p′ p″ done        (step r′ rs′) = r′ ↯ NF→¬R p′
          det⟹* p′ p″ (step r rs) rs′           = det⟹* p′ p″ rs (skip⟹ p″ r rs′)

          ≡→⟹* : ∀ {Γ A} {d d′ : Γ ⊢ A} (eq : d ≡ d′) → d ⟹* d′
          ≡→⟹* refl = done

          module ⟹-Reasoning where
            infix 1 begin_
            begin_ : ∀ {Γ A} {d d′ : Γ ⊢ A} (rs : d ⟹* d′) → d ⟹* d′
            begin_ rs = rs

            infixr 2 _⟹⟨_⟩_
            _⟹⟨_⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′ d″} (r : d ⟹ d′) (rs : d′ ⟹* d″) → d ⟹* d″
            d ⟹⟨ r ⟩ rs = step r rs

            infixr 2 _⟹*⟨⟩_
            _⟹*⟨⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′} (rs : d ⟹* d′) → d ⟹* d′
            d ⟹*⟨⟩ rs = rs

            infixr 2 _⟹*⟨_⟩_
            _⟹*⟨_⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′ d″} (rs : d ⟹* d′) (rs′ : d′ ⟹* d″) →
                          d ⟹* d″
            d ⟹*⟨ rs ⟩ rs′ = trans⟹* rs rs′

            infixr 2 _≡⟨_⟩_
            _≡⟨_⟩_ : ∀ {Γ A} (d : Γ ⊢ A) {d′ d″} (eq : d ≡ d′) (rs′ : d′ ⟹* d″) → d ⟹* d″
            d ≡⟨ eq ⟩ rs′ = trans⟹* (≡→⟹* eq) rs′

            infix 3 _∎
            _∎ : ∀ {Γ A} (d : Γ ⊢ A) → d ⟹* d
            d ∎ = done


----------------------------------------------------------------------------------------------------
