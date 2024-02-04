module Common where

open import Prelude public
open import Category public
open import Isomorphism public
open ≡-Reasoning


----------------------------------------------------------------------------------------------------

module _ {𝓍} {X : Set 𝓍} where
  infix 4 _∋_
  data _∋_ : List X → X → Set where
    zero : ∀ {Γ A} → A ∷ Γ ∋ A
    suc  : ∀ {Γ A B} (i : Γ ∋ A) → B ∷ Γ ∋ A

  injsuc : ∀ {Γ A B} {i i′ : Γ ∋ A} → suc i ≡ suc i′ :> (B ∷ Γ ∋ A) → i ≡ i′
  injsuc refl = refl

  infix 4 _≟∋_
  _≟∋_ : ∀ {Γ A} (i i′ : Γ ∋ A) → Dec (i ≡ i′)
  zero  ≟∋ zero   = yes refl
  zero  ≟∋ suc i′ = no λ ()
  suc i ≟∋ zero   = no λ ()
  suc i ≟∋ suc i′ with i ≟∋ i′
  ... | yes refl    = yes refl
  ... | no ¬eq      = no λ { refl → refl ↯ ¬eq }


----------------------------------------------------------------------------------------------------

module OrderPreservingEmbeddings {𝓍} {X : Set 𝓍} where
  infix 4 _⊆_
  data _⊆_ : List X → List X → Set 𝓍 where
    stop⊆ : [] ⊆ []
    wk⊆   : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) → Γ ⊆ A ∷ Γ′
    lift⊆ : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) → A ∷ Γ ⊆ A ∷ Γ′

  id⊆ : ∀ {Γ} → Γ ⊆ Γ
  id⊆ {[]}    = stop⊆
  id⊆ {A ∷ Γ} = lift⊆ id⊆

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ = id⊆

  _∘⊆_ : ∀ {Γ Γ′ Γ″} → Γ′ ⊆ Γ″ → Γ ⊆ Γ′ → Γ ⊆ Γ″
  stop⊆    ∘⊆ e       = e
  wk⊆ e′   ∘⊆ e       = wk⊆ (e′ ∘⊆ e)
  lift⊆ e′ ∘⊆ wk⊆ e   = wk⊆ (e′ ∘⊆ e)
  lift⊆ e′ ∘⊆ lift⊆ e = lift⊆ (e′ ∘⊆ e)

  _○_ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  _○_ = flip _∘⊆_

  trans⊆ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  trans⊆ = flip _∘⊆_

  ren∋ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ∋ A → Γ′ ∋ A
  ren∋ stop⊆     i       = i
  ren∋ (wk⊆ e)   i       = suc (ren∋ e i)
  ren∋ (lift⊆ e) zero    = zero
  ren∋ (lift⊆ e) (suc i) = suc (ren∋ e i)

  wk∋ : ∀ {Γ A B} → Γ ∋ B → A ∷ Γ ∋ B
  wk∋ i = ren∋ (wk⊆ id⊆) i

  lid⊆ : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) → id⊆ ∘⊆ e ≡ e
  lid⊆ stop⊆     = refl
  lid⊆ (wk⊆ e)   = wk⊆ & lid⊆ e
  lid⊆ (lift⊆ e) = lift⊆ & lid⊆ e

  rid⊆ : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) → e ∘⊆ id⊆ ≡ e
  rid⊆ stop⊆     = refl
  rid⊆ (wk⊆ e)   = wk⊆ & rid⊆ e
  rid⊆ (lift⊆ e) = lift⊆ & rid⊆ e

  ass⊆ : ∀ {Γ Γ′ Γ″ Γ‴} (e″ : Γ″ ⊆ Γ‴) (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) →
         e″ ∘⊆ (e′ ∘⊆ e) ≡ (e″ ∘⊆ e′) ∘⊆ e
  ass⊆ stop⊆      e′         e         = refl
  ass⊆ (wk⊆ e″)   e′         e         = wk⊆ & ass⊆ e″ e′ e
  ass⊆ (lift⊆ e″) (wk⊆ e′)   e         = wk⊆ & ass⊆ e″ e′ e
  ass⊆ (lift⊆ e″) (lift⊆ e′) (wk⊆ e)   = wk⊆ & ass⊆ e″ e′ e
  ass⊆ (lift⊆ e″) (lift⊆ e′) (lift⊆ e) = lift⊆ & ass⊆ e″ e′ e

  ⟪⊇⟫ : Category 𝓍 𝓍
  ⟪⊇⟫ = record
          { Obj  = List X
          ; _▻_  = flip _⊆_
          ; id   = id⊆
          ; _∘_  = _○_
          ; lid∘ = rid⊆
          ; rid∘ = lid⊆
          ; ass∘ = λ is is′ is″ → sym (ass⊆ is″ is′ is)
          }

  idren∋ : ∀ {Γ A} (i : Γ ∋ A) → ren∋ id⊆ i ≡ i
  idren∋ zero    = refl
  idren∋ (suc i) = suc & idren∋ i

  compren∋ : ∀ {Γ Γ′ Γ″ A} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (i : Γ ∋ A) →
             ren∋ (e′ ∘⊆ e) i ≡ (ren∋ e′ ∘ ren∋ e) i
  compren∋ stop⊆      e         i       = refl
  compren∋ (wk⊆ e′)   e         i       = suc & compren∋ e′ e i
  compren∋ (lift⊆ e′) (wk⊆ e)   i       = suc & compren∋ e′ e i
  compren∋ (lift⊆ e′) (lift⊆ e) zero    = refl
  compren∋ (lift⊆ e′) (lift⊆ e) (suc i) = suc & compren∋ e′ e i

  module _ (⚠ : FunExt) where
    ⟪ren∋⟫ : ∀ (A : X) → Presheaf ⟪⊇⟫ lzero
    ⟪ren∋⟫ A = record
                 { ƒObj = _∋ A
                 ; ƒ    = ren∋
                 ; idƒ  = ⚠ idren∋
                 ; _∘ƒ_ = λ e′ e → ⚠ (compren∋ e′ e)
                 }

  injren∋ : ∀ {Γ Γ′ A} {e : Γ ⊆ Γ′} {i i′ : Γ ∋ A} → ren∋ e i ≡ ren∋ e i′ → i ≡ i′
  injren∋ {e = stop⊆}   {i}     {i′}     eq   = eq
  injren∋ {e = wk⊆ e}   {i}     {i′}     eq   = injren∋ (injsuc eq)
  injren∋ {e = lift⊆ e} {zero}  {zero}   refl = refl
  injren∋ {e = lift⊆ e} {suc i} {suc i′} eq   = suc & (injren∋ (injsuc eq))

  -- TODO: delete?
  unren∋ : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (i′ : Γ′ ∋ A) → Dec (Σ (Γ ∋ A) λ i → i′ ≡ ren∋ e i)
  unren∋ stop⊆     i′       = yes (i′ , refl)
  unren∋ (wk⊆ e)   zero     = no λ ()
  unren∋ (wk⊆ e)   (suc i′) with unren∋ e i′
  ... | no ¬p                 = no λ { (i , refl) → (i , refl) ↯ ¬p }
  ... | yes (i , refl)        = yes (i , refl)
  unren∋ (lift⊆ e) zero     = yes (zero , refl)
  unren∋ (lift⊆ e) (suc i′) with unren∋ e i′
  ... | no ¬p                 = no λ { (suc i , refl) → (i , refl) ↯ ¬p }
  ... | yes (i , refl)        = yes (suc i , refl)


----------------------------------------------------------------------------------------------------

module Renamings {𝓍} {X : Set 𝓍} where
  infix 4 _⊆_
  data _⊆_ : List X → List X → Set 𝓍 where
    []  : ∀ {Γ} → [] ⊆ Γ
    _∷_ : ∀ {Γ Γ′ A} (i : Γ′ ∋ A) (is : Γ ⊆ Γ′) → A ∷ Γ ⊆ Γ′

  stop⊆ : [] ⊆ []
  stop⊆ = []

  wk⊆ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊆ A ∷ Γ′
  wk⊆ []       = []
  wk⊆ (i ∷ is) = suc i ∷ wk⊆ is

  lift⊆ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → A ∷ Γ ⊆ A ∷ Γ′
  lift⊆ is = zero ∷ wk⊆ is

  id⊆ : ∀ {Γ} → Γ ⊆ Γ
  id⊆ {[]}    = []
  id⊆ {A ∷ Γ} = lift⊆ id⊆

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ = id⊆

  ren∋ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ∋ A → Γ′ ∋ A
  ren∋ (j ∷ js) zero    = j
  ren∋ (j ∷ js) (suc i) = ren∋ js i

  wk∋ : ∀ {Γ A B} → Γ ∋ B → A ∷ Γ ∋ B
  wk∋ i = ren∋ (wk⊆ id⊆) i

  eqsucren∋ : ∀ {Γ Γ′ A B} (js : Γ ⊆ Γ′) (i : Γ ∋ A) →
              ren∋ (wk⊆ {A = B} js) i ≡ (suc ∘ ren∋ js) i
  eqsucren∋ (j ∷ js) zero    = refl
  eqsucren∋ (j ∷ js) (suc i) = eqsucren∋ js i

  idren∋ : ∀ {Γ A} (i : Γ ∋ A) → ren∋ id⊆ i ≡ i
  idren∋ zero    = refl
  idren∋ (suc i) = eqsucren∋ id⊆ i ⋮ suc & idren∋ i

  _∘⊆_ : ∀ {Γ Γ′ Γ″} → Γ′ ⊆ Γ″ → Γ ⊆ Γ′ → Γ ⊆ Γ″
  is′ ∘⊆ []       = []
  is′ ∘⊆ (i ∷ is) = ren∋ is′ i ∷ (is′ ∘⊆ is)

  _○_ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  _○_ = flip _∘⊆_

  trans⊆ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  trans⊆ = flip _∘⊆_

  -- like compsub∋
  -- compsub∋ : ∀ {Γ Ξ Ξ′ A} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (i : Γ ∋ A) →
  -- --         sub∋ (sub* ss′ ss) i ≡ (sub ss′ ∘ sub∋ ss) i
  --            sub∋ (ss ● ss′) i ≡ (sub∋ ss ⨾ sub ss′) i
  compren∋ : ∀ {Γ Γ′ Γ″ A} (js′ : Γ′ ⊆ Γ″) (js : Γ ⊆ Γ′) (i : Γ ∋ A) →
  --         ren∋ (js′ ∘⊆ js) i ≡ (ren∋ js′ ∘ ren∋ js) i
             ren∋ (js ○ js′) i ≡ (ren∋ js ⨾ ren∋ js′) i
  compren∋ (j′ ∷ js′) (j ∷ js) zero    = refl
  compren∋ (j′ ∷ js′) (j ∷ js) (suc i) = compren∋ (j′ ∷ js′) js i

  -- -- like lidsub*
  -- lidsub* : ∀ {Γ Δ} (ts : Γ ⊢* Δ) →
  -- --        sub* id* ts ≡ ts
  --           ts ● id* ≡ ts
  lid⊆ : ∀ {Γ Γ′} (is : Γ ⊆ Γ′) →
  --     id⊆ ∘⊆ is ≡ is
         is ○ id⊆ ≡ is
  lid⊆ []       = refl
  lid⊆ (i ∷ is) = _∷_ & idren∋ i ⊗ lid⊆ is

  -- -- like eqwksub*
  -- eqwksub* : ∀ {Γ Ξ Δ B} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
  -- --         (sub* (lift* {A = B} ss) ∘ wk*) ts ≡ (wk* ∘ sub* ss) ts
  --            (wk* ts) ● (lift* {A = B} ss) ≡ wk* (ts ● ss)
  eqwk⊆ : ∀ {Γ Γ′ Γ″ B} (js : Γ′ ⊆ Γ″) (is : Γ ⊆ Γ′) →
  --      lift⊆ {A = B} js ∘⊆ wk⊆ is ≡ wk⊆ (js ∘⊆ is)
          (wk⊆ is) ○ (lift⊆ {A = B} js) ≡ wk⊆ (is ○ js)
  eqwk⊆ js []       = refl
  eqwk⊆ js (i ∷ is) = _∷_ & eqsucren∋ js i ⊗ eqwk⊆ js is

  -- -- like eqliftsub*
  -- eqliftsub* : ∀ {Γ Ξ Δ B} (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
  -- --           (sub* (lift* {A = B} ss) ∘ lift*) ts ≡ (lift* ∘ sub* ss) ts
  --              (lift* ts) ● (lift* {A = B} ss) ≡ lift* (ts ● ss)
  eqlift⊆ : ∀ {Γ Γ′ Γ″ B} (js : Γ′ ⊆ Γ″) (is : Γ ⊆ Γ′) →
  --        lift⊆ {A = B} js ∘⊆ (lift⊆ is) ≡ lift⊆ (js ∘⊆ is)
            (lift⊆ is) ○ (lift⊆ {A = B} js) ≡ lift⊆ (is ○ js)
  eqlift⊆ js []       = refl
  eqlift⊆ js (i ∷ is) = (zero ∷_) & eqwk⊆ js (i ∷ is)

  -- like eqsub*
  -- eqsub* : ∀ {Γ Ξ Δ B} (s : Ξ ⊢ B) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
  -- --       (sub* (s ∷ ss) ∘ wk*) ts ≡ sub* ss ts
  --          (wk* ts) ● (s ∷ ss) ≡ ts ● ss
  eq⊆ : ∀ {Γ Γ′ Γ″ A} (j : Γ″ ∋ A) (js : Γ′ ⊆ Γ″) (is : Γ ⊆ Γ′) →
  --    (j ∷ js) ∘⊆ wk⊆ is ≡ js ∘⊆ is
        (wk⊆ is) ○ (j ∷ js) ≡ is ○ js
  eq⊆ j js []       = refl
  eq⊆ j js (i ∷ is) = (ren∋ js i ∷_) & eq⊆ j js is

  -- like sidsub*
  -- ridsub* : ∀ {Γ Ξ} (ss : Ξ ⊢* Γ) →
  -- --        sub* ss id* ≡ ss
  --           id* ● ss ≡ ss
  rid⊆ : ∀ {Γ Γ′} (is : Γ ⊆ Γ′) →
  --     is ∘⊆ id⊆ ≡ is
         id⊆ ○ is ≡ is
  rid⊆ []       = refl
  rid⊆ (i ∷ is) = (i ∷_) & (eq⊆ i is id⊆ ⋮ rid⊆ is)

  -- like asssub*
  -- asssub* : ∀ {Γ Ξ Ξ′ Δ} (ss′ : Ξ′ ⊢* Ξ) (ss : Ξ ⊢* Γ) (ts : Γ ⊢* Δ) →
  -- --        sub* (sub* ss′ ss) ts ≡ (sub* ss′ ∘ sub* ss) ts
  --           ts ● (ss ● ss′) ≡ (ts ● ss) ● ss′
  ass⊆ : ∀ {Γ Γ′ Γ″ Γ‴} (is″ : Γ″ ⊆ Γ‴) (is′ : Γ′ ⊆ Γ″) (is : Γ ⊆ Γ′) →
  --       is″ ∘⊆ (is′ ∘⊆ is) ≡ (is″ ∘⊆ is′) ∘⊆ is
         (is ○ is′) ○ is″ ≡ is ○ (is′ ○ is″)
  ass⊆ is″ is′        []       = refl
  ass⊆ is″ (i′ ∷ is′) (i ∷ is) = _∷_ & compren∋ is″ (i′ ∷ is′) i ⁻¹ ⊗ ass⊆ is″ (i′ ∷ is′) is

  ⟪⊇⟫ : Category 𝓍 𝓍
  ⟪⊇⟫ = record
          { Obj  = List X
          ; _▻_  = flip _⊆_
          ; id   = id⊆
          ; _∘_  = _○_
          ; lid∘ = rid⊆
          ; rid∘ = lid⊆
          ; ass∘ = λ is is′ is″ → sym (ass⊆ is″ is′ is)
          }

  module _ (⚠ : FunExt) where
    ⟪ren∋⟫ : ∀ (A : X) → Presheaf ⟪⊇⟫ lzero
    ⟪ren∋⟫ A = record
                 { ƒObj = _∋ A
                 ; ƒ    = ren∋
                 ; idƒ  = ⚠ idren∋
                 ; _∘ƒ_ = λ is′ is → ⚠ (compren∋ is′ is)
                 }


----------------------------------------------------------------------------------------------------

-- list-based renamings are isomorphic to function-based renamings
private
  module _ {𝓍} {X : Set 𝓍} where
    open Renamings

    infix 4 _⊑_
    _⊑_ : List X → List X → Set 𝓍
    Γ ⊑ Γ′ = ∀ {A} → Γ ∋ A → Γ′ ∋ A

    to : ∀ {Γ Γ′} → Γ ⊆ Γ′ → Γ ⊑ Γ′
    to (j ∷ js) zero    = j
    to (j ∷ js) (suc i) = to js i

    from : ∀ {Γ Γ′} → Γ ⊑ Γ′ → Γ ⊆ Γ′
    from {[]}    ρ = []
    from {A ∷ Γ} ρ = ρ zero ∷ from (ρ ∘ suc)

    lemfrom : ∀ {Γ Γ′} (ρ ρ′ : Γ ⊑ Γ′) → (∀ {A : X} (i : Γ ∋ A) → ρ i ≡ ρ′ i) → from ρ ≡ from ρ′
    lemfrom {[]}    ρ ρ′ eqf = refl
    lemfrom {A ∷ Γ} ρ ρ′ eqf = _∷_ & eqf zero ⊗ lemfrom (ρ ∘ suc) (ρ′ ∘ suc) (eqf ∘ suc)

    from∘to : ∀ {Γ Γ′} (is : Γ ⊆ Γ′) → (from ∘ to) is ≡ is
    from∘to []       = refl
    from∘to (i ∷ is) = (i ∷_) & from∘to is

    to⊙from : ∀ {Γ Γ′} (ρ : Γ ⊑ Γ′) → (∀ {A : X} (i : Γ ∋ A) → (to ∘ from) ρ i ≡ ρ i)
    to⊙from {A ∷ Γ} ρ zero    = refl
    to⊙from {A ∷ Γ} ρ (suc i) = to⊙from (ρ ∘ suc) i

    module _ (⚠ : FunExt) where
      ⚠′ = implify ⚠

      to∘from : ∀ {Γ Γ′} (ρ : Γ ⊑ Γ′) → (to ∘ from) ρ ≡ ρ :> (Γ ⊑ Γ′)
      to∘from ρ = ⚠′ (⚠ (to⊙from ρ))

      ⊆≃⊑ : ∀ {Γ Γ′} → (Γ ⊆ Γ′) ≃ (Γ ⊑ Γ′)
      ⊆≃⊑ = record
              { to      = to
              ; from    = from
              ; from∘to = from∘to
              ; to∘from = to∘from
              }


----------------------------------------------------------------------------------------------------
