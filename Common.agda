module Common where

open import Prelude public
open import Category public
open import Isomorphism public


----------------------------------------------------------------------------------------------------

module _ {𝓍} {X : Set 𝓍} where
  infix 4 _∋_
  data _∋_ : List X → X → Set where
    zero : ∀ {Γ A} → A ∷ Γ ∋ A
    suc  : ∀ {B Γ A} (i : Γ ∋ A) → B ∷ Γ ∋ A

  injsuc : ∀ {Γ A B} {i i′ : Γ ∋ A} → suc i ≡ _∋_.suc {B} i′ → i ≡ i′
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
    wk⊆   : ∀ {B Γ Γ′} (e : Γ ⊆ Γ′) → Γ ⊆ B ∷ Γ′
    lift⊆ : ∀ {B Γ Γ′} (e : Γ ⊆ Γ′) → B ∷ Γ ⊆ B ∷ Γ′

  wk⊆² : ∀ {B C Γ Γ′} → Γ ⊆ Γ′ → Γ ⊆ C ∷ B ∷ Γ′
  wk⊆² = wk⊆ ∘ wk⊆

  lift⊆² : ∀ {B C Γ Γ′} → Γ ⊆ Γ′ → C ∷ B ∷ Γ ⊆ C ∷ B ∷ Γ′
  lift⊆² = lift⊆ ∘ lift⊆

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

  trans⊆ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  trans⊆ = flip _∘⊆_

  _○_ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  _○_ = flip _∘⊆_

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

  ⟪⊆⟫ : Category 𝓍 𝓍
  ⟪⊆⟫ = record
          { Obj  = List X
          ; _▻_  = _⊆_
          ; id   = id⊆
          ; _∘_  = _∘⊆_ -- flip _○_
          ; lid▻ = lid⊆
          ; rid▻ = rid⊆
          ; ass▻ = ass⊆
          ; ◅ssa = λ e e′ e″ → ass⊆ e″ e′ e ⁻¹
          }

  ⟪⊇⟫ : Category 𝓍 𝓍
  ⟪⊇⟫ = ⟪⊆⟫ ᵒᵖ

  ren∋ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ∋ A → Γ′ ∋ A
  ren∋ stop⊆     i       = i
  ren∋ (wk⊆ e)   i       = suc (ren∋ e i)
  ren∋ (lift⊆ e) zero    = zero
  ren∋ (lift⊆ e) (suc i) = suc (ren∋ e i)

  wk∋ : ∀ {B Γ A} → Γ ∋ A → B ∷ Γ ∋ A
  wk∋ i = ren∋ (wk⊆ id⊆) i

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

  ⟪lift⊆⟫ : ∀ (B : X) → Functor ⟪⊆⟫ ⟪⊆⟫
  ⟪lift⊆⟫ B = record
                { ƒObj = B ∷_
                ; ƒ    = lift⊆
                ; idƒ  = refl
                ; _∘ƒ_ = λ e′ e → refl
                }

  ⟪wk⊆⟫ : ∀ (B : X) → NatTrans (⟪Id⟫ ⟪⊆⟫) (⟪lift⊆⟫ B)
  ⟪wk⊆⟫ B = record
              { η    = λ Γ → wk⊆ id⊆
              ; natη = λ Γ Δ e → wk⊆ & (lid⊆ e ⋮ rid⊆ e ⁻¹)
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

module FirstOrderRenamings {𝓍} {X : Set 𝓍} where
  infix 4 _⊆_
  data _⊆_ : List X → List X → Set 𝓍 where
    []  : ∀ {Γ} → [] ⊆ Γ
    _∷_ : ∀ {Γ Γ′ A} (i : Γ′ ∋ A) (is : Γ ⊆ Γ′) → A ∷ Γ ⊆ Γ′

  stop⊆ : [] ⊆ []
  stop⊆ = []

  wk⊆ : ∀ {B Γ Γ′} → Γ ⊆ Γ′ → Γ ⊆ B ∷ Γ′
  wk⊆ []       = []
  wk⊆ (i ∷ is) = suc i ∷ wk⊆ is

  wk⊆² : ∀ {B C Γ Γ′} → Γ ⊆ Γ′ → Γ ⊆ C ∷ B ∷ Γ′
  wk⊆² = wk⊆ ∘ wk⊆

  lift⊆ : ∀ {B Γ Γ′} → Γ ⊆ Γ′ → B ∷ Γ ⊆ B ∷ Γ′
  lift⊆ is = zero ∷ wk⊆ is

  lift⊆² : ∀ {B C Γ Γ′} → Γ ⊆ Γ′ → C ∷ B ∷ Γ ⊆ C ∷ B ∷ Γ′
  lift⊆² = lift⊆ ∘ lift⊆

  id⊆ : ∀ {Γ} → Γ ⊆ Γ
  id⊆ {[]}    = []
  id⊆ {A ∷ Γ} = lift⊆ id⊆

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ = id⊆

  ren∋ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ∋ A → Γ′ ∋ A
  ren∋ (j ∷ js) zero    = j
  ren∋ (j ∷ js) (suc i) = ren∋ js i

  wk∋ : ∀ {B Γ A} → Γ ∋ B → A ∷ Γ ∋ B
  wk∋ i = ren∋ (wk⊆ id⊆) i

  eqwkren∋ : ∀ {B Γ Γ′ A} (js : Γ ⊆ Γ′) (i : Γ ∋ A) →
             ren∋ (wk⊆ js) i ≡ (_∋_.suc {B = B} ∘ ren∋ js) i
  eqwkren∋ (j ∷ js) zero    = refl
  eqwkren∋ (j ∷ js) (suc i) = eqwkren∋ js i

  idren∋ : ∀ {Γ A} (i : Γ ∋ A) → ren∋ id⊆ i ≡ i
  idren∋ zero    = refl
  idren∋ (suc i) = eqwkren∋ id⊆ i ⋮ suc & idren∋ i

  _∘⊆_ : ∀ {Γ Γ′ Γ″} → Γ′ ⊆ Γ″ → Γ ⊆ Γ′ → Γ ⊆ Γ″
  is′ ∘⊆ []       = []
  is′ ∘⊆ (i ∷ is) = ren∋ is′ i ∷ (is′ ∘⊆ is)

  trans⊆ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  trans⊆ = flip _∘⊆_

  _○_ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  _○_ = flip _∘⊆_

  compren∋ : ∀ {Γ Γ′ Γ″ A} (js′ : Γ′ ⊆ Γ″) (js : Γ ⊆ Γ′) (i : Γ ∋ A) →
             ren∋ (js′ ∘⊆ js) i ≡ (ren∋ js′ ∘ ren∋ js) i
  compren∋ (j′ ∷ js′) (j ∷ js) zero    = refl
  compren∋ (j′ ∷ js′) (j ∷ js) (suc i) = compren∋ (j′ ∷ js′) js i

  lid⊆ : ∀ {Γ Γ′} (is : Γ ⊆ Γ′) → id⊆ ∘⊆ is ≡ is
  lid⊆ []       = refl
  lid⊆ (i ∷ is) = _∷_ & idren∋ i ⊗ lid⊆ is

  eq⊆ : ∀ {B Γ Γ′ Γ″} (i′ : Γ″ ∋ B) (is′ : Γ′ ⊆ Γ″) (is : Γ ⊆ Γ′) →
        (i′ ∷ is′) ∘⊆ (wk⊆ is) ≡ is′ ∘⊆ is
  eq⊆ i′ is′ []       = refl
  eq⊆ i′ is′ (i ∷ is) = (ren∋ is′ i ∷_) & eq⊆ i′ is′ is

  eqwk⊆ : ∀ {B Γ Γ′ Γ″} (is′ : Γ′ ⊆ Γ″) (is : Γ ⊆ Γ′) →
          (lift⊆ is′) ∘⊆ (wk⊆ is) ≡ wk⊆ {B} (is′ ∘⊆ is)
  eqwk⊆ is′ []       = refl
  eqwk⊆ is′ (i ∷ is) = _∷_ & eqwkren∋ is′ i ⊗ eqwk⊆ is′ is

  -- TODO: name? friends? delete?
  eqwk⊆′ : ∀ {B Γ Γ′} (is : Γ ⊆ Γ′) →
           wk⊆ id⊆ ∘⊆ is ≡ wk⊆ {B} is
  eqwk⊆′ is = eq⊆ zero (wk⊆ id⊆) is ⁻¹
            ⋮ eqwk⊆ id⊆ is
            ⋮ wk⊆ & (lid⊆ is)

  eqlift⊆ : ∀ {B Γ Γ′ Γ″} (is′ : Γ′ ⊆ Γ″) (is : Γ ⊆ Γ′) →
            (lift⊆ is′) ∘⊆ (lift⊆ is) ≡ lift⊆ {B} (is′ ∘⊆ is)
  eqlift⊆ is′ []       = refl
  eqlift⊆ is′ (i ∷ is) = (zero ∷_) & eqwk⊆ is′ (i ∷ is)

  rid⊆ : ∀ {Γ Γ′} (is : Γ ⊆ Γ′) → is ∘⊆ id⊆ ≡ is
  rid⊆ []       = refl
  rid⊆ (i ∷ is) = (i ∷_) & (eq⊆ i is id⊆ ⋮ rid⊆ is)

  ass⊆ : ∀ {Γ Γ′ Γ″ Γ‴} (is″ : Γ″ ⊆ Γ‴) (is′ : Γ′ ⊆ Γ″) (is : Γ ⊆ Γ′) →
         is″ ∘⊆ (is′ ∘⊆ is) ≡ (is″ ∘⊆ is′) ∘⊆ is
  ass⊆ is″ is′ []       = refl
  ass⊆ is″ is′ (i ∷ is) = _∷_ & compren∋ is″ is′ i ⁻¹ ⊗ ass⊆ is″ is′ is

  ⟪⊆⟫ : Category 𝓍 𝓍
  ⟪⊆⟫ = record
          { Obj  = List X
          ; _▻_  = _⊆_
          ; id   = id⊆
          ; _∘_  = _∘⊆_ -- flip _○_
          ; lid▻ = lid⊆
          ; rid▻ = rid⊆
          ; ass▻ = ass⊆
          ; ◅ssa = λ is″ is′ is → ass⊆ is is′ is″ ⁻¹
          }

  ⟪⊇⟫ : Category 𝓍 𝓍
  ⟪⊇⟫ = ⟪⊆⟫ ᵒᵖ

  module _ (⚠ : FunExt) where
    ⟪ren∋⟫ : ∀ (A : X) → Presheaf ⟪⊇⟫ lzero
    ⟪ren∋⟫ A = record
                 { ƒObj = _∋ A
                 ; ƒ    = ren∋
                 ; idƒ  = ⚠ idren∋
                 ; _∘ƒ_ = λ is′ is → ⚠ (compren∋ is′ is)
                 }


----------------------------------------------------------------------------------------------------

-- first-order renamings are isomorphic to higher-order renamings
private
  module _ {𝓍} {X : Set 𝓍} where
    open FirstOrderRenamings

    infix 4 _≤_
    _≤_ : List X → List X → Set 𝓍
    Γ ≤ Γ′ = ∀ {A} → Γ ∋ A → Γ′ ∋ A

    to : ∀ {Γ Γ′} → Γ ⊆ Γ′ → Γ ≤ Γ′
    to (j ∷ js) zero    = j
    to (j ∷ js) (suc i) = to js i

    from : ∀ {Γ Γ′} → Γ ≤ Γ′ → Γ ⊆ Γ′
    from {[]}    ρ = []
    from {A ∷ Γ} ρ = ρ zero ∷ from (ρ ∘ suc)

    from∘to : ∀ {Γ Γ′} (is : Γ ⊆ Γ′) → (from ∘ to) is ≡ is
    from∘to []       = refl
    from∘to (i ∷ is) = (i ∷_) & from∘to is

    to∘from∙ : ∀ {Γ Γ′} (ρ : Γ ≤ Γ′) → (∀ {A : X} (i : Γ ∋ A) → (to ∘ from) ρ i ≡ ρ i)
    to∘from∙ {A ∷ Γ} ρ zero    = refl
    to∘from∙ {A ∷ Γ} ρ (suc i) = to∘from∙ (ρ ∘ suc) i

    module _ (⚠ : FunExt) where
      ⚠′ = implify ⚠

      to∘from : ∀ {Γ Γ′} (ρ : Γ ≤ Γ′) → (to ∘ from) ρ ≡ ρ :> (Γ ≤ Γ′)
      to∘from ρ = ⚠′ (⚠ (to∘from∙ ρ))

      ⊆≃≤ : ∀ {Γ Γ′} → (Γ ⊆ Γ′) ≃ (Γ ≤ Γ′)
      ⊆≃≤ = record
              { to      = to
              ; from    = from
              ; from∘to = from∘to
              ; to∘from = to∘from
              }

    extfrom : ∀ {Γ Γ′} (ρ ρ′ : Γ ≤ Γ′) → (∀ {A : X} (i : Γ ∋ A) → ρ i ≡ ρ′ i) → from ρ ≡ from ρ′
    extfrom {[]}    ρ ρ′ peq = refl
    extfrom {A ∷ Γ} ρ ρ′ peq = _∷_ & peq zero ⊗ extfrom (ρ ∘ suc) (ρ′ ∘ suc) (peq ∘ suc)


----------------------------------------------------------------------------------------------------
