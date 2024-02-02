module Kit1 where

open import Common public
open import Category public


----------------------------------------------------------------------------------------------------

module TyKit (Ty : Set) where
  data Ctx : Set where
    []  : Ctx
    _∷_ : Ty → Ctx → Ctx

  infix 4 _∋_
  data _∋_ : Ctx → Ty → Set where
    zero : ∀ {Γ A} → A ∷ Γ ∋ A
    suc  : ∀ {Γ A B} (i : Γ ∋ A) → B ∷ Γ ∋ A

  injsuc : ∀ {Γ A B} {i i′ : Γ ∋ A} → _∋_.suc {B = B} i ≡ suc i′ → i ≡ i′
  injsuc refl = refl

  infix 4 _⊆_
  data _⊆_ : Ctx → Ctx → Set where
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

  lid⊆ : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) → id⊆ ∘⊆ e ≡ e
  lid⊆ stop     = refl
  lid⊆ (drop e) = drop & lid⊆ e
  lid⊆ (keep e) = keep & lid⊆ e

  rid⊆ : ∀ {Γ Γ′} (e : Γ ⊆ Γ′) → e ∘⊆ id⊆ ≡ e
  rid⊆ stop     = refl
  rid⊆ (drop e) = drop & rid⊆ e
  rid⊆ (keep e) = keep & rid⊆ e

  ass⊆ : ∀ {Γ Γ′ Γ″ Γ‴} (e″ : Γ″ ⊆ Γ‴) (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) →
         e″ ∘⊆ (e′ ∘⊆ e) ≡ (e″ ∘⊆ e′) ∘⊆ e
  ass⊆ stop      e′        e        = refl
  ass⊆ (drop e″) e′        e        = drop & ass⊆ e″ e′ e
  ass⊆ (keep e″) (drop e′) e        = drop & ass⊆ e″ e′ e
  ass⊆ (keep e″) (keep e′) (drop e) = drop & ass⊆ e″ e′ e
  ass⊆ (keep e″) (keep e′) (keep e) = keep & ass⊆ e″ e′ e

  ⟪⊆⟫ : Category lzero lzero
  ⟪⊆⟫ = record
          { Obj  = Ctx
          ; _▻_  = _⊆_
          ; id   = id⊆
          ; _∘_  = _∘⊆_
          ; lid▻ = lid⊆
          ; rid▻ = rid⊆
          ; ass▻ = ass⊆
          }

  ren∋ : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ∋ A → Γ′ ∋ A
  ren∋ stop     i       = i
  ren∋ (drop e) i       = suc (ren∋ e i)
  ren∋ (keep e) zero    = zero
  ren∋ (keep e) (suc i) = suc (ren∋ e i)

  wk∋ : ∀ {Γ A B} → Γ ∋ B → A ∷ Γ ∋ B
  wk∋ i = ren∋ wk⊆ i

  idren∋ : ∀ {Γ A} (i : Γ ∋ A) → ren∋ id⊆ i ≡ i
  idren∋ zero    = refl
  idren∋ (suc i) = suc & idren∋ i

  compren∋ : ∀ {Γ Γ′ Γ″ A} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (i : Γ ∋ A) →
             ren∋ (e′ ∘⊆ e) i ≡ (ren∋ e′ ∘ ren∋ e) i
  compren∋ stop      e        i       = refl
  compren∋ (drop e′) e        i       = suc & compren∋ e′ e i
  compren∋ (keep e′) (drop e) i       = suc & compren∋ e′ e i
  compren∋ (keep e′) (keep e) zero    = refl
  compren∋ (keep e′) (keep e) (suc i) = suc & compren∋ e′ e i

  module _ (⚠ : Funext) where
    ⟪ren∋⟫ : ∀ (A : Ty) → Presheaf (⟪⊆⟫ ᵒᵖ) lzero
    ⟪ren∋⟫ A = record
                 { ƒObj = _∋ A
                 ; ƒ    = ren∋
                 ; idƒ  = ⚠ idren∋
                 ; _∘ƒ_ = λ e′ e → ⚠ (compren∋ e′ e)
                 }

  injren∋ : ∀ {Γ Γ′ A} {e : Γ ⊆ Γ′} {i i′ : Γ ∋ A} → ren∋ e i ≡ ren∋ e i′ → i ≡ i′
  injren∋ {e = stop}   {i}     {i′}     eq   = eq
  injren∋ {e = drop e} {i}     {i′}     eq   = injren∋ (injsuc eq)
  injren∋ {e = keep e} {zero}  {zero}   refl = refl
  injren∋ {e = keep e} {suc i} {suc i′} eq   = suc & (injren∋ (injsuc eq))

  -- TODO: delete?
  unren∋ : ∀ {Γ Γ′ A} (e : Γ ⊆ Γ′) (i′ : Γ′ ∋ A) → Dec (Σ (Γ ∋ A) λ i → i′ ≡ ren∋ e i)
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

record TmKitParams : Set₁ where
  constructor kit
  field
    {Ty} : Set
  open TyKit Ty public
  field
    _⊢_ : Ctx → Ty → Set

module TmKit (κ : TmKitParams) where
  open TmKitParams κ
  tmkit = κ

  ty : ∀ {Γ A} → Γ ⊢ A → Ty
  ty {A = A} t = A

  infix 3 _⊢*_
  data _⊢*_ (Γ : Ctx) : Ctx → Set where
    []  : Γ ⊢* []
    _∷_ : ∀ {A Δ} (t : Γ ⊢ A) (ts : Γ ⊢* Δ) → Γ ⊢* A ∷ Δ

  -- TODO: consider using Data.List.Relation.Unary.All
  -- _⊢*_ : Ctx → Ctx → Set
  -- Γ ⊢* Δ = All (Γ ⊢_) Δ


----------------------------------------------------------------------------------------------------

record RenKitParams : Set₁ where
  constructor kit
  field
    {tmkit} : TmKitParams
  open TmKitParams tmkit public
  open TmKit tmkit public hiding (tmkit)
  field
    var : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
    ren : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A

module RenKit (κ : RenKitParams) where
  open RenKitParams κ
  renkit = κ

  wk : ∀ {Γ A B} → Γ ⊢ B → (A ∷ Γ) ⊢ B
  wk t = ren wk⊆ t

  -- Kovacs: flip _ₛ∘ₑ_
  rens : ∀ {Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⊢* Δ → Γ′ ⊢* Δ
  rens e []       = []
  rens e (t ∷ ts) = ren e t ∷ rens e ts

  wks : ∀ {Γ Δ A} → Γ ⊢* Δ → A ∷ Γ ⊢* Δ
  wks ts = rens wk⊆ ts

  lifts : ∀ {Γ Δ A} → Γ ⊢* Δ → A ∷ Γ ⊢* A ∷ Δ
  lifts ts = var zero ∷ wks ts

  -- Kovacs: ⌜_⌝ᵒᵖᵉ
  vars : ∀ {Γ Γ′} → Γ ⊆ Γ′ → Γ′ ⊢* Γ
  vars stop     = []
  vars (drop e) = wks (vars e)
  vars (keep e) = lifts (vars e)

  -- TODO: check if changing this affects anything
  ids : ∀ {Γ} → Γ ⊢* Γ
  ids = vars id⊆
  -- ids {[]}    = []
  -- ids {A ∷ Γ} = lifts ids

  refls : ∀ {Γ} → Γ ⊢* Γ
  refls = ids

  sub∋ : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ∋ A → Ξ ⊢ A
  sub∋ (s ∷ ss) zero    = s
  sub∋ (s ∷ ss) (suc i) = sub∋ ss i


----------------------------------------------------------------------------------------------------

record SubKitParams : Set₁ where
  constructor kit
  field
    renkit : RenKitParams
  open RenKitParams renkit public
  open RenKit renkit public hiding (renkit)
  field
    sub : ∀ {Γ Ξ A} → Ξ ⊢* Γ → Γ ⊢ A → Ξ ⊢ A

module SubKit (κ : SubKitParams) where
  open SubKitParams κ
  subkit = κ

  subs : ∀ {Γ Ξ Δ} → Ξ ⊢* Γ → Γ ⊢* Δ → Ξ ⊢* Δ
  subs ss []       = []
  subs ss (t ∷ ts) = sub ss t ∷ subs ss ts

  transs : ∀ {Γ Ξ Δ} → Ξ ⊢* Γ → Γ ⊢* Δ → Ξ ⊢* Δ
  transs = subs

  _∘s_ : ∀ {Γ Ξ Δ} → Γ ⊢* Δ → Ξ ⊢* Γ → Ξ ⊢* Δ
  _∘s_ = flip transs

  _[_] : ∀ {Γ A B} → (A ∷ Γ) ⊢ B → Γ ⊢ A → Γ ⊢ B
  t [ s ] = sub (s ∷ ids) t

  -- Kovacs: _ₑ∘ₛ_; flip?
  gets : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⊢* Δ′ → Γ ⊢* Δ
  gets stop     ts       = ts
  gets (drop e) (t ∷ ts) = gets e ts
  gets (keep e) (t ∷ ts) = t ∷ gets e ts


----------------------------------------------------------------------------------------------------

record DefEqKitParams : Set₁ where
  constructor kit
  field
    tmkit : TmKitParams
  open TmKitParams tmkit public
  open TmKit tmkit public hiding (tmkit)
  field
    {_≝_}  : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
    refl≝  : ∀ {Γ A} {t : Γ ⊢ A} → t ≝ t
    sym≝   : ∀ {Γ A} {t t′ : Γ ⊢ A} → t ≝ t′ → t′ ≝ t
    trans≝ : ∀ {Γ A} {t t′ t″ : Γ ⊢ A} → t ≝ t′ → t′ ≝ t″ → t ≝ t″

module DefEqKit (κ : DefEqKitParams) where
  open DefEqKitParams κ
  defeqkit = κ

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
