module Kit1-Renamings where

open import Common public


----------------------------------------------------------------------------------------------------

module TyKit (Ty : Set) where
  Ctx : Set
  Ctx = List Ty

  open FirstOrderRenamings public


----------------------------------------------------------------------------------------------------

record TmKitParams : Set₁ where
  constructor kit
  field
    {Ty} : Set
  open TyKit Ty public
  infix 3 _⊢_
  field
    _⊢_ : Ctx → Ty → Set

module TmKit (¶ : TmKitParams) where
  open TmKitParams ¶
  tmkit = ¶

  ty : ∀ {A Γ} → Γ ⊢ A → Ty
  ty {A} t = A

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

module RenKit (¶ : RenKitParams) where
  open RenKitParams ¶
  renkit = ¶

  wk : ∀ {B Γ A} → Γ ⊢ A → B ∷ Γ ⊢ A
  wk t = ren (wk⊆ id⊆) t

  -- Kovacs: flip _ₛ∘ₑ_
  ren* : ∀ {Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⊢* Δ → Γ′ ⊢* Δ
  ren* js []       = []
  ren* js (t ∷ ts) = ren js t ∷ ren* js ts

  _◐_ : ∀ {Γ Γ′ Δ} → Γ ⊢* Δ → Γ ⊆ Γ′ → Γ′ ⊢* Δ
  _◐_ = flip ren*

  wk* : ∀ {B Γ Δ} → Γ ⊢* Δ → B ∷ Γ ⊢* Δ
  wk* ts = ren* (wk⊆ id⊆) ts

  lift* : ∀ {B Γ Δ} → Γ ⊢* Δ → B ∷ Γ ⊢* B ∷ Δ
  lift* ts = var zero ∷ wk* ts

  lift*² : ∀ {B C Γ Δ} → Γ ⊢* Δ → C ∷ B ∷ Γ ⊢* C ∷ B ∷ Δ
  lift*² = lift* ∘ lift*

  -- Kovacs: ⌜_⌝ᵒᵖᵉ
  var* : ∀ {Γ Γ′} → Γ ⊆ Γ′ → Γ′ ⊢* Γ
  var* []       = []
  var* (i ∷ is) = var i ∷ var* is

  -- defining id* using var* breaks lidren*
  id* : ∀ {Γ} → Γ ⊢* Γ
  id* {[]}    = []
  id* {A ∷ Γ} = lift* id*
  -- id* = var* id⊆

  refl* : ∀ {Γ} → Γ ⊢* Γ
  refl* = id*

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

module SubKit (¶ : SubKitParams) where
  open SubKitParams ¶
  subkit = ¶

  sub* : ∀ {Γ Ξ Δ} → Ξ ⊢* Γ → Γ ⊢* Δ → Ξ ⊢* Δ
  sub* ss []       = []
  sub* ss (t ∷ ts) = sub ss t ∷ sub* ss ts

  trans* : ∀ {Γ Ξ Δ} → Ξ ⊢* Γ → Γ ⊢* Δ → Ξ ⊢* Δ
  trans* = sub*

  _●_ : ∀ {Γ Ξ Δ} → Γ ⊢* Δ → Ξ ⊢* Γ → Ξ ⊢* Δ
  _●_ = flip sub*

  _[_] : ∀ {Γ A B} → A ∷ Γ ⊢ B → Γ ⊢ A → Γ ⊢ B
  t [ s ] = sub (s ∷ id*) t

  -- Kovacs: _ₑ∘ₛ_
  get* : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⊢* Δ′ → Γ ⊢* Δ
  get* []       ts = []
  get* (i ∷ is) ts = sub ts (var i) ∷ get* is ts

  _◑_ : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⊢* Δ′ → Γ ⊢* Δ
  _◑_ = get*


----------------------------------------------------------------------------------------------------

-- TODO: only needs _⊢_; refactor?
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

module DefEqKit (¶ : DefEqKitParams) where
  open DefEqKitParams ¶
  defeqkit = ¶

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
