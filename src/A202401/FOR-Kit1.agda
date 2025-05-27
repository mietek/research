module A202401.FOR-Kit1 where

open import A202401.FOR public


----------------------------------------------------------------------------------------------------

module TyKit (Ty : Set) where
  Ctx : Set
  Ctx = Rist Ty


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

  infix 3 _⊢§_
  data _⊢§_ (Γ : Ctx) : Ctx → Set where
    ∙   : Γ ⊢§ ∙
    _,_ : ∀ {Δ A} (τ : Γ ⊢§ Δ) (t : Γ ⊢ A) → Γ ⊢§ Δ , A

  -- TODO: consider using Data.List.Relation.Unary.All
  -- _⊢§_ : Ctx → Ctx → Set
  -- Γ ⊢§ Δ = All (Γ ⊢_) Δ


----------------------------------------------------------------------------------------------------

record RenKitParams : Set₁ where
  constructor kit
  field
    {tmkit} : TmKitParams
  open TmKitParams tmkit public
  open TmKit tmkit public hiding (tmkit)
  field
    var : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
    ren : ∀ {Γ Γ′ A} → Γ ⊑ Γ′ → Γ ⊢ A → Γ′ ⊢ A

module RenKit (¶ : RenKitParams) where
  open RenKitParams ¶
  renkit = ¶

  wk : ∀ {B Γ A} → Γ ⊢ A → Γ , B ⊢ A
  wk t = ren (wk⊑ id⊑) t

  -- Kovacs: flip _ₛ∘ₑ_
  ren§ : ∀ {Γ Γ′ Δ} → Γ ⊑ Γ′ → Γ ⊢§ Δ → Γ′ ⊢§ Δ
  ren§ ϱ ∙       = ∙
  ren§ ϱ (τ , t) = ren§ ϱ τ , ren ϱ t

  _◐_ : ∀ {Γ Γ′ Δ} → Γ ⊢§ Δ → Γ ⊑ Γ′ → Γ′ ⊢§ Δ
  _◐_ = flip ren§

  wk§ : ∀ {B Γ Δ} → Γ ⊢§ Δ → Γ , B ⊢§ Δ
  wk§ τ = ren§ (wk⊑ id⊑) τ

  lift§ : ∀ {B Γ Δ} → Γ ⊢§ Δ → Γ , B ⊢§ Δ , B
  lift§ τ = wk§ τ , var zero

  -- Kovacs: ⌜_⌝ᵒᵖᵉ
  var§ : ∀ {Γ Γ′} → Γ ⊑ Γ′ → Γ′ ⊢§ Γ
  var§ ∙       = ∙
  var§ (τ , i) = var§ τ , var i

  -- TODO: defining id§ using var§ breaks lidren§
  id§ refl§ : ∀ {Γ} → Γ ⊢§ Γ
  id§ {∙}     = ∙
  id§ {Γ , A} = lift§ id§
  -- id§ = var§ id⊑
  refl§ = id§

  sub∋ : ∀ {Γ Ξ A} → Ξ ⊢§ Γ → Γ ∋ A → Ξ ⊢ A
  sub∋ (σ , s) zero    = s
  sub∋ (σ , s) (wk∋ i) = sub∋ σ i


----------------------------------------------------------------------------------------------------

record SubKitParams : Set₁ where
  constructor kit
  field
    renkit : RenKitParams
  open RenKitParams renkit public
  open RenKit renkit public hiding (renkit)
  field
    sub : ∀ {Γ Ξ A} → Ξ ⊢§ Γ → Γ ⊢ A → Ξ ⊢ A

module SubKit (¶ : SubKitParams) where
  open SubKitParams ¶
  subkit = ¶

  -- Kovacs: _∘ₛ_
  sub§ trans§ : ∀ {Γ Ξ Δ} → Ξ ⊢§ Γ → Γ ⊢§ Δ → Ξ ⊢§ Δ
  sub§ σ ∙       = ∙
  sub§ σ (τ , t) = sub§ σ τ , sub σ t
  trans§ = sub§

  _●_ : ∀ {Γ Ξ Δ} → Γ ⊢§ Δ → Ξ ⊢§ Γ → Ξ ⊢§ Δ
  _●_ = flip sub§

  _[_] : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A → Γ ⊢ B
  t [ s ] = sub (id§ , s) t

  -- Kovacs: _ₑ∘ₛ_
  get§ _◑_ : ∀ {Γ Δ Δ′} → Δ ⊑ Δ′ → Γ ⊢§ Δ′ → Γ ⊢§ Δ
  get§ ∙       τ = ∙
  get§ (ϱ , i) τ = get§ ϱ τ , sub τ (var i)
  _◑_ = get§


----------------------------------------------------------------------------------------------------

record RenNNFKitParams : Set₁ where
  constructor kit
  field
    renkit : RenKitParams
  open RenKitParams renkit public
  open RenKit renkit public hiding (renkit)
  field
    {NNF}  : ∀ {Γ A} → Γ ⊢ A → Set
    var-   : ∀ {Γ A} {i : Γ ∋ A} → NNF (var i)
    renNNF : ∀ {Γ Γ′ A} {t : Γ ⊢ A} (ϱ : Γ ⊑ Γ′) → NNF t → NNF (ren ϱ t)

module RenNNFKit (¶ : RenNNFKitParams) where
  open RenNNFKitParams ¶
  rennnfkit = ¶

  data NNF§ {Γ} : ∀ {Δ} → Γ ⊢§ Δ → Set where
    ∙   : NNF§ ∙
    _,_ : ∀ {Δ A} {τ : Γ ⊢§ Δ} {t : Γ ⊢ A} (ψ : NNF§ τ) (p : NNF t) → NNF§ (τ , t)

  renNNF§ : ∀ {Γ Γ′ Δ} {σ : Γ ⊢§ Δ} (ϱ : Γ ⊑ Γ′) → NNF§ σ → NNF§ (ren§ ϱ σ)
  renNNF§ ϱ ∙       = ∙
  renNNF§ ϱ (ψ , p) = renNNF§ ϱ ψ , renNNF ϱ p

  wkNNF§ : ∀ {B Γ Δ} {σ : Γ ⊢§ Δ} → NNF§ σ → NNF§ (wk§ {B} σ)
  wkNNF§ ψ = renNNF§ (wk⊑ id⊑) ψ

  liftNNF§ : ∀ {B Γ Δ} {σ : Γ ⊢§ Δ} → NNF§ σ → NNF§ (lift§ {B} σ)
  liftNNF§ ψ = wkNNF§ ψ , var-

  sub∋NNF : ∀ {Γ Ξ A} {σ : Ξ ⊢§ Γ} {i : Γ ∋ A} → NNF§ σ → NNF (sub∋ σ i)
  sub∋NNF {i = zero}  (ψ , p) = p
  sub∋NNF {i = wk∋ i} (ψ , p) = sub∋NNF ψ


----------------------------------------------------------------------------------------------------

-- TODO: refactor
record DefEqKitParams : Set₁ where
  constructor kit
  field
    tmkit : TmKitParams
  open TmKitParams tmkit public
  open TmKit tmkit public hiding (tmkit)
  infix 4 _≝_
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
    begin deq = deq

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
