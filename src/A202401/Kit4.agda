module A202401.Kit4 where

open import A202401.Kit1 public


----------------------------------------------------------------------------------------------------

record ValKitParams : Set₁ where
  constructor kit
  field
    {Ty} : Set
  open TyKit Ty public
  field
    _⊩_ : Ctx → Ty → Set
    vren : ∀ {A W W′} → W ⊑ W′ → W ⊩ A → W′ ⊩ A

module ValKit (¶ : ValKitParams) where
  open ValKitParams ¶
  valkit = ¶

  infix 3 _⊩§_
  data _⊩§_ (W : Ctx) : Ctx → Set where
    ∙   : W ⊩§ ∙
    _,_ : ∀ {Δ A} (δ : W ⊩§ Δ) (v : W ⊩ A) → W ⊩§ Δ , A

  vren§ : ∀ {Δ W W′} → W ⊑ W′ → W ⊩§ Δ → W′ ⊩§ Δ
  vren§ ϱ ∙       = ∙
  vren§ ϱ (δ , v) = vren§ ϱ δ , vren ϱ v

  infix 3 _⊨_
  _⊨_ : Ctx → Ty → Set
  Γ ⊨ A = ∀ {W : Ctx} → W ⊩§ Γ → W ⊩ A

  ⟦_⟧∋ : ∀ {Γ A} → Γ ∋ A → Γ ⊨ A
  ⟦ zero  ⟧∋ (γ , v) = v
  ⟦ wk∋ i ⟧∋ (γ , v) = ⟦ i ⟧∋ γ


----------------------------------------------------------------------------------------------------

record ModelKitParams : Set₂ where
  constructor kit
  field
    {Ty} : Set
  open TyKit Ty public
  field
    {Model} : Set₁
    {World} : Model → Set
    {_≤_}   : ∀ (ℳ : Model) → World ℳ → World ℳ → Set -- TODO: implify?
    _⊩_    : ∀ {ℳ} → World ℳ → Ty → Set
    vren    : ∀ {ℳ A W W′} → _≤_ ℳ W W′ → W ⊩ A → W′ ⊩ A

module ModelKit (¶ : ModelKitParams) where
  open ModelKitParams ¶
  modelkit = ¶

  module _ {ℳ : Model} where
    infix 3 _⊩§_
    data _⊩§_ (W : World ℳ) : Ctx → Set where
      ∙   : W ⊩§ ∙
      _,_ : ∀ {Δ A} (δ : W ⊩§ Δ) (v : W ⊩ A) → W ⊩§ Δ , A

    vren§ : ∀ {Δ W W′} → _≤_ ℳ W W′ → W ⊩§ Δ → W′ ⊩§ Δ
    vren§ ϱ ∙       = ∙
    vren§ ϱ (δ , v) = vren§ ϱ δ , vren ϱ v

  infix 3 _/_⊩_
  _/_⊩_ : ∀ (ℳ : Model) (W : World ℳ) → Ty → Set
  ℳ / W ⊩ A = _⊩_ {ℳ} W A

  infix 3 _/_⊩§_
  _/_⊩§_ : ∀ (ℳ : Model) (W : World ℳ) → Ctx → Set
  ℳ / W ⊩§ Δ = _⊩§_ {ℳ} W Δ

  infix 3 _⊨_
  _⊨_ : Ctx → Ty → Set₁
  Γ ⊨ A = ∀ {ℳ : Model} {W : World ℳ} → ℳ / W ⊩§ Γ → ℳ / W ⊩ A

  ⟦_⟧∋ : ∀ {Γ A} → Γ ∋ A → Γ ⊨ A
  ⟦ zero  ⟧∋ (γ , v) = v
  ⟦ wk∋ i ⟧∋ (γ , v) = ⟦ i ⟧∋ γ


----------------------------------------------------------------------------------------------------

record SplitModelKitParams : Set₂ where
  constructor kit
  field
    {Ty} : Set
  open TyKit Ty public
  field
    {BaseModel}  : Set₁
    {SplitModel} : BaseModel → Set₁
    {World}      : ∀ {ℬ} → SplitModel ℬ → Set
    {_≤_}        : ∀ {ℬ} (ℳ : SplitModel ℬ) → World ℳ → World ℳ → Set -- TODO: implify?
    _⊩_         : ∀ {ℬ} (ℳ : SplitModel ℬ) → World ℳ → Ty → Set -- TODO: implify
    vren         : ∀ {ℬ} {ℳ : SplitModel ℬ} {A W W′} → _≤_ ℳ W W′ → _⊩_ ℳ W A → _⊩_ ℳ W′ A

module SplitModelKit (¶ : SplitModelKitParams) where
  open SplitModelKitParams ¶
  splitmodelkit = ¶

  module _ {ℬ} {ℳ : SplitModel ℬ} where
    infix 3 _⊩§_
    data _⊩§_ (W : World ℳ) : Ctx → Set where
      ∙   : W ⊩§ ∙
      _,_ : ∀ {Δ A} (δ : W ⊩§ Δ) (v : _⊩_ ℳ W A) → W ⊩§ Δ , A

    vren§ : ∀ {Δ W W′} → _≤_ ℳ W W′ → W ⊩§ Δ → W′ ⊩§ Δ
    vren§ ϱ ∙       = ∙
    vren§ ϱ (δ , v) = vren§ ϱ δ , vren ϱ v

  infix 3 _/_⊩_
  _/_⊩_ : ∀ {ℬ} (ℳ : SplitModel ℬ) (W : World ℳ) → Ty → Set
  ℳ / W ⊩ A = _⊩_ ℳ W A

  infix 3 _/_⊩§_
  _/_⊩§_ : ∀ {ℬ} (ℳ : SplitModel ℬ) (W : World ℳ) → Ctx → Set
  ℳ / W ⊩§ Δ = _⊩§_ {ℳ = ℳ} W Δ

  infix 3 _⊨_
  _⊨_ : Ctx → Ty → Set₁
  Γ ⊨ A = ∀ {ℬ} {ℳ : SplitModel ℬ} {W : World ℳ} → ℳ / W ⊩§ Γ → ℳ / W ⊩ A

  ⟦_⟧∋ : ∀ {Γ A} → Γ ∋ A → Γ ⊨ A
  ⟦ zero  ⟧∋ (γ , v) = v
  ⟦ wk∋ i ⟧∋ (γ , v) = ⟦ i ⟧∋ γ


----------------------------------------------------------------------------------------------------
