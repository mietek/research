module A201706.IS4SyntaxNoTerms where

open import A201706.IS4 public
open IS4List public


-- Contexts.

Cx : Set
Cx = BoxTy⋆ ∧ Ty⋆


-- Derivations.

mutual
  infix 3 _⊢_
  data _⊢_ : Cx → Ty → Set where
    var   : ∀ {Δ Γ A} →
              Γ ∋ A →
              Δ ⁏ Γ ⊢ A
    mvar  : ∀ {Δ Γ A} →
              Δ ∋ □ A →
              Δ ⁏ Γ ⊢ A
    lam   : ∀ {Δ Γ A B} →
              Δ ⁏ Γ , A ⊢ B →
              Δ ⁏ Γ ⊢ A ⇒ B
    app   : ∀ {Δ Γ A B} →
              Δ ⁏ Γ ⊢ A ⇒ B → Δ ⁏ Γ ⊢ A →
              Δ ⁏ Γ ⊢ B
    box   : ∀ {Δ Γ A} →
              Δ ⟨⊢⟩ □ A →
              Δ ⁏ Γ ⊢ □ A
    unbox : ∀ {Δ Γ A C} →
              Δ ⁏ Γ ⊢ □ A → Δ , □ A ⁏ Γ ⊢ C →
              Δ ⁏ Γ ⊢ C

  infix 3 _⟨⊢⟩_
  _⟨⊢⟩_ : BoxTy⋆ → BoxTy → Set
  Δ ⟨⊢⟩ □ A = Δ ⁏ ∅ ⊢ A

mutual
  mono⊢ : ∀ {Δ Γ Δ′ Γ′ A} → Δ′ ⊇ Δ → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ A → Δ′ ⁏ Γ′ ⊢ A
  mono⊢ ζ η (var 𝒾)     = var (mono∋ η 𝒾)
  mono⊢ ζ η (mvar 𝒾)    = mvar (mono∋ ζ 𝒾)
  mono⊢ ζ η (lam 𝒟)     = lam (mono⊢ ζ (lift η) 𝒟)
  mono⊢ ζ η (app 𝒟 ℰ)   = app (mono⊢ ζ η 𝒟) (mono⊢ ζ η ℰ)
  mono⊢ ζ η (box 𝒟)     = box (mono⟨⊢⟩ ζ 𝒟)
  mono⊢ ζ η (unbox 𝒟 ℰ) = unbox (mono⊢ ζ η 𝒟) (mono⊢ (lift ζ) η ℰ)

  mono⟨⊢⟩ : ∀ {Δ Δ′ A} → Δ′ ⊇ Δ → Δ ⟨⊢⟩ □ A → Δ′ ⟨⊢⟩ □ A
  mono⟨⊢⟩ ζ 𝒟 = mono⊢ ζ refl⊇ 𝒟

mutual
  idmono⊢ : ∀ {Δ Γ A} → (𝒟 : Δ ⁏ Γ ⊢ A) → mono⊢ refl⊇ refl⊇ 𝒟 ≡ 𝒟
  idmono⊢ (var 𝒾)     = cong var (idmono∋ 𝒾)
  idmono⊢ (mvar 𝒾)    = cong mvar (idmono∋ 𝒾)
  idmono⊢ (lam 𝒟)     = cong lam (idmono⊢ 𝒟)
  idmono⊢ (app 𝒟 ℰ)   = cong² app (idmono⊢ 𝒟) (idmono⊢ ℰ)
  idmono⊢ (box 𝒟)     = cong box (idmono⟨⊢⟩ 𝒟)
  idmono⊢ (unbox 𝒟 ℰ) = cong² unbox (idmono⊢ 𝒟) (idmono⊢ ℰ)

  idmono⟨⊢⟩ : ∀ {Δ A} → (𝒟 : Δ ⟨⊢⟩ □ A) → mono⟨⊢⟩ refl⊇ 𝒟 ≡ 𝒟
  idmono⟨⊢⟩ 𝒟 = idmono⊢ 𝒟

mutual
  assocmono⊢ : ∀ {Δ Γ Δ′ Γ′ Γ″ Δ″ A} →
                  (ζ′ : Δ″ ⊇ Δ′) (η′ : Γ″ ⊇ Γ′) (ζ : Δ′ ⊇ Δ) (η : Γ′ ⊇ Γ) (𝒟 : Δ ⁏ Γ ⊢ A) →
                  mono⊢ ζ′ η′ (mono⊢ ζ η 𝒟) ≡ mono⊢ (trans⊇ ζ′ ζ) (trans⊇ η′ η) 𝒟
  assocmono⊢ ζ′ η′ ζ η (var 𝒾)     = cong var (assocmono∋ η′ η 𝒾)
  assocmono⊢ ζ′ η′ ζ η (mvar 𝒾)    = cong mvar (assocmono∋ ζ′ ζ 𝒾)
  assocmono⊢ ζ′ η′ ζ η (lam 𝒟)     = cong lam (assocmono⊢ ζ′ (lift η′) ζ (lift η) 𝒟)
  assocmono⊢ ζ′ η′ ζ η (app 𝒟 ℰ)   = cong² app (assocmono⊢ ζ′ η′ ζ η 𝒟) (assocmono⊢ ζ′ η′ ζ η ℰ)
  assocmono⊢ ζ′ η′ ζ η (box 𝒟)     = cong box (assocmono⟨⊢⟩ ζ′ ζ 𝒟)
  assocmono⊢ ζ′ η′ ζ η (unbox 𝒟 ℰ) = cong² unbox (assocmono⊢ ζ′ η′ ζ η 𝒟) (assocmono⊢ (lift ζ′) η′ (lift ζ) η ℰ)

  assocmono⟨⊢⟩ : ∀ {Δ Δ′ Δ″ A} →
                    (ζ′ : Δ″ ⊇ Δ′) (ζ : Δ′ ⊇ Δ) (𝒟 : Δ ⟨⊢⟩ A) →
                    mono⟨⊢⟩ ζ′ (mono⟨⊢⟩ ζ 𝒟) ≡ mono⟨⊢⟩ (trans⊇ ζ′ ζ) 𝒟
  assocmono⟨⊢⟩ ζ′ ζ 𝒟 = assocmono⊢ ζ′ refl⊇ ζ refl⊇ 𝒟


-- Lists of derivations.

infix 3 _⊢⋆_
_⊢⋆_ : Cx → Ty⋆ → Set
Δ ⁏ Γ ⊢⋆ Ξ = All (Δ ⁏ Γ ⊢_) Ξ

mono⊢⋆ : ∀ {Δ Γ Δ′ Γ′ Ξ} → Δ′ ⊇ Δ → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢⋆ Ξ → Δ′ ⁏ Γ′ ⊢⋆ Ξ
mono⊢⋆ ζ η ξ = mapAll (mono⊢ ζ η) ξ

refl⊢⋆ : ∀ {Γ Δ} → Δ ⁏ Γ ⊢⋆ Γ
refl⊢⋆ {∅}     = ∅
refl⊢⋆ {Γ , A} = mono⊢⋆ refl⊇ (weak refl⊇) refl⊢⋆ , var zero

lookup⊢ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ → Ξ ∋ A → Δ ⁏ Γ ⊢ A
lookup⊢ ξ 𝒾 = lookupAll ξ 𝒾

graft⊢ : ∀ {Δ Γ Ψ A} → Δ ⁏ Γ ⊢⋆ Ψ → Δ ⁏ Ψ ⊢ A → Δ ⁏ Γ ⊢ A
graft⊢ ψ (var 𝒾)     = lookup⊢ ψ 𝒾
graft⊢ ψ (mvar 𝒾)    = mvar 𝒾
graft⊢ ψ (lam 𝒟)     = lam (graft⊢ (mono⊢⋆ refl⊇ (weak refl⊇) ψ , var zero) 𝒟)
graft⊢ ψ (app 𝒟 ℰ)   = app (graft⊢ ψ 𝒟) (graft⊢ ψ ℰ)
graft⊢ ψ (box 𝒟)     = box (graft⊢ ∅ 𝒟)
graft⊢ ψ (unbox 𝒟 ℰ) = unbox (graft⊢ ψ 𝒟) (graft⊢ (mono⊢⋆ (weak refl⊇) refl⊇ ψ) ℰ)

graft⊢⋆ : ∀ {Δ Γ Ψ Ξ} → Δ ⁏ Γ ⊢⋆ Ψ → Δ ⁏ Ψ ⊢⋆ Ξ → Δ ⁏ Γ ⊢⋆ Ξ
graft⊢⋆ ψ ξ = mapAll (graft⊢ ψ) ξ

trans⊢⋆ : ∀ {Δ Γ Γ′ Γ″} → Δ ⁏ Γ″ ⊢⋆ Γ′ → Δ ⁏ Γ′ ⊢⋆ Γ → Δ ⁏ Γ″ ⊢⋆ Γ
trans⊢⋆ γ′ γ = graft⊢⋆ γ′ γ


-- TODO: Needs a name.

infix 3 _⟨⊢⟩⋆_
_⟨⊢⟩⋆_ : BoxTy⋆ → BoxTy⋆ → Set
Δ ⟨⊢⟩⋆ Ξ = All (Δ ⟨⊢⟩_) Ξ

mono⟨⊢⟩⋆ : ∀ {Δ Δ′ Ξ} → Δ′ ⊇ Δ → Δ ⟨⊢⟩⋆ Ξ → Δ′ ⟨⊢⟩⋆ Ξ
mono⟨⊢⟩⋆ ζ ξ = mapAll (mono⟨⊢⟩ ζ) ξ

mrefl⟨⊢⟩⋆ : ∀ {Δ} → Δ ⟨⊢⟩⋆ Δ
mrefl⟨⊢⟩⋆ {∅}       = ∅
mrefl⟨⊢⟩⋆ {Δ , □ A} = mono⟨⊢⟩⋆ (weak refl⊇) mrefl⟨⊢⟩⋆ , mvar zero

mlookup⟨⊢⟩ : ∀ {Δ Ξ A} → Δ ⟨⊢⟩⋆ Ξ → Ξ ∋ □ A → Δ ⟨⊢⟩ □ A
mlookup⟨⊢⟩ ξ 𝒾 = lookupAll ξ 𝒾

mgraft⊢ : ∀ {Δ Γ Φ A} → Δ ⟨⊢⟩⋆ Φ → Φ ⁏ Γ ⊢ A → Δ ⁏ Γ ⊢ A
mgraft⊢ φ (var 𝒾)     = var 𝒾
mgraft⊢ φ (mvar 𝒾)    = graft⊢ ∅ (mlookup⟨⊢⟩ φ 𝒾)
mgraft⊢ φ (lam 𝒟)     = lam (mgraft⊢ φ 𝒟)
mgraft⊢ φ (app 𝒟 ℰ)   = app (mgraft⊢ φ 𝒟) (mgraft⊢ φ ℰ)
mgraft⊢ φ (box 𝒟)     = box (mgraft⊢ φ 𝒟)
mgraft⊢ φ (unbox 𝒟 ℰ) = unbox (mgraft⊢ φ 𝒟) (mgraft⊢ (mono⟨⊢⟩⋆ (weak refl⊇) φ , mvar zero) ℰ)

mgraft⊢⋆ : ∀ {Δ Φ Ψ Ξ} → Δ ⟨⊢⟩⋆ Φ → Φ ⁏ Ψ ⊢⋆ Ξ → Δ ⁏ Ψ ⊢⋆ Ξ
mgraft⊢⋆ φ ξ = mapAll (mgraft⊢ φ) ξ

mgraft⟨⊢⟩ : ∀ {Δ Φ A} → Δ ⟨⊢⟩⋆ Φ → Φ ⟨⊢⟩ □ A → Δ ⟨⊢⟩ □ A
mgraft⟨⊢⟩ φ 𝒟 = mgraft⊢ φ 𝒟

mgraft⟨⊢⟩⋆ : ∀ {Δ Φ Ξ} → Δ ⟨⊢⟩⋆ Φ → Φ ⟨⊢⟩⋆ Ξ → Δ ⟨⊢⟩⋆ Ξ
mgraft⟨⊢⟩⋆ φ ξ = mapAll (mgraft⟨⊢⟩ φ) ξ

mtrans⟨⊢⟩⋆ : ∀ {Δ Δ′ Δ″} → Δ″ ⟨⊢⟩⋆ Δ′ → Δ′ ⟨⊢⟩⋆ Δ → Δ″ ⟨⊢⟩⋆ Δ
mtrans⟨⊢⟩⋆ δ′ δ = mgraft⟨⊢⟩⋆ δ′ δ


-- Normal forms.

mutual
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ : Cx → Ty → Set where
    lamⁿᶠ   : ∀ {Δ Γ A B} →
                Δ ⁏ Γ , A ⊢ⁿᶠ B →
                Δ ⁏ Γ ⊢ⁿᶠ A ⇒ B
    boxⁿᶠ   : ∀ {Δ Γ A} →
                Δ ⟨⊢⟩ □ A →
                Δ ⁏ Γ ⊢ⁿᶠ □ A
    neⁿᶠ    : ∀ {Δ Γ A} →
                Δ ⁏ Γ ⊢ⁿᵉ A →
                Δ ⁏ Γ ⊢ⁿᶠ A

  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ : Cx → Ty → Set where
    varⁿᵉ   : ∀ {Δ Γ A} →
                Γ ∋ A →
                Δ ⁏ Γ ⊢ⁿᵉ A
    mvarⁿᵉ  : ∀ {Δ Γ A} →
                Δ ∋ □ A →
                Δ ⁏ Γ ⊢ⁿᵉ A
    appⁿᵉ   : ∀ {Δ Γ A B} →
                Δ ⁏ Γ ⊢ⁿᵉ A ⇒ B → Δ ⁏ Γ ⊢ⁿᶠ A →
                Δ ⁏ Γ ⊢ⁿᵉ B
    unboxⁿᵉ : ∀ {Δ Γ A C} →
                Δ ⁏ Γ ⊢ⁿᵉ □ A → Δ , □ A ⁏ Γ ⊢ⁿᶠ C →
                Δ ⁏ Γ ⊢ⁿᵉ C

mutual
  mono⊢ⁿᶠ : ∀ {Δ Γ Δ′ Γ′ A} → Δ′ ⊇ Δ → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ⁿᶠ A → Δ′ ⁏ Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ ζ η (lamⁿᶠ 𝒟)     = lamⁿᶠ (mono⊢ⁿᶠ ζ (lift η) 𝒟)
  mono⊢ⁿᶠ ζ η (boxⁿᶠ 𝒟)     = boxⁿᶠ (mono⟨⊢⟩ ζ 𝒟)
  mono⊢ⁿᶠ ζ η (neⁿᶠ 𝒟)      = neⁿᶠ (mono⊢ⁿᵉ ζ η 𝒟)

  mono⊢ⁿᵉ : ∀ {Δ Γ Δ′ Γ′ A} → Δ′ ⊇ Δ → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ⁿᵉ A → Δ′ ⁏ Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ ζ η (varⁿᵉ 𝒾)     = varⁿᵉ (mono∋ η 𝒾)
  mono⊢ⁿᵉ ζ η (mvarⁿᵉ 𝒾)    = mvarⁿᵉ (mono∋ ζ 𝒾)
  mono⊢ⁿᵉ ζ η (appⁿᵉ 𝒟 ℰ)   = appⁿᵉ (mono⊢ⁿᵉ ζ η 𝒟) (mono⊢ⁿᶠ ζ η ℰ)
  mono⊢ⁿᵉ ζ η (unboxⁿᵉ 𝒟 ℰ) = unboxⁿᵉ (mono⊢ⁿᵉ ζ η 𝒟) (mono⊢ⁿᶠ (lift ζ) η ℰ)

mutual
  idmono⊢ⁿᶠ : ∀ {Δ Γ A} → (𝒟 : Δ ⁏ Γ ⊢ⁿᶠ A) → mono⊢ⁿᶠ refl⊇ refl⊇ 𝒟 ≡ 𝒟
  idmono⊢ⁿᶠ (lamⁿᶠ 𝒟)     = cong lamⁿᶠ (idmono⊢ⁿᶠ 𝒟)
  idmono⊢ⁿᶠ (boxⁿᶠ 𝒟)     = cong boxⁿᶠ (idmono⟨⊢⟩ 𝒟)
  idmono⊢ⁿᶠ (neⁿᶠ 𝒟)      = cong neⁿᶠ (idmono⊢ⁿᵉ 𝒟)

  idmono⊢ⁿᵉ : ∀ {Δ Γ A} → (𝒟 : Δ ⁏ Γ ⊢ⁿᵉ A) → mono⊢ⁿᵉ refl⊇ refl⊇ 𝒟 ≡ 𝒟
  idmono⊢ⁿᵉ (varⁿᵉ 𝒾)     = cong varⁿᵉ (idmono∋ 𝒾)
  idmono⊢ⁿᵉ (mvarⁿᵉ 𝒾)    = cong mvarⁿᵉ (idmono∋ 𝒾)
  idmono⊢ⁿᵉ (appⁿᵉ 𝒟 ℰ)   = cong² appⁿᵉ (idmono⊢ⁿᵉ 𝒟) (idmono⊢ⁿᶠ ℰ)
  idmono⊢ⁿᵉ (unboxⁿᵉ 𝒟 ℰ) = cong² unboxⁿᵉ (idmono⊢ⁿᵉ 𝒟) (idmono⊢ⁿᶠ ℰ)

mutual
  assocmono⊢ⁿᶠ : ∀ {Δ Γ Δ′ Γ′ Γ″ Δ″ A} →
                    (ζ′ : Δ″ ⊇ Δ′) (η′ : Γ″ ⊇ Γ′) (ζ : Δ′ ⊇ Δ) (η : Γ′ ⊇ Γ) (𝒟 : Δ ⁏ Γ ⊢ⁿᶠ A) →
                    mono⊢ⁿᶠ ζ′ η′ (mono⊢ⁿᶠ ζ η 𝒟) ≡ mono⊢ⁿᶠ (trans⊇ ζ′ ζ) (trans⊇ η′ η) 𝒟
  assocmono⊢ⁿᶠ ζ′ η′ ζ η (lamⁿᶠ 𝒟)     = cong lamⁿᶠ (assocmono⊢ⁿᶠ ζ′ (lift η′) ζ (lift η) 𝒟)
  assocmono⊢ⁿᶠ ζ′ η′ ζ η (boxⁿᶠ 𝒟)     = cong boxⁿᶠ (assocmono⟨⊢⟩ ζ′ ζ 𝒟)
  assocmono⊢ⁿᶠ ζ′ η′ ζ η (neⁿᶠ 𝒟)      = cong neⁿᶠ (assocmono⊢ⁿᵉ ζ′ η′ ζ η 𝒟)

  assocmono⊢ⁿᵉ : ∀ {Δ Γ Δ′ Γ′ Γ″ Δ″ A} →
                    (ζ′ : Δ″ ⊇ Δ′) (η′ : Γ″ ⊇ Γ′) (ζ : Δ′ ⊇ Δ) (η : Γ′ ⊇ Γ) (𝒟 : Δ ⁏ Γ ⊢ⁿᵉ A) →
                    mono⊢ⁿᵉ ζ′ η′ (mono⊢ⁿᵉ ζ η 𝒟) ≡ mono⊢ⁿᵉ (trans⊇ ζ′ ζ) (trans⊇ η′ η) 𝒟
  assocmono⊢ⁿᵉ ζ′ η′ ζ η (varⁿᵉ 𝒾)     = cong varⁿᵉ (assocmono∋ η′ η 𝒾)
  assocmono⊢ⁿᵉ ζ′ η′ ζ η (mvarⁿᵉ 𝒾)    = cong mvarⁿᵉ (assocmono∋ ζ′ ζ 𝒾)
  assocmono⊢ⁿᵉ ζ′ η′ ζ η (appⁿᵉ 𝒟 ℰ)   = cong² appⁿᵉ (assocmono⊢ⁿᵉ ζ′ η′ ζ η 𝒟) (assocmono⊢ⁿᶠ ζ′ η′ ζ η ℰ)
  assocmono⊢ⁿᵉ ζ′ η′ ζ η (unboxⁿᵉ 𝒟 ℰ) = cong² unboxⁿᵉ (assocmono⊢ⁿᵉ ζ′ η′ ζ η 𝒟) (assocmono⊢ⁿᶠ (lift ζ′) η′ (lift ζ) η ℰ)


-- Lists of normal forms.

infix 3 _⊢⋆ⁿᵉ_
_⊢⋆ⁿᵉ_ : Cx → Ty⋆ → Set
Δ ⁏ Γ ⊢⋆ⁿᵉ Ξ = All (Δ ⁏ Γ ⊢ⁿᵉ_) Ξ

mono⊢⋆ⁿᵉ : ∀ {Δ Γ Δ′ Γ′ Ξ} → Δ′ ⊇ Δ → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢⋆ⁿᵉ Ξ → Δ′ ⁏ Γ′ ⊢⋆ⁿᵉ Ξ
mono⊢⋆ⁿᵉ ζ η ξ = mapAll (mono⊢ⁿᵉ ζ η) ξ


-- Example derivations.

v₀ : ∀ {Δ Γ A} →
       Δ ⁏ Γ , A ⊢ A
v₀ = var zero

v₁ : ∀ {Δ Γ A B} →
       Δ ⁏ Γ , A , B ⊢ A
v₁ = var (suc zero)

v₂ : ∀ {Δ Γ A B C} →
       Δ ⁏ Γ , A , B , C ⊢ A
v₂ = var (suc (suc zero))

mv₀ : ∀ {Δ Γ A} →
        Δ , □ A ⁏ Γ ⊢ A
mv₀ = mvar zero

mv₁ : ∀ {Δ Γ A B} →
        Δ , □ A , □ B ⁏ Γ ⊢ A
mv₁ = mvar (suc zero)

mv₂ : ∀ {Δ Γ A B C} →
        Δ , □ A , □ B , □ C ⁏ Γ ⊢ A
mv₂ = mvar (suc (suc zero))

iᶜ : ∀ {Δ Γ A} →
       Δ ⁏ Γ ⊢ A ⇒ A
iᶜ = lam v₀

kᶜ : ∀ {Δ Γ A B} →
       Δ ⁏ Γ ⊢ A ⇒ B ⇒ A
kᶜ = lam (lam v₁)

sᶜ : ∀ {Δ Γ A B C} →
       Δ ⁏ Γ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
sᶜ = lam (lam (lam
       (app (app v₂ v₀) (app v₁ v₀))))

cᶜ : ∀ {Δ Γ A B C} →
       Δ ⁏ Γ ⊢ (A ⇒ B ⇒ C) ⇒ B ⇒ A ⇒ C
cᶜ = lam (lam (lam
       (app (app v₂ v₀) v₁)))

bᶜ : ∀ {Δ Γ A B C} →
       Δ ⁏ Γ ⊢ (B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
bᶜ = lam (lam (lam
       (app v₂ (app v₁ v₀))))

aᶜ : ∀ {Δ Γ A B} →
       Δ ⁏ Γ ⊢ (A ⇒ A ⇒ B) ⇒ A ⇒ B
aᶜ = lam (lam
       (app (app v₁ v₀) v₀))

dᶜ : ∀ {Δ Γ A B} →
       Δ ⁏ Γ ⊢ □ (A ⇒ B) ⇒ □ A ⇒ □ B
dᶜ = lam (lam (unbox v₁ (unbox v₀
       (box (app mv₁ mv₀)))))

4ᶜ : ∀ {Δ Γ A} →
       Δ ⁏ Γ ⊢ □ A ⇒ □ □ A
4ᶜ = lam (unbox v₀
       (box (box mv₀)))

tᶜ : ∀ {Δ Γ A} →
       Δ ⁏ Γ ⊢ □ A ⇒ A
tᶜ = lam (unbox v₀ mv₀)


-- Example inference rules on derivations.

exch : ∀ {Δ Γ A B C} →
         Δ ⁏ Γ ⊢ A ⇒ B ⇒ C →
         Δ ⁏ Γ ⊢ B ⇒ A ⇒ C
exch 𝒟 = app cᶜ 𝒟

comp : ∀ {Δ Γ A B C} →
         Δ ⁏ Γ ⊢ B ⇒ C → Δ ⁏ Γ ⊢ A ⇒ B →
         Δ ⁏ Γ ⊢ A ⇒ C
comp 𝒟 ℰ = app (app bᶜ 𝒟) ℰ

cont : ∀ {Δ Γ A B} →
         Δ ⁏ Γ ⊢ A ⇒ A ⇒ B →
         Δ ⁏ Γ ⊢ A ⇒ B
cont 𝒟 = app aᶜ 𝒟

mlam : ∀ {A B Γ Δ} →
         Δ , □ A ⁏ Γ ⊢ B →
         Δ ⁏ Γ ⊢ □ A ⇒ B
mlam 𝒟 = lam (unbox v₀ (mono⊢ refl⊇ (weak refl⊇) 𝒟))

det : ∀ {Δ Γ A B} →
        Δ ⁏ Γ ⊢ A ⇒ B →
        Δ ⁏ Γ , A ⊢ B
det 𝒟 = app (mono⊢ refl⊇ (weak refl⊇) 𝒟) v₀

mdet : ∀ {Δ Γ A B} →
         Δ ⁏ Γ ⊢ □ A ⇒ B →
         Δ , □ A ⁏ Γ ⊢ B
mdet 𝒟 = app (mono⊢ (weak refl⊇) refl⊇ 𝒟) (box mv₀)

dist : ∀ {Δ Γ A B} →
         Δ ⁏ Γ ⊢ □ (A ⇒ B) → Δ ⁏ Γ ⊢ □ A →
         Δ ⁏ Γ ⊢ □ B
dist 𝒟 ℰ = app (app dᶜ 𝒟) ℰ

wrap : ∀ {Δ Γ A} →
         Δ ⁏ Γ ⊢ □ A →
         Δ ⁏ Γ ⊢ □ □ A
wrap 𝒟 = app 4ᶜ 𝒟

eval : ∀ {Δ Γ A} →
         Δ ⁏ Γ ⊢ □ A →
         Δ ⁏ Γ ⊢ A
eval 𝒟 = app tᶜ 𝒟
