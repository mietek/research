{-# OPTIONS --rewriting #-}

module IMCMLSyntaxNoTerms where

open import IMCML public
open IMCMLList public


-- TODO: Needs a name.

⌈_⌉ : Ty⋆ → BoxTy⋆
⌈ Ξ ⌉ = map ([ ∅ ]_) Ξ

∋→⌈∋⌉ : ∀ {Ξ A} → Ξ ∋ A → ⌈ Ξ ⌉ ∋ [ ∅ ] A
∋→⌈∋⌉ zero    = zero
∋→⌈∋⌉ (suc 𝒾) = suc (∋→⌈∋⌉ 𝒾)


-- Contexts.

Cx : Set
Cx = Ty⋆ ∧ Ty⋆


-- Derivations.

mutual
  infix 3 _⊢_
  data _⊢_ : Cx → Ty → Set where
    var   : ∀ {Δ Γ A} →
              Γ ∋ A →
              Δ ⁏ Γ ⊢ A
    mvar  : ∀ {Δ Γ A} →
              Δ ∋ A →
              Δ ⁏ Γ ⊢ A
    lam   : ∀ {Δ Γ A B} →
              Δ ⁏ Γ , A ⊢ B →
              Δ ⁏ Γ ⊢ A ⇒ B
    app   : ∀ {Δ Γ A B} →
              Δ ⁏ Γ ⊢ A ⇒ B → Δ ⁏ Γ ⊢ A →
              Δ ⁏ Γ ⊢ B
    box   : ∀ {Δ Γ Φ A} →
              Δ ⟨⊢⟩ [ Φ ] A →
              Δ ⁏ Γ ⊢ [ Φ ] A
    unbox : ∀ {Δ Γ Φ A C} →
              Δ ⟨⊢⟩⋆ ⌈ Φ ⌉ → Δ ⁏ Γ ⊢ [ Φ ] A → Δ , A ⁏ Γ ⊢ C →
              Δ ⁏ Γ ⊢ C

  infix 3 _⟨⊢⟩_
  _⟨⊢⟩_ : Ty⋆ → BoxTy → Set
  Δ ⟨⊢⟩ [ Φ ] A = Δ ⧺ Φ ⁏ ∅ ⊢ A

  infix 3 _⟨⊢⟩⋆_
  _⟨⊢⟩⋆_ : Ty⋆ → BoxTy⋆ → Set
  Δ ⟨⊢⟩⋆ Ξ = All (Δ ⟨⊢⟩_) Ξ

mutual
  mono⊢ : ∀ {Δ Γ Δ′ Γ′ A} → Δ′ ⊇ Δ → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ A → Δ′ ⁏ Γ′ ⊢ A
  mono⊢ ζ η (var 𝒾)         = var (mono∋ η 𝒾)
  mono⊢ ζ η (mvar 𝒾)        = mvar (mono∋ ζ 𝒾)
  mono⊢ ζ η (lam 𝒟)         = lam (mono⊢ ζ (lift η) 𝒟)
  mono⊢ ζ η (app 𝒟 ℰ)       = app (mono⊢ ζ η 𝒟) (mono⊢ ζ η ℰ)
  mono⊢ ζ η (box {Φ = Φ} 𝒟) = box (mono⟨⊢⟩ {Φ} ζ 𝒟)
  mono⊢ ζ η (unbox φ 𝒟 ℰ)   = unbox (mono⟨⊢⟩⋆ ζ φ) (mono⊢ ζ η 𝒟) (mono⊢ (lift ζ) η ℰ)

  mono⟨⊢⟩ : ∀ {Φ Δ Δ′ A} → Δ′ ⊇ Δ → Δ ⟨⊢⟩ [ Φ ] A → Δ′ ⟨⊢⟩ [ Φ ] A
  mono⟨⊢⟩ {Φ} ζ 𝒟 = mono⊢ (lift⊇⧺ ζ Φ) refl⊇ 𝒟

  mono⟨⊢⟩⋆ : ∀ {Ξ Δ Δ′} → Δ′ ⊇ Δ → Δ ⟨⊢⟩⋆ Ξ → Δ′ ⟨⊢⟩⋆ Ξ
  mono⟨⊢⟩⋆ {∅}           ζ ∅       = ∅
  mono⟨⊢⟩⋆ {Ξ , [ Φ ] A} ζ (ξ , 𝒟) = mono⟨⊢⟩⋆ ζ ξ , mono⟨⊢⟩ {Φ} ζ 𝒟
  -- NOTE: Equivalent, but does not pass termination check.
  -- mono⟨⊢⟩⋆ ζ ξ = mapAll (λ { {[ Φ ] A} → mono⟨⊢⟩ {Φ} ζ }) ξ

mutual
  idmono⊢ : ∀ {Δ Γ A} → (𝒟 : Δ ⁏ Γ ⊢ A) → mono⊢ refl⊇ refl⊇ 𝒟 ≡ 𝒟
  idmono⊢ (var 𝒾)         = cong var (idmono∋ 𝒾)
  idmono⊢ (mvar 𝒾)        = cong mvar (idmono∋ 𝒾)
  idmono⊢ (lam 𝒟)         = cong lam (idmono⊢ 𝒟)
  idmono⊢ (app 𝒟 ℰ)       = cong² app (idmono⊢ 𝒟) (idmono⊢ ℰ)
  idmono⊢ (box {Φ = Φ} 𝒟) = cong box (idmono⟨⊢⟩ {Φ} 𝒟)
  idmono⊢ (unbox φ 𝒟 ℰ)   = cong³ unbox (idmono⟨⊢⟩⋆ φ) (idmono⊢ 𝒟) (idmono⊢ ℰ)

  idmono⟨⊢⟩ : ∀ {Φ Δ A} → (𝒟 : Δ ⟨⊢⟩ [ Φ ] A) → mono⟨⊢⟩ {Φ} refl⊇ 𝒟 ≡ 𝒟
  idmono⟨⊢⟩ 𝒟 = idmono⊢ 𝒟

  idmono⟨⊢⟩⋆ : ∀ {Ξ Δ} → (ξ : Δ ⟨⊢⟩⋆ Ξ) → mono⟨⊢⟩⋆ refl⊇ ξ ≡ ξ
  idmono⟨⊢⟩⋆ {∅}           ∅       = refl
  idmono⟨⊢⟩⋆ {Ξ , [ Φ ] A} (ξ , 𝒟) = cong² _,_ (idmono⟨⊢⟩⋆ ξ) (idmono⟨⊢⟩ {Φ} 𝒟)

mutual
  assocmono⊢ : ∀ {Δ Γ Δ′ Γ′ Δ″ Γ″ A} →
                  (ζ′ : Δ″ ⊇ Δ′) (η′ : Γ″ ⊇ Γ′) (ζ : Δ′ ⊇ Δ) (η : Γ′ ⊇ Γ) (𝒟 : Δ ⁏ Γ ⊢ A) →
                  mono⊢ ζ′ η′ (mono⊢ ζ η 𝒟) ≡ mono⊢ (trans⊇ ζ′ ζ) (trans⊇ η′ η) 𝒟
  assocmono⊢ ζ′ η′ ζ η (var 𝒾)         = cong var (assocmono∋ η′ η 𝒾)
  assocmono⊢ ζ′ η′ ζ η (mvar 𝒾)        = cong mvar (assocmono∋ ζ′ ζ 𝒾)
  assocmono⊢ ζ′ η′ ζ η (lam 𝒟)         = cong lam (assocmono⊢ ζ′ (lift η′) ζ (lift η) 𝒟)
  assocmono⊢ ζ′ η′ ζ η (app 𝒟 ℰ)       = cong² app (assocmono⊢ ζ′ η′ ζ η 𝒟) (assocmono⊢ ζ′ η′ ζ η ℰ)
  assocmono⊢ ζ′ η′ ζ η (box {Φ = Φ} 𝒟) = cong box (assocmono⟨⊢⟩ {Φ} ζ′ ζ 𝒟)
  assocmono⊢ ζ′ η′ ζ η (unbox φ 𝒟 ℰ)   = cong³ unbox (assocmono⟨⊢⟩⋆ ζ′ ζ φ) (assocmono⊢ ζ′ η′ ζ η 𝒟) (assocmono⊢ (lift ζ′) η′ (lift ζ) η ℰ)

  assocmono⟨⊢⟩ : ∀ {Φ Δ Δ′ Δ″ A} →
                    (ζ′ : Δ″ ⊇ Δ′) (ζ : Δ′ ⊇ Δ) (𝒟 : Δ ⟨⊢⟩ [ Φ ] A) →
                    mono⟨⊢⟩ {Φ} ζ′ (mono⟨⊢⟩ {Φ} ζ 𝒟) ≡ mono⟨⊢⟩ {Φ} (trans⊇ ζ′ ζ) 𝒟
  assocmono⟨⊢⟩ {Φ} ζ′ ζ 𝒟 = assocmono⊢ (lift⊇⧺ ζ′ Φ) refl⊇ (lift⊇⧺ ζ Φ) refl⊇ 𝒟

  assocmono⟨⊢⟩⋆ : ∀ {Ξ Δ Δ′ Δ″} →
                   (ζ′ : Δ″ ⊇ Δ′) (ζ : Δ′ ⊇ Δ) (ξ : Δ ⟨⊢⟩⋆ Ξ) →
                   mono⟨⊢⟩⋆ ζ′ (mono⟨⊢⟩⋆ ζ ξ) ≡ mono⟨⊢⟩⋆ (trans⊇ ζ′ ζ) ξ
  assocmono⟨⊢⟩⋆ {∅} ζ′        ζ ∅       = refl
  assocmono⟨⊢⟩⋆ {Ξ , [ Φ ] A} ζ′ ζ (ξ , 𝒟) = cong² _,_ (assocmono⟨⊢⟩⋆ ζ′ ζ ξ) (assocmono⟨⊢⟩ {Φ} ζ′ ζ 𝒟)


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
graft⊢ ψ (var 𝒾)       = lookup⊢ ψ 𝒾
graft⊢ ψ (mvar 𝒾)      = mvar 𝒾
graft⊢ ψ (lam 𝒟)       = lam (graft⊢ (mono⊢⋆ refl⊇ (weak refl⊇) ψ , var zero) 𝒟)
graft⊢ ψ (app 𝒟 ℰ)     = app (graft⊢ ψ 𝒟) (graft⊢ ψ ℰ)
graft⊢ ψ (box 𝒟)       = box 𝒟
graft⊢ ψ (unbox φ 𝒟 ℰ) = unbox φ (graft⊢ ψ 𝒟) (graft⊢ (mono⊢⋆ (weak refl⊇) refl⊇ ψ) ℰ)

graft⊢⋆ : ∀ {Δ Γ Ψ Ξ} → Δ ⁏ Γ ⊢⋆ Ψ → Δ ⁏ Ψ ⊢⋆ Ξ → Δ ⁏ Γ ⊢⋆ Ξ
graft⊢⋆ ψ ∅       = ∅
graft⊢⋆ ψ (ξ , 𝒟) = graft⊢⋆ ψ ξ , graft⊢ ψ 𝒟

trans⊢⋆ : ∀ {Δ Γ Γ′ Γ″} → Δ ⁏ Γ″ ⊢⋆ Γ′ → Δ ⁏ Γ′ ⊢⋆ Γ → Δ ⁏ Γ″ ⊢⋆ Γ
trans⊢⋆ γ′ γ = graft⊢⋆ γ′ γ


-- TODO: Needs a name.

concat⟨⊢⟩⋆ : ∀ {`Φ `Ξ Φ Ξ} → Ξ ⟨⊢⟩⋆ ⌈ Φ ⌉ → `Ξ ⟨⊢⟩⋆ ⌈ `Φ ⌉ → Ξ ⧺ `Ξ ⟨⊢⟩⋆ ⌈ Φ ⧺ `Φ ⌉
concat⟨⊢⟩⋆ {∅}       {`Ξ} {Φ} {Ξ} φ ∅         = mono⟨⊢⟩⋆ (weak⊇⧺ refl⊇ `Ξ) φ
concat⟨⊢⟩⋆ {`Φ , `A} {`Ξ} {Φ} {Ξ} φ (`φ , `𝒟) = concat⟨⊢⟩⋆ φ `φ , mono⟨⊢⟩ {∅} (weak⊇⧺₁ `Ξ) `𝒟

mrefl⟨⊢⟩⋆ : ∀ {Δ} → Δ ⟨⊢⟩⋆ ⌈ Δ ⌉
mrefl⟨⊢⟩⋆ {∅}     = ∅
mrefl⟨⊢⟩⋆ {Δ , A} = mono⟨⊢⟩⋆ (weak refl⊇) mrefl⟨⊢⟩⋆ , mvar zero

mlookup⟨⊢⟩ : ∀ {Δ Ξ Φ A} → Δ ⟨⊢⟩⋆ Ξ → Ξ ∋ [ Φ ] A → Δ ⟨⊢⟩ [ Φ ] A
mlookup⟨⊢⟩ ξ 𝒾 = lookupAll ξ 𝒾

mutual
  mgraft⊢ : ∀ {Δ Γ Φ A} → Δ ⟨⊢⟩⋆ ⌈ Φ ⌉ → Φ ⁏ Γ ⊢ A → Δ ⁏ Γ ⊢ A
  mgraft⊢ φ (var 𝒾)          = var 𝒾
  mgraft⊢ φ (mvar 𝒾)         = graft⊢ ∅ (mlookup⟨⊢⟩ φ (∋→⌈∋⌉ 𝒾))
  mgraft⊢ φ (lam 𝒟)          = lam (mgraft⊢ φ 𝒟)
  mgraft⊢ φ (app 𝒟 ℰ)        = app (mgraft⊢ φ 𝒟) (mgraft⊢ φ ℰ)
  mgraft⊢ φ (box {Φ = `Φ} 𝒟) = box (mgraft⟨⊢⟩ {`Φ} φ 𝒟)
  mgraft⊢ φ (unbox `φ 𝒟 ℰ)   = unbox (mgraft⟨⊢⟩⋆ φ `φ) (mgraft⊢ φ 𝒟) (mgraft⊢ (mono⟨⊢⟩⋆ (weak refl⊇) φ , mvar zero) ℰ)

  mgraft⟨⊢⟩ : ∀ {`Φ Φ Δ A} → Δ ⟨⊢⟩⋆ ⌈ Φ ⌉ → Φ ⟨⊢⟩ [ `Φ ] A → Δ ⟨⊢⟩ [ `Φ ] A
  mgraft⟨⊢⟩ {`Φ} φ 𝒟 = mgraft⊢ (concat⟨⊢⟩⋆ {`Φ} φ mrefl⟨⊢⟩⋆) 𝒟

  mgraft⟨⊢⟩⋆ : ∀ {Ξ Δ Φ} → Δ ⟨⊢⟩⋆ ⌈ Φ ⌉ → Φ ⟨⊢⟩⋆ Ξ → Δ ⟨⊢⟩⋆ Ξ
  mgraft⟨⊢⟩⋆ {∅}            φ ∅       = ∅
  mgraft⟨⊢⟩⋆ {Ξ , [ `Φ ] A} φ (ξ , 𝒟) = mgraft⟨⊢⟩⋆ φ ξ , mgraft⟨⊢⟩ {`Φ} φ 𝒟
  -- NOTE: Equivalent, but does not pass termination check.
  -- mgraft⟨⊢⟩⋆ φ ξ = mapAll (mgraft⟨⊢⟩ φ) ξ

mgraft⊢⋆ : ∀ {Δ Γ Φ Ξ} → Δ ⟨⊢⟩⋆ ⌈ Φ ⌉ → Φ ⁏ Γ ⊢⋆ Ξ → Δ ⁏ Γ ⊢⋆ Ξ
mgraft⊢⋆ φ ξ = mapAll (mgraft⊢ φ) ξ

mtrans⟨⊢⟩⋆ : ∀ {Δ Δ′ Δ″} → Δ″ ⟨⊢⟩⋆ ⌈ Δ′ ⌉ → Δ′ ⟨⊢⟩⋆ Δ → Δ″ ⟨⊢⟩⋆ Δ
mtrans⟨⊢⟩⋆ δ′ δ = mgraft⟨⊢⟩⋆ δ′ δ


-- Normal forms.

mutual
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ : Cx → Ty → Set where
    lamⁿᶠ   : ∀ {Δ Γ A B} →
                Δ ⁏ Γ , A ⊢ⁿᶠ B →
                Δ ⁏ Γ ⊢ⁿᶠ A ⇒ B
    boxⁿᶠ   : ∀ {Δ Γ Φ A} →
                Δ ⟨⊢⟩ [ Φ ] A →
                Δ ⁏ Γ ⊢ⁿᶠ [ Φ ] A
    neⁿᶠ    : ∀ {Δ Γ A} →
                Δ ⁏ Γ ⊢ⁿᵉ A →
                Δ ⁏ Γ ⊢ⁿᶠ A

  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ : Cx → Ty → Set where
    varⁿᵉ   : ∀ {Δ Γ A} →
                Γ ∋ A →
                Δ ⁏ Γ ⊢ⁿᵉ A
    mvarⁿᵉ  : ∀ {Δ Γ A} →
                Δ ∋ A →
                Δ ⁏ Γ ⊢ⁿᵉ A
    appⁿᵉ   : ∀ {Δ Γ A B} →
                Δ ⁏ Γ ⊢ⁿᵉ A ⇒ B → Δ ⁏ Γ ⊢ⁿᶠ A →
                Δ ⁏ Γ ⊢ⁿᵉ B
    unboxⁿᵉ : ∀ {Δ Γ Φ A C} →
                Δ ⟨⊢⟩⋆ⁿᶠ ⌈ Φ ⌉ → Δ ⁏ Γ ⊢ⁿᵉ [ Φ ] A → Δ , [ Φ ] A ⁏ Γ ⊢ⁿᶠ C →
                Δ ⁏ Γ ⊢ⁿᵉ C

  infix 3 _⟨⊢⟩ⁿᶠ_
  _⟨⊢⟩ⁿᶠ_ : Ty⋆ → BoxTy → Set
  Δ ⟨⊢⟩ⁿᶠ [ Φ ] A = Δ ⧺ Φ ⁏ ∅ ⊢ⁿᶠ A

  infix 3 _⟨⊢⟩⋆ⁿᶠ_
  _⟨⊢⟩⋆ⁿᶠ_ : Ty⋆ → BoxTy⋆ → Set
  Δ ⟨⊢⟩⋆ⁿᶠ Ξ = All (Δ ⟨⊢⟩ⁿᶠ_) Ξ

mutual
  mono⊢ⁿᶠ : ∀ {Δ Γ Δ′ Γ′ A} → Δ′ ⊇ Δ → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ⁿᶠ A → Δ′ ⁏ Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ ζ η (lamⁿᶠ 𝒟)         = lamⁿᶠ (mono⊢ⁿᶠ ζ (lift η) 𝒟)
  mono⊢ⁿᶠ ζ η (boxⁿᶠ {Φ = Φ} 𝒟) = boxⁿᶠ (mono⟨⊢⟩ {Φ} ζ 𝒟)
  mono⊢ⁿᶠ ζ η (neⁿᶠ 𝒟)          = neⁿᶠ (mono⊢ⁿᵉ ζ η 𝒟)

  mono⊢ⁿᵉ : ∀ {Δ Γ Δ′ Γ′ A} → Δ′ ⊇ Δ → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ⁿᵉ A → Δ′ ⁏ Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ ζ η (varⁿᵉ 𝒾)         = varⁿᵉ (mono∋ η 𝒾)
  mono⊢ⁿᵉ ζ η (mvarⁿᵉ 𝒾)        = mvarⁿᵉ (mono∋ ζ 𝒾)
  mono⊢ⁿᵉ ζ η (appⁿᵉ 𝒟 ℰ)       = appⁿᵉ (mono⊢ⁿᵉ ζ η 𝒟) (mono⊢ⁿᶠ ζ η ℰ)
  mono⊢ⁿᵉ ζ η (unboxⁿᵉ φ 𝒟 ℰ)   = unboxⁿᵉ (mono⟨⊢⟩⋆ⁿᶠ ζ φ) (mono⊢ⁿᵉ ζ η 𝒟) (mono⊢ⁿᶠ (lift ζ) η ℰ)

  mono⟨⊢⟩ⁿᶠ : ∀ {Φ Δ Δ′ A} → Δ′ ⊇ Δ → Δ ⟨⊢⟩ⁿᶠ [ Φ ] A → Δ′ ⟨⊢⟩ⁿᶠ [ Φ ] A
  mono⟨⊢⟩ⁿᶠ {Φ} ζ 𝒟 = mono⊢ⁿᶠ (lift⊇⧺ ζ Φ) refl⊇ 𝒟

  mono⟨⊢⟩⋆ⁿᶠ : ∀ {Ξ Δ Δ′} → Δ′ ⊇ Δ → Δ ⟨⊢⟩⋆ⁿᶠ Ξ → Δ′ ⟨⊢⟩⋆ⁿᶠ Ξ
  mono⟨⊢⟩⋆ⁿᶠ {∅}           ζ ∅       = ∅
  mono⟨⊢⟩⋆ⁿᶠ {Ξ , [ Φ ] A} ζ (ξ , 𝒟) = mono⟨⊢⟩⋆ⁿᶠ ζ ξ , mono⟨⊢⟩ⁿᶠ {Φ} ζ 𝒟
  -- NOTE: Equivalent, but does not pass termination check.
  -- mono⟨⊢⟩⋆ⁿᶠ ζ η ξ = mapAll (mono⊢ⁿᶠ ζ η) ξ

mutual
  idmono⊢ⁿᶠ : ∀ {Δ Γ A} → (𝒟 : Δ ⁏ Γ ⊢ⁿᶠ A) → mono⊢ⁿᶠ refl⊇ refl⊇ 𝒟 ≡ 𝒟
  idmono⊢ⁿᶠ (lamⁿᶠ 𝒟)         = cong lamⁿᶠ (idmono⊢ⁿᶠ 𝒟)
  idmono⊢ⁿᶠ (boxⁿᶠ {Φ = Φ} 𝒟) = cong boxⁿᶠ (idmono⟨⊢⟩ {Φ} 𝒟)
  idmono⊢ⁿᶠ (neⁿᶠ 𝒟)          = cong neⁿᶠ (idmono⊢ⁿᵉ 𝒟)

  idmono⊢ⁿᵉ : ∀ {Δ Γ A} → (𝒟 : Δ ⁏ Γ ⊢ⁿᵉ A) → mono⊢ⁿᵉ refl⊇ refl⊇ 𝒟 ≡ 𝒟
  idmono⊢ⁿᵉ (varⁿᵉ 𝒾)         = cong varⁿᵉ (idmono∋ 𝒾)
  idmono⊢ⁿᵉ (mvarⁿᵉ 𝒾)        = cong mvarⁿᵉ (idmono∋ 𝒾)
  idmono⊢ⁿᵉ (appⁿᵉ 𝒟 ℰ)       = cong² appⁿᵉ (idmono⊢ⁿᵉ 𝒟) (idmono⊢ⁿᶠ ℰ)
  idmono⊢ⁿᵉ (unboxⁿᵉ φ 𝒟 ℰ)   = cong³ unboxⁿᵉ (idmono⟨⊢⟩⋆ⁿᶠ φ) (idmono⊢ⁿᵉ 𝒟) (idmono⊢ⁿᶠ ℰ)

  idmono⟨⊢⟩ⁿᶠ : ∀ {Φ Δ A} → (𝒟 : Δ ⟨⊢⟩ⁿᶠ [ Φ ] A) → mono⟨⊢⟩ⁿᶠ {Φ} refl⊇ 𝒟 ≡ 𝒟
  idmono⟨⊢⟩ⁿᶠ 𝒟 = idmono⊢ⁿᶠ 𝒟

  idmono⟨⊢⟩⋆ⁿᶠ : ∀ {Ξ Δ} → (ξ : Δ ⟨⊢⟩⋆ⁿᶠ Ξ) → mono⟨⊢⟩⋆ⁿᶠ refl⊇ ξ ≡ ξ
  idmono⟨⊢⟩⋆ⁿᶠ {∅}           ∅       = refl
  idmono⟨⊢⟩⋆ⁿᶠ {Ξ , [ Φ ] A} (ξ , 𝒟) = cong² _,_ (idmono⟨⊢⟩⋆ⁿᶠ ξ) (idmono⟨⊢⟩ⁿᶠ {Φ} 𝒟)

mutual
  assocmono⊢ⁿᶠ : ∀ {Δ Γ Δ′ Γ′ Γ″ Δ″ A} →
                    (ζ′ : Δ″ ⊇ Δ′) (η′ : Γ″ ⊇ Γ′) (ζ : Δ′ ⊇ Δ) (η : Γ′ ⊇ Γ) (𝒟 : Δ ⁏ Γ ⊢ⁿᶠ A) →
                    mono⊢ⁿᶠ ζ′ η′ (mono⊢ⁿᶠ ζ η 𝒟) ≡ mono⊢ⁿᶠ (trans⊇ ζ′ ζ) (trans⊇ η′ η) 𝒟
  assocmono⊢ⁿᶠ ζ′ η′ ζ η (lamⁿᶠ 𝒟)         = cong lamⁿᶠ (assocmono⊢ⁿᶠ ζ′ (lift η′) ζ (lift η) 𝒟)
  assocmono⊢ⁿᶠ ζ′ η′ ζ η (boxⁿᶠ {Φ = Φ} 𝒟) = cong boxⁿᶠ (assocmono⟨⊢⟩ {Φ} ζ′ ζ 𝒟)
  assocmono⊢ⁿᶠ ζ′ η′ ζ η (neⁿᶠ 𝒟)          = cong neⁿᶠ (assocmono⊢ⁿᵉ ζ′ η′ ζ η 𝒟)

  assocmono⊢ⁿᵉ : ∀ {Δ Γ Δ′ Γ′ Γ″ Δ″ A} →
                    (ζ′ : Δ″ ⊇ Δ′) (η′ : Γ″ ⊇ Γ′) (ζ : Δ′ ⊇ Δ) (η : Γ′ ⊇ Γ) (𝒟 : Δ ⁏ Γ ⊢ⁿᵉ A) →
                    mono⊢ⁿᵉ ζ′ η′ (mono⊢ⁿᵉ ζ η 𝒟) ≡ mono⊢ⁿᵉ (trans⊇ ζ′ ζ) (trans⊇ η′ η) 𝒟
  assocmono⊢ⁿᵉ ζ′ η′ ζ η (varⁿᵉ 𝒾)         = cong varⁿᵉ (assocmono∋ η′ η 𝒾)
  assocmono⊢ⁿᵉ ζ′ η′ ζ η (mvarⁿᵉ 𝒾)        = cong mvarⁿᵉ (assocmono∋ ζ′ ζ 𝒾)
  assocmono⊢ⁿᵉ ζ′ η′ ζ η (appⁿᵉ 𝒟 ℰ)       = cong² appⁿᵉ (assocmono⊢ⁿᵉ ζ′ η′ ζ η 𝒟) (assocmono⊢ⁿᶠ ζ′ η′ ζ η ℰ)
  assocmono⊢ⁿᵉ ζ′ η′ ζ η (unboxⁿᵉ φ 𝒟 ℰ)   = cong³ unboxⁿᵉ (assocmono⟨⊢⟩⋆ⁿᶠ ζ′ ζ φ) (assocmono⊢ⁿᵉ ζ′ η′ ζ η 𝒟) (assocmono⊢ⁿᶠ (lift ζ′) η′ (lift ζ) η ℰ)

  assocmono⟨⊢⟩ⁿᶠ : ∀ {Φ Δ Δ′ Δ″ A} →
                      (ζ′ : Δ″ ⊇ Δ′) (ζ : Δ′ ⊇ Δ) (𝒟 : Δ ⟨⊢⟩ⁿᶠ [ Φ ] A) →
                      mono⟨⊢⟩ⁿᶠ {Φ} ζ′ (mono⟨⊢⟩ⁿᶠ {Φ} ζ 𝒟) ≡ mono⟨⊢⟩ⁿᶠ {Φ} (trans⊇ ζ′ ζ) 𝒟
  assocmono⟨⊢⟩ⁿᶠ {Φ} ζ′ ζ 𝒟 = assocmono⊢ⁿᶠ (lift⊇⧺ ζ′ Φ) refl⊇ (lift⊇⧺ ζ Φ) refl⊇ 𝒟

  assocmono⟨⊢⟩⋆ⁿᶠ : ∀ {Ξ Δ Δ′ Δ″} →
                       (ζ′ : Δ″ ⊇ Δ′) (ζ : Δ′ ⊇ Δ) (ξ : Δ ⟨⊢⟩⋆ⁿᶠ Ξ) →
                       mono⟨⊢⟩⋆ⁿᶠ ζ′ (mono⟨⊢⟩⋆ⁿᶠ ζ ξ) ≡ mono⟨⊢⟩⋆ⁿᶠ (trans⊇ ζ′ ζ) ξ
  assocmono⟨⊢⟩⋆ⁿᶠ {∅}           ζ′ ζ ∅       = refl
  assocmono⟨⊢⟩⋆ⁿᶠ {Ξ , [ Φ ] A} ζ′ ζ (ξ , 𝒟) = cong² _,_ (assocmono⟨⊢⟩⋆ⁿᶠ ζ′ ζ ξ) (assocmono⟨⊢⟩ⁿᶠ {Φ} ζ′ ζ 𝒟)


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
        Δ , A ⁏ Γ ⊢ A
mv₀ = mvar zero

mv₁ : ∀ {Δ Γ A B} →
        Δ , A , B ⁏ Γ ⊢ A
mv₁ = mvar (suc zero)

mv₂ : ∀ {Δ Γ A B C} →
        Δ , A , B , C ⁏ Γ ⊢ A
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
       Δ ⁏ Γ ⊢ [ ∅ ] (A ⇒ B) ⇒ [ ∅ ] A ⇒ [ ∅ ] B
dᶜ = lam (lam (unbox ∅ v₁ (unbox ∅ v₀
       (box (app mv₁ mv₀)))))

4ᶜ : ∀ {Δ Γ A} →
       Δ ⁏ Γ ⊢ [ ∅ ] A ⇒ [ ∅ ] [ ∅ ] A
4ᶜ = lam (unbox ∅ v₀
       (box (box mv₀)))

tᶜ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ [ ∅ ] A ⇒ A
tᶜ = lam (unbox ∅ v₀ mv₀)


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
         Δ , A ⁏ Γ ⊢ B →
         Δ ⁏ Γ ⊢ [ ∅ ] A ⇒ B
mlam 𝒟 = lam (unbox ∅ v₀ (mono⊢ refl⊇ (weak refl⊇) 𝒟))

det : ∀ {Δ Γ A B} →
        Δ ⁏ Γ ⊢ A ⇒ B →
        Δ ⁏ Γ , A ⊢ B
det 𝒟 = app (mono⊢ refl⊇ (weak refl⊇) 𝒟) v₀

mdet : ∀ {Δ Γ A B} →
         Δ ⁏ Γ ⊢ [ ∅ ] A ⇒ B →
         Δ , A ⁏ Γ ⊢ B
mdet 𝒟 = app (mono⊢ (weak refl⊇) refl⊇ 𝒟) (box mv₀)

dist : ∀ {Δ Γ A B} →
         Δ ⁏ Γ ⊢ [ ∅ ] (A ⇒ B) → Δ ⁏ Γ ⊢ [ ∅ ] A →
         Δ ⁏ Γ ⊢ [ ∅ ] B
dist 𝒟 ℰ = app (app dᶜ 𝒟) ℰ

wrap : ∀ {Δ Γ A} →
         Δ ⁏ Γ ⊢ [ ∅ ] A →
         Δ ⁏ Γ ⊢ [ ∅ ] [ ∅ ] A
wrap 𝒟 = app 4ᶜ 𝒟

eval : ∀ {Δ Γ A} →
         Δ ⁏ Γ ⊢ [ ∅ ] A →
         Δ ⁏ Γ ⊢ A
eval 𝒟 = app tᶜ 𝒟
