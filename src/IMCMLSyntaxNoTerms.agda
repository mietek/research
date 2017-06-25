{-# OPTIONS --rewriting #-}

module IMCMLSyntaxNoTerms where

open import IMCML public
open IMCMLList public


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
    mvar  : ∀ {Δ Γ Φ A} →
              Δ ⁏ ∅ ⊢⧆ Φ → Δ ∋ [ Φ ] A →
              Δ ⁏ Γ ⊢ A
    lam   : ∀ {Δ Γ A B} →
              Δ ⁏ Γ , A ⊢ B →
              Δ ⁏ Γ ⊢ A ⇒ B
    app   : ∀ {Δ Γ A B} →
              Δ ⁏ Γ ⊢ A ⇒ B → Δ ⁏ Γ ⊢ A →
              Δ ⁏ Γ ⊢ B
    box   : ∀ {Δ Γ Φ A} →
              Φ ⁏ ∅ ⊢ A →
              Δ ⁏ Γ ⊢ [ Φ ] A
    unbox : ∀ {Δ Γ Φ A C} →
              Δ ⁏ Γ ⊢ [ Φ ] A → Δ , [ Φ ] A ⁏ Γ ⊢ C →
              Δ ⁏ Γ ⊢ C

  infix 3 _⊢⧆_
  data _⊢⧆_ : Cx → BoxTy⋆ → Set where
    ∅   : ∀ {Δ Γ}       → Δ ⁏ Γ ⊢⧆ ∅
    _,_ : ∀ {Δ Γ Φ Ξ A} →
            Δ ⁏ Γ ⊢⧆ Ξ → Δ ⁏ Γ ⊢ [ Φ ] A →
            Δ ⁏ Γ ⊢⧆ Ξ , [ Φ ] A

infix 3 _⊢⋆_
_⊢⋆_ : Cx → Ty⋆ → Set
Δ ⁏ Γ ⊢⋆ Ξ = All (Δ ⁏ Γ ⊢_) Ξ

mutual
  mono⊢ : ∀ {Δ Γ Δ′ Γ′ A} → Δ′ ⊇ Δ → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ A → Δ′ ⁏ Γ′ ⊢ A
  mono⊢ ζ η (var 𝒾)     = var (mono∋ η 𝒾)
  mono⊢ ζ η (mvar φ 𝒾)  = mvar (mono⊢⧆ ζ done φ) (mono∋ ζ 𝒾)
  mono⊢ ζ η (lam 𝒟)     = lam (mono⊢ ζ (lift η) 𝒟)
  mono⊢ ζ η (app 𝒟 ℰ)   = app (mono⊢ ζ η 𝒟) (mono⊢ ζ η ℰ)
  mono⊢ ζ η (box 𝒟)     = box 𝒟
  mono⊢ ζ η (unbox 𝒟 ℰ) = unbox (mono⊢ ζ η 𝒟) (mono⊢ (lift ζ) η ℰ)

  mono⊢⧆ : ∀ {Δ Γ Δ′ Γ′ Ξ} → Δ′ ⊇ Δ → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢⧆ Ξ → Δ′ ⁏ Γ′ ⊢⧆ Ξ
  mono⊢⧆ ζ η ∅       = ∅
  mono⊢⧆ ζ η (ξ , 𝒟) = mono⊢⧆ ζ η ξ , mono⊢ ζ η 𝒟

mono⊢⋆ : ∀ {Δ Γ Δ′ Γ′ Ξ} → Δ′ ⊇ Δ → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢⋆ Ξ → Δ′ ⁏ Γ′ ⊢⋆ Ξ
mono⊢⋆ ζ η ∅       = ∅
mono⊢⋆ ζ η (ξ , 𝒟) = mono⊢⋆ ζ η ξ , mono⊢ ζ η 𝒟
-- NOTE: Equivalent, but does not pass termination check.
-- mono⊢⋆ ζ η ξ = mapAll (mono⊢ ζ η) ξ

mutual
  idmono⊢ : ∀ {Δ Γ A} → (𝒟 : Δ ⁏ Γ ⊢ A) → mono⊢ refl⊇ refl⊇ 𝒟 ≡ 𝒟
  idmono⊢ (var 𝒾)     = cong var (idmono∋ 𝒾)
  idmono⊢ (mvar φ 𝒾)  = cong² mvar (idmono⊢⧆ φ) (idmono∋ 𝒾)
  idmono⊢ (lam 𝒟)     = cong lam (idmono⊢ 𝒟)
  idmono⊢ (app 𝒟 ℰ)   = cong² app (idmono⊢ 𝒟) (idmono⊢ ℰ)
  idmono⊢ (box 𝒟)     = refl
  idmono⊢ (unbox 𝒟 ℰ) = cong² unbox (idmono⊢ 𝒟) (idmono⊢ ℰ)

  idmono⊢⧆ : ∀ {Δ Γ Ξ} → (ξ : Δ ⁏ Γ ⊢⧆ Ξ) → mono⊢⧆ refl⊇ refl⊇ ξ ≡ ξ
  idmono⊢⧆ ∅       = refl
  idmono⊢⧆ (ξ , 𝒟) = cong² _,_ (idmono⊢⧆ ξ) (idmono⊢ 𝒟)

-- NOTE: Needs {-# REWRITE idtrans⊇₁ #-}.
mutual
  assocmono⊢ : ∀ {Δ Γ Δ′ Γ′ Γ″ Δ″ A} →
                  (ζ′ : Δ″ ⊇ Δ′) (η′ : Γ″ ⊇ Γ′) (ζ : Δ′ ⊇ Δ) (η : Γ′ ⊇ Γ) (𝒟 : Δ ⁏ Γ ⊢ A) →
                  mono⊢ ζ′ η′ (mono⊢ ζ η 𝒟) ≡ mono⊢ (trans⊇ ζ′ ζ) (trans⊇ η′ η) 𝒟
  assocmono⊢ ζ′ η′ ζ η (var 𝒾)     = cong var (assocmono∋ η′ η 𝒾)
  assocmono⊢ ζ′ η′ ζ η (mvar φ 𝒾)  = cong² mvar (assocmono⊢⧆ ζ′ done ζ done φ) (assocmono∋ ζ′ ζ 𝒾)
  assocmono⊢ ζ′ η′ ζ η (lam 𝒟)     = cong lam (assocmono⊢ ζ′ (lift η′) ζ (lift η) 𝒟)
  assocmono⊢ ζ′ η′ ζ η (app 𝒟 ℰ)   = cong² app (assocmono⊢ ζ′ η′ ζ η 𝒟) (assocmono⊢ ζ′ η′ ζ η ℰ)
  assocmono⊢ ζ′ η′ ζ η (box 𝒟)     = refl
  assocmono⊢ ζ′ η′ ζ η (unbox 𝒟 ℰ) = cong² unbox (assocmono⊢ ζ′ η′ ζ η 𝒟) (assocmono⊢ (lift ζ′) η′ (lift ζ) η ℰ)

  assocmono⊢⧆ : ∀ {Δ Γ Δ′ Γ′ Γ″ Δ″ Ξ} →
                   (ζ′ : Δ″ ⊇ Δ′) (η′ : Γ″ ⊇ Γ′) (ζ : Δ′ ⊇ Δ) (η : Γ′ ⊇ Γ) (ξ : Δ ⁏ Γ ⊢⧆ Ξ) →
                   mono⊢⧆ ζ′ η′ (mono⊢⧆ ζ η ξ) ≡ mono⊢⧆ (trans⊇ ζ′ ζ) (trans⊇ η′ η) ξ
  assocmono⊢⧆ ζ′ η′ ζ η ∅       = refl
  assocmono⊢⧆ ζ′ η′ ζ η (ξ , 𝒟) = cong² _,_ (assocmono⊢⧆ ζ′ η′ ζ η ξ) (assocmono⊢ ζ′ η′ ζ η 𝒟)

refl⊢⋆ : ∀ {Δ Γ} → Δ ⁏ Γ ⊢⋆ Γ
refl⊢⋆ {Γ = ∅}     = ∅
refl⊢⋆ {Γ = Γ , A} = mono⊢⋆ refl⊇ (weak refl⊇) refl⊢⋆ , var zero

-- TODO: Should Telescopic Δ always be required?
Telescopic : BoxTy⋆ → Set
Telescopic ∅             = ⊤
Telescopic (Δ , [ Φ ] A) = Telescopic Δ ∧ Δ ⁏ ∅ ⊢⧆ Φ

-- -- TODO: How did this go wrong?
-- postulate
--   oops : ∀ {Δ Γ Φ A} → Δ , [ Φ ] A ⁏ Γ ⊢ [ Δ , [ Φ ] A ] A →
--                         Δ , [ Φ ] A ⁏ Γ ⊢ [ Φ ] A
--
-- -- TODO: What is going on here?
-- -- Goal: Δ , [ Φ ] A ⁏ Γ ⊢ [ Φ ] A
-- -- Have: Δ , [ Φ ] A ⁏ Γ ⊢ [ Δ , [ Φ ] A ] A
-- mrefl⊢⧆ : ∀ {Δ Γ} → Telescopic Δ → Δ ⁏ Γ ⊢⧆ Δ
-- mrefl⊢⧆ {∅}           {Γ} ∅       = ∅
-- mrefl⊢⧆ {Δ , [ Φ ] A} {Γ} (τ , φ) =
--   mono⊢⧆ (weak refl⊇) refl⊇ (mrefl⊢⧆ τ) ,
--   oops
--     (box {Δ , [ Φ ] A} {Γ}
--       (mvar {Δ , [ Φ ] A} (mono⊢⧆ (weak refl⊇) done φ) zero))

lookup⊢ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ → Ξ ∋ A → Δ ⁏ Γ ⊢ A
lookup⊢ ξ 𝒾 = lookupAll ξ 𝒾

mlookup⊢ : ∀ {Δ Γ Ξ Ψ A} → Δ ⁏ Γ ⊢⧆ Ξ → Ξ ∋ [ Ψ ] A → Δ ⁏ Γ ⊢ [ Ψ ] A
mlookup⊢ (ξ , 𝒟) zero    = 𝒟
mlookup⊢ (ξ , ℰ) (suc 𝒾) = mlookup⊢ ξ 𝒾

graft⊢ : ∀ {Δ Γ Ψ A} → Δ ⁏ Γ ⊢⋆ Ψ → Δ ⁏ Ψ ⊢ A → Δ ⁏ Γ ⊢ A
graft⊢ ψ (var 𝒾)     = lookup⊢ ψ 𝒾
graft⊢ ψ (mvar φ 𝒾)  = mvar φ 𝒾
graft⊢ ψ (lam 𝒟)     = lam (graft⊢ (mono⊢⋆ refl⊇ (weak refl⊇) ψ , var zero) 𝒟)
graft⊢ ψ (app 𝒟 ℰ)   = app (graft⊢ ψ 𝒟) (graft⊢ ψ ℰ)
graft⊢ ψ (box 𝒟)     = box (graft⊢ ∅ 𝒟)
graft⊢ ψ (unbox 𝒟 ℰ) = unbox (graft⊢ ψ 𝒟) (graft⊢ (mono⊢⋆ (weak refl⊇) refl⊇ ψ) ℰ)

graft⊢⋆ : ∀ {Δ Γ Ψ Ξ} → Δ ⁏ Γ ⊢⋆ Ψ → Δ ⁏ Ψ ⊢⋆ Ξ → Δ ⁏ Γ ⊢⋆ Ξ
graft⊢⋆ ψ ∅       = ∅
graft⊢⋆ ψ (ξ , 𝒟) = graft⊢⋆ ψ ξ , graft⊢ ψ 𝒟

trans⊢⋆ : ∀ {Δ Γ Γ′ Γ″} → Δ ⁏ Γ″ ⊢⋆ Γ′ → Δ ⁏ Γ′ ⊢⋆ Γ → Δ ⁏ Γ″ ⊢⋆ Γ
trans⊢⋆ = graft⊢⋆

-- -- TODO: What is going on here?
-- -- Goal:    Δ , [ Φ ] A ⁏ ∅ ⊢ [ Φ ] A
-- -- Have:    Δ , [ Φ ] A ⁏ ∅ ⊢ [ Δ , [ Φ ] A ] A
-- -- Subgoal: Δ , [ Φ ] A ⁏ ∅ ⊢⧆ Φ
-- mutual
--   mgraft⊢ : ∀ {Δ Γ Φ A} → Δ ⁏ ∅ ⊢⧆ Φ → Φ ⁏ Γ ⊢ A → Δ ⁏ Γ ⊢ A
--   mgraft⊢ φ (var 𝒾)     = var 𝒾
--   mgraft⊢ φ (mvar φ′ 𝒾) = unbox (mono⊢ refl⊇ inf⊇ (mlookup⊢ φ 𝒾))
--                                  (mvar (mgraft⊢⧆ (mono⊢⧆ (weak refl⊇) refl⊇ φ) φ′) zero)
--   mgraft⊢ φ (lam 𝒟)     = lam (mgraft⊢ φ 𝒟)
--   mgraft⊢ φ (app 𝒟 ℰ)   = app (mgraft⊢ φ 𝒟) (mgraft⊢ φ ℰ)
--   mgraft⊢ φ (box 𝒟)     = box 𝒟
--   mgraft⊢ {Δ} {Γ} {Ξ} φ (unbox {Φ = Φ} {A} 𝒟 ℰ) =
--     unbox (mgraft⊢ φ 𝒟)
--           (mgraft⊢ (mono⊢⧆ (weak refl⊇) refl⊇ φ ,
--                      oops
--                        (box {Δ , [ Φ ] A} {∅}
--                          (mvar {Δ , [ Φ ] A} {!!} zero)) ℰ)
--
--   mgraft⊢⧆ : ∀ {Δ Γ Φ Ξ} → Δ ⁏ ∅ ⊢⧆ Φ → Φ ⁏ Γ ⊢⧆ Ξ → Δ ⁏ Γ ⊢⧆ Ξ
--   mgraft⊢⧆ φ ∅       = ∅
--   mgraft⊢⧆ φ (ξ , 𝒟) = mgraft⊢⧆ φ ξ , mgraft⊢ φ 𝒟
--
-- mtrans⊢⧆ : ∀ {Δ Δ′ Δ″} → Δ″ ⁏ ∅ ⊢⧆ Δ′ → Δ′ ⁏ ∅ ⊢⧆ Δ → Δ″ ⁏ ∅ ⊢⧆ Δ
-- mtrans⊢⧆ = mgraft⊢⧆


-- Normal forms.

mutual
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ : Cx → Ty → Set where
    lamⁿᶠ   : ∀ {Δ Γ A B} →
                Δ ⁏ Γ , A ⊢ⁿᶠ B →
                Δ ⁏ Γ ⊢ⁿᶠ A ⇒ B
    boxⁿᶠ   : ∀ {Δ Γ Φ A} →
                Φ ⁏ ∅ ⊢ A →
                Δ ⁏ Γ ⊢ⁿᶠ [ Φ ] A
    neⁿᶠ    : ∀ {Δ Γ A} →
                Δ ⁏ Γ ⊢ⁿᵉ A →
                Δ ⁏ Γ ⊢ⁿᶠ A

  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ : Cx → Ty → Set where
    varⁿᵉ   : ∀ {Δ Γ A} →
                Γ ∋ A →
                Δ ⁏ Γ ⊢ⁿᵉ A
    mvarⁿᵉ  : ∀ {Δ Γ Φ A} →
                Δ ⁏ ∅ ⊢⧆ Φ → Δ ∋ [ Φ ] A →
                Δ ⁏ Γ ⊢ⁿᵉ A
    appⁿᵉ   : ∀ {Δ Γ A B} →
                Δ ⁏ Γ ⊢ⁿᵉ A ⇒ B → Δ ⁏ Γ ⊢ⁿᶠ A →
                Δ ⁏ Γ ⊢ⁿᵉ B
    unboxⁿᵉ : ∀ {Δ Γ Φ A C} →
                Δ ⁏ Γ ⊢ⁿᵉ [ Φ ] A → Δ , [ Φ ] A ⁏ Γ ⊢ⁿᶠ C →
                Δ ⁏ Γ ⊢ⁿᵉ C

infix 3 _⊢⋆ⁿᵉ_
_⊢⋆ⁿᵉ_ : Cx → Ty⋆ → Set
Δ ⁏ Γ ⊢⋆ⁿᵉ Ξ = All (Δ ⁏ Γ ⊢ⁿᵉ_) Ξ

mutual
  mono⊢ⁿᶠ : ∀ {Δ Γ Δ′ Γ′ A} → Δ′ ⊇ Δ → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ⁿᶠ A → Δ′ ⁏ Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ ζ η (lamⁿᶠ 𝒟)     = lamⁿᶠ (mono⊢ⁿᶠ ζ (lift η) 𝒟)
  mono⊢ⁿᶠ ζ η (boxⁿᶠ 𝒟)     = boxⁿᶠ 𝒟
  mono⊢ⁿᶠ ζ η (neⁿᶠ 𝒟)      = neⁿᶠ (mono⊢ⁿᵉ ζ η 𝒟)

  mono⊢ⁿᵉ : ∀ {Δ Γ Δ′ Γ′ A} → Δ′ ⊇ Δ → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ⁿᵉ A → Δ′ ⁏ Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ ζ η (varⁿᵉ 𝒾)     = varⁿᵉ (mono∋ η 𝒾)
  mono⊢ⁿᵉ ζ η (mvarⁿᵉ φ 𝒾)  = mvarⁿᵉ (mono⊢⧆ ζ done φ) (mono∋ ζ 𝒾)
  mono⊢ⁿᵉ ζ η (appⁿᵉ 𝒟 ℰ)   = appⁿᵉ (mono⊢ⁿᵉ ζ η 𝒟) (mono⊢ⁿᶠ ζ η ℰ)
  mono⊢ⁿᵉ ζ η (unboxⁿᵉ 𝒟 ℰ) = unboxⁿᵉ (mono⊢ⁿᵉ ζ η 𝒟) (mono⊢ⁿᶠ (lift ζ) η ℰ)

mono⊢⋆ⁿᵉ : ∀ {Δ Γ Δ′ Γ′ Ξ} → Δ′ ⊇ Δ → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢⋆ⁿᵉ Ξ → Δ′ ⁏ Γ′ ⊢⋆ⁿᵉ Ξ
mono⊢⋆ⁿᵉ ζ η ξ = mapAll (mono⊢ⁿᵉ ζ η) ξ

mutual
  idmono⊢ⁿᶠ : ∀ {Δ Γ A} → (𝒟 : Δ ⁏ Γ ⊢ⁿᶠ A) → mono⊢ⁿᶠ refl⊇ refl⊇ 𝒟 ≡ 𝒟
  idmono⊢ⁿᶠ (lamⁿᶠ 𝒟)     = cong lamⁿᶠ (idmono⊢ⁿᶠ 𝒟)
  idmono⊢ⁿᶠ (boxⁿᶠ 𝒟)     = refl
  idmono⊢ⁿᶠ (neⁿᶠ 𝒟)      = cong neⁿᶠ (idmono⊢ⁿᵉ 𝒟)

  idmono⊢ⁿᵉ : ∀ {Δ Γ A} → (𝒟 : Δ ⁏ Γ ⊢ⁿᵉ A) → mono⊢ⁿᵉ refl⊇ refl⊇ 𝒟 ≡ 𝒟
  idmono⊢ⁿᵉ (varⁿᵉ 𝒾)     = cong varⁿᵉ (idmono∋ 𝒾)
  idmono⊢ⁿᵉ (mvarⁿᵉ φ 𝒾)  = cong² mvarⁿᵉ (idmono⊢⧆ φ) (idmono∋ 𝒾)
  idmono⊢ⁿᵉ (appⁿᵉ 𝒟 ℰ)   = cong² appⁿᵉ (idmono⊢ⁿᵉ 𝒟) (idmono⊢ⁿᶠ ℰ)
  idmono⊢ⁿᵉ (unboxⁿᵉ 𝒟 ℰ) = cong² unboxⁿᵉ (idmono⊢ⁿᵉ 𝒟) (idmono⊢ⁿᶠ ℰ)

mutual
  assocmono⊢ⁿᶠ : ∀ {Δ Γ Δ′ Γ′ Γ″ Δ″ A} →
                    (ζ′ : Δ″ ⊇ Δ′) (η′ : Γ″ ⊇ Γ′) (ζ : Δ′ ⊇ Δ) (η : Γ′ ⊇ Γ) (𝒟 : Δ ⁏ Γ ⊢ⁿᶠ A) →
                    mono⊢ⁿᶠ ζ′ η′ (mono⊢ⁿᶠ ζ η 𝒟) ≡ mono⊢ⁿᶠ (trans⊇ ζ′ ζ) (trans⊇ η′ η) 𝒟
  assocmono⊢ⁿᶠ ζ′ η′ ζ η (lamⁿᶠ 𝒟)     = cong lamⁿᶠ (assocmono⊢ⁿᶠ ζ′ (lift η′) ζ (lift η) 𝒟)
  assocmono⊢ⁿᶠ ζ′ η′ ζ η (boxⁿᶠ 𝒟)     = refl
  assocmono⊢ⁿᶠ ζ′ η′ ζ η (neⁿᶠ 𝒟)      = cong neⁿᶠ (assocmono⊢ⁿᵉ ζ′ η′ ζ η 𝒟)

  assocmono⊢ⁿᵉ : ∀ {Δ Γ Δ′ Γ′ Γ″ Δ″ A} →
                    (ζ′ : Δ″ ⊇ Δ′) (η′ : Γ″ ⊇ Γ′) (ζ : Δ′ ⊇ Δ) (η : Γ′ ⊇ Γ) (𝒟 : Δ ⁏ Γ ⊢ⁿᵉ A) →
                    mono⊢ⁿᵉ ζ′ η′ (mono⊢ⁿᵉ ζ η 𝒟) ≡ mono⊢ⁿᵉ (trans⊇ ζ′ ζ) (trans⊇ η′ η) 𝒟
  assocmono⊢ⁿᵉ ζ′ η′ ζ η (varⁿᵉ 𝒾)     = cong varⁿᵉ (assocmono∋ η′ η 𝒾)
  assocmono⊢ⁿᵉ ζ′ η′ ζ η (mvarⁿᵉ φ 𝒾)  = cong² mvarⁿᵉ (assocmono⊢⧆ ζ′ done ζ done φ) (assocmono∋ ζ′ ζ 𝒾)
  assocmono⊢ⁿᵉ ζ′ η′ ζ η (appⁿᵉ 𝒟 ℰ)   = cong² appⁿᵉ (assocmono⊢ⁿᵉ ζ′ η′ ζ η 𝒟) (assocmono⊢ⁿᶠ ζ′ η′ ζ η ℰ)
  assocmono⊢ⁿᵉ ζ′ η′ ζ η (unboxⁿᵉ 𝒟 ℰ) = cong² unboxⁿᵉ (assocmono⊢ⁿᵉ ζ′ η′ ζ η 𝒟) (assocmono⊢ⁿᶠ (lift ζ′) η′ (lift ζ) η ℰ)

idmono⊢⋆ⁿᵉ : ∀ {Δ Γ Ξ} → (ξ : Δ ⁏ Γ ⊢⋆ⁿᵉ Ξ) → mono⊢⋆ⁿᵉ refl⊇ refl⊇ ξ ≡ ξ
idmono⊢⋆ⁿᵉ ∅       = refl
idmono⊢⋆ⁿᵉ (ξ , 𝒟) = cong² _,_ (idmono⊢⋆ⁿᵉ ξ) (idmono⊢ⁿᵉ 𝒟)

assocmono⊢⋆ⁿᵉ : ∀ {Δ Γ Δ′ Γ′ Γ″ Δ″ Ξ} →
                   (ζ′ : Δ″ ⊇ Δ′) (η′ : Γ″ ⊇ Γ′) (ζ : Δ′ ⊇ Δ) (η : Γ′ ⊇ Γ) (ξ : Δ ⁏ Γ ⊢⋆ⁿᵉ Ξ) →
                   mono⊢⋆ⁿᵉ ζ′ η′ (mono⊢⋆ⁿᵉ ζ η ξ) ≡ mono⊢⋆ⁿᵉ (trans⊇ ζ′ ζ) (trans⊇ η′ η) ξ
assocmono⊢⋆ⁿᵉ ζ′ η′ ζ η ∅       = refl
assocmono⊢⋆ⁿᵉ ζ′ η′ ζ η (ξ , 𝒟) = cong² _,_ (assocmono⊢⋆ⁿᵉ ζ′ η′ ζ η ξ) (assocmono⊢ⁿᵉ ζ′ η′ ζ η 𝒟)


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

mv₀ : ∀ {Δ Γ Φ A} →
        Δ , [ Φ ] A ⁏ ∅ ⊢⧆ Φ →
        Δ , [ Φ ] A ⁏ Γ ⊢ A
mv₀ φ = mvar φ zero

mv₁ : ∀ {Δ Γ Φ Φ′ A B} →
        Δ , [ Φ ] A , [ Φ′ ] B ⁏ ∅ ⊢⧆ Φ →
        Δ , [ Φ ] A , [ Φ′ ] B ⁏ Γ ⊢ A
mv₁ φ = mvar φ (suc zero)

mv₂ : ∀ {Δ Γ Φ Φ′ Φ″ A B C} →
        Δ , [ Φ ] A , [ Φ′ ] B , [ Φ″ ] C ⁏ ∅ ⊢⧆ Φ →
        Δ , [ Φ ] A , [ Φ′ ] B , [ Φ″ ] C ⁏ Γ ⊢ A
mv₂ φ = mvar φ (suc (suc zero))

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

-- -- NOTE: Needs mrefl⊢⧆.
-- dᶜ : ∀ {Δ Γ Φ Φ′ A B} →
--        Telescopic Δ →
--        Δ ⁏ Γ ⊢ [ Φ ] (A ⇒ B) ⇒ [ Φ′ ] A ⇒
--                 [ Δ , [ Δ ] (A ⇒ B) , [ Δ ] A ] B
-- dᶜ τ = lam (lam (unbox v₁ (unbox v₀
--          (box (app (mv₁ (mono⊢⧆ (weak (weak refl⊇)) refl⊇ (mrefl⊢⧆ τ)))
--                    (mv₀ (mono⊢⧆ (weak (weak refl⊇)) refl⊇ (mrefl⊢⧆ τ))))))))
--
-- 4ᶜ : ∀ {Δ Γ Φ Φ′ A} →
--        Telescopic Δ →
--        Δ ⁏ Γ ⊢ [ Φ ] A ⇒
--                 [ Φ′ ] [ Δ , [ Δ ] A ] A
-- 4ᶜ τ = lam (unbox v₀
--          (box (box
--            (mv₀ (mono⊢⧆ (weak refl⊇) refl⊇ (mrefl⊢⧆ τ))))))
--
-- tᶜ : ∀ {Δ Γ A} → Telescopic Δ → Δ ⁏ Γ ⊢ [ Δ ] A ⇒ A
-- tᶜ τ = lam (unbox v₀
--          (mv₀ (mono⊢⧆ (weak refl⊇) refl⊇ (mrefl⊢⧆ τ))))


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

det : ∀ {Δ Γ A B} →
        Δ ⁏ Γ ⊢ A ⇒ B →
        Δ ⁏ Γ , A ⊢ B
det 𝒟 = app (mono⊢ refl⊇ (weak refl⊇) 𝒟) v₀

-- -- TODO: What is going on here?
-- -- Goal:    Δ , [ Φ ] A ⁏ Γ ⊢ [ Φ ] A
-- -- Have:    Δ , [ Φ ] A ⁏ Γ ⊢ [ Δ , [ Φ ] A ] A
-- -- Subgoal: Δ , [ Φ ] A ⁏ ∅ ⊢⧆ Φ
-- mdet : ∀ {Δ Γ Φ A B} →
--          Δ ⁏ Γ ⊢ [ Φ ] A ⇒ B →
--          Δ , [ Φ ] A ⁏ Γ ⊢ B
-- mdet {Δ} {Γ} {Φ} {A} {B} 𝒟 =
--   app (mono⊢ (weak refl⊇) refl⊇ 𝒟)
--     (oops (box {Δ , [ Φ ] A} {Γ} (mv₀ {Δ} {∅} {Φ} {A} {!!})))
--
-- -- NOTE: Needs example derivations.
-- dist : ∀ {Δ Γ Φ Φ′ A B} →
--          Telescopic Δ →
--          Δ ⁏ Γ ⊢ [ Φ ] (A ⇒ B) → Δ ⁏ Γ ⊢ [ Φ′ ] A →
--          Δ ⁏ Γ ⊢ [ Δ , [ Δ ] (A ⇒ B) , [ Δ ] A ] B
-- dist τ 𝒟 ℰ = app (app (dᶜ τ) 𝒟) ℰ
--
-- wrap : ∀ {Δ Γ Φ Φ′ A} →
--          Telescopic Δ →
--          Δ ⁏ Γ ⊢ [ Φ ] A →
--          Δ ⁏ Γ ⊢ [ Φ′ ] [ Δ , [ Δ ] A ] A
-- wrap τ 𝒟 = app (4ᶜ τ) 𝒟
--
-- eval : ∀ {Δ Γ A} →
--          Telescopic Δ →
--          Δ ⁏ Γ ⊢ [ Δ ] A →
--          Δ ⁏ Γ ⊢ A
-- eval τ 𝒟 = app (tᶜ τ) 𝒟