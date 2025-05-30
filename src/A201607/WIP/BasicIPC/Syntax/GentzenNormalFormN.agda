{-# OPTIONS --sized-types #-}

module A201607.WIP.BasicIPC.Syntax.GentzenNormalFormN where

open import A201607.BasicIPC.Syntax.Gentzen public

open import Data.Nat using (_+_)


mutual
  infix 3 _⊢ⁿᶠ[_]_
  data _⊢ⁿᶠ[_]_ (Γ : Cx Ty) : ℕ → Ty → Set where
    neⁿᶠ   : ∀ {A k}     → Γ ⊢ⁿᵉ[ suc k ] A → Γ ⊢ⁿᶠ[ suc k ] A
    lamⁿᶠ  : ∀ {A B k}   → Γ , A ⊢ⁿᶠ[ k ] B → Γ ⊢ⁿᶠ[ k ] A ▻ B
    pairⁿᶠ : ∀ {A B k l} → Γ ⊢ⁿᶠ[ k ] A → Γ ⊢ⁿᶠ[ l ] B → Γ ⊢ⁿᶠ[ k + l ] A ∧ B
    unitⁿᶠ : Γ ⊢ⁿᶠ[ 0 ] ⊤

  infix 3 _⊢ⁿᵉ[_]_
  data _⊢ⁿᵉ[_]_ (Γ : Cx Ty) : ℕ → Ty → Set where
    varⁿᵉ : ∀ {A k}     → A ∈ Γ → Γ ⊢ⁿᵉ[ k ] A
    appⁿᵉ : ∀ {A B k l} → Γ ⊢ⁿᵉ[ k ] A ▻ B → Γ ⊢ⁿᶠ[ l ] A → Γ ⊢ⁿᵉ[ suc (k + l) ] B
    fstⁿᵉ : ∀ {A B k}   → Γ ⊢ⁿᵉ[ k ] A ∧ B → Γ ⊢ⁿᵉ[ suc k ] A
    sndⁿᵉ : ∀ {A B k}   → Γ ⊢ⁿᵉ[ k ] A ∧ B → Γ ⊢ⁿᵉ[ suc k ] B

mutual
  nf→tm : ∀ {Γ A k} → Γ ⊢ⁿᶠ[ k ] A → Γ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)
  nf→tm unitⁿᶠ       = unit

  ne→tm : ∀ {Γ A k} → Γ ⊢ⁿᵉ[ k ] A → Γ ⊢ A
  ne→tm (varⁿᵉ i)   = var i
  ne→tm (appⁿᵉ t u) = app (ne→tm t) (nf→tm u)
  ne→tm (fstⁿᵉ t)   = fst (ne→tm t)
  ne→tm (sndⁿᵉ t)   = snd (ne→tm t)

data NfNe⁼ {Γ A} (k : ℕ) (t : Γ ⊢ A) : Set where
  nfⁿᶠⁿᵉ⁼ : (t′ : Γ ⊢ⁿᶠ[ k ] A) → {{_ : nf→tm t′ ≡ t}} → NfNe⁼ k t
  neⁿᶠⁿᵉ⁼ : (t′ : Γ ⊢ⁿᵉ[ k ] A) → {{_ : ne→tm t′ ≡ t}} → NfNe⁼ k t


mutual
  data Nf {Γ} : ∀ {A} → ℕ → Γ ⊢ A → Set where
    neⁿᶠ   : ∀ {A k}     {t : Γ ⊢ A}              → Ne (suc k) t → Nf (suc k) t
    lamⁿᶠ  : ∀ {A B k}   {t : Γ , A ⊢ B}          → Nf k t → Nf k (lam t)
    pairⁿᶠ : ∀ {A B k l} {t : Γ ⊢ A} {u : Γ ⊢ B} → Nf k t → Nf l u → Nf (k + l) (pair t u)
    unitⁿᶠ : Nf 0 unit

  data Ne {Γ} : ∀ {A} → ℕ → Γ ⊢ A → Set where
    varⁿᵉ : ∀ {A k}                                   → (i : A ∈ Γ) → Ne k (var i)
    appⁿᵉ : ∀ {A B k l} {t : Γ ⊢ A ▻ B} {u : Γ ⊢ A} → Ne k t → Nf l u → Ne (suc (k + l)) (app t u)
    fstⁿᵉ : ∀ {A B k}   {t : Γ ⊢ A ∧ B}              → Ne k t → Ne (suc k) (fst t)
    sndⁿᵉ : ∀ {A B k}   {t : Γ ⊢ A ∧ B}              → Ne k t → Ne (suc k) (snd t)

data NfNe {Γ A} (k : ℕ) (t : Γ ⊢ A) : Set where
  nfⁿᶠⁿᵉ : Nf k t → NfNe k t
  neⁿᶠⁿᵉ : Ne k t → NfNe k t

-- mutual
--   expⁿᶠ : ∀ {Γ A k} {t : Γ ⊢ A} → Nf t → Σ (Γ ⊢ⁿᶠ A) (λ t′ → nf→tm t′ ≡ t)
--   expⁿᶠ (neⁿᶠ d)     with expⁿᵉ d
--   expⁿᶠ (neⁿᶠ d)     | t′ , refl = neⁿᶠ t′ , refl
--   expⁿᶠ (lamⁿᶠ d)    with expⁿᶠ d
--   expⁿᶠ (lamⁿᶠ d)    | t′ , refl = lamⁿᶠ t′ , refl
--   expⁿᶠ (pairⁿᶠ d e) with expⁿᶠ d | expⁿᶠ e
--   expⁿᶠ (pairⁿᶠ d e) | t′ , refl | u′ , refl = pairⁿᶠ t′ u′ , refl
--   expⁿᶠ unitⁿᶠ       = unitⁿᶠ , refl

--   expⁿᵉ : ∀ {Γ A k} {t : Γ ⊢ A} → Ne t → Σ (Γ ⊢ⁿᵉ A) (λ t′ → ne→tm t′ ≡ t)
--   expⁿᵉ (varⁿᵉ i)   = varⁿᵉ i , refl
--   expⁿᵉ (appⁿᵉ d e) with expⁿᵉ d | expⁿᶠ e
--   expⁿᵉ (appⁿᵉ d e) | t′ , refl | u′ , refl = appⁿᵉ t′ u′ , refl
--   expⁿᵉ (fstⁿᵉ d)   with expⁿᵉ d
--   expⁿᵉ (fstⁿᵉ d)   | t′ , refl = fstⁿᵉ t′ , refl
--   expⁿᵉ (sndⁿᵉ d)   with expⁿᵉ d
--   expⁿᵉ (sndⁿᵉ d)   | t′ , refl = sndⁿᵉ t′ , refl

-- expⁿᶠⁿᵉ : ∀ {Γ A k} {t : Γ ⊢ A} → NfNe t → NfNe⁼ t
-- expⁿᶠⁿᵉ (nfⁿᶠⁿᵉ d) with expⁿᶠ d
-- expⁿᶠⁿᵉ (nfⁿᶠⁿᵉ d) | t′ , refl = nfⁿᶠⁿᵉ⁼ t′
-- expⁿᶠⁿᵉ (neⁿᶠⁿᵉ d) with expⁿᵉ d
-- expⁿᶠⁿᵉ (neⁿᶠⁿᵉ d) | t′ , refl = neⁿᶠⁿᵉ⁼ t′
