module PfenningDaviesS4.CoinductiveNormalisationByEvaluation where

open import Common.Delay public
open import Common.OrderPreservingEmbedding public
open import PfenningDaviesS4.Syntax public

open import Function using (flip)


-- Normal terms, neutral terms, values, and environments.

mutual
  data No (Γ Δ : Cx Ty) : Ty → Set where
    lamₙ  : ∀ {A B} → No (Γ , A) Δ B → No Γ Δ (A ⊃ B)
    pairₙ : ∀ {A B} → No Γ Δ A → No Γ Δ B → No Γ Δ (A ∧ B)
    unitₙ : No Γ Δ ⊤
    boxₙ  : ∀ {A} → No ∅ Δ A → No Γ Δ (□ A)
    neₙ   : ∀ {A} → Ne No Γ Δ A → No Γ Δ A

  data Ne (Ξ : Cx Ty → Cx Ty → Ty → Set) (Γ Δ : Cx Ty) : Ty → Set where
    varₙ   : ∀ {A} → A ∈ Γ → Ne Ξ Γ Δ A
    ⋆varₙ  : ∀ {A} → A ∈ Δ → Ne Ξ Γ Δ A
    appₙ   : ∀ {A B} → Ne Ξ Γ Δ (A ⊃ B) → Ξ Γ Δ A → Ne Ξ Γ Δ B
    fstₙ   : ∀ {A B} → Ne Ξ Γ Δ (A ∧ B) → Ne Ξ Γ Δ A
    sndₙ   : ∀ {A B} → Ne Ξ Γ Δ (A ∧ B) → Ne Ξ Γ Δ B
    unboxₙ : ∀ {A C Γᶜ Δᶜ} → Ne Ξ Γ Δ (□ A) → Tm Γᶜ (Δᶜ , A) C → Ne Ξ Γ Δ C

  data Val (Γ Δ : Cx Ty) : Ty → Set where
    lamᵥ  : ∀ {A B Γᶜ Δᶜ} → Env Γ Δ Γᶜ → Env ∅ Δ Δᶜ → Tm (Γᶜ , A) Δᶜ B → Val Γ Δ (A ⊃ B)
    pairᵥ : ∀ {A B} → Val Γ Δ A → Val Γ Δ B → Val Γ Δ (A ∧ B)
    unitᵥ : Val Γ Δ ⊤
    boxᵥ  : ∀ {A} → Val ∅ Δ A → Val Γ Δ (□ A)
    neᵥ   : ∀ {A} → Ne Val Γ Δ A → Val Γ Δ A

  data Env (Γ Δ : Cx Ty) : Cx Ty → Set where
    ∅   : Env Γ Δ ∅
    _,_ : ∀ {A Ξᶜ} → Env Γ Δ Ξᶜ → Val Γ Δ A → Env Γ Δ (Ξᶜ , A)


-- Weakening.

mutual
  ren-no : ∀ {Γ Γ′ Δ} → Γ ⊆ Γ′ → Ren (flip No Δ) Γ Γ′
  ren-no ρ (lamₙ t)    = lamₙ (ren-no (keep ρ) t)
  ren-no ρ (pairₙ t u) = pairₙ (ren-no ρ t) (ren-no ρ u)
  ren-no ρ unitₙ       = unitₙ
  ren-no ρ (boxₙ t)    = boxₙ t
  ren-no ρ (neₙ t)     = neₙ (ren-nen ρ t)

  ren-nen : ∀ {Γ Γ′ Δ} → Γ ⊆ Γ′ → Ren (flip (Ne No) Δ) Γ Γ′
  ren-nen ρ (varₙ i)     = varₙ (ren-var ρ i)
  ren-nen ρ (⋆varₙ i)    = ⋆varₙ i
  ren-nen ρ (appₙ t u)   = appₙ (ren-nen ρ t) (ren-no ρ u)
  ren-nen ρ (fstₙ t)     = fstₙ (ren-nen ρ t)
  ren-nen ρ (sndₙ t)     = sndₙ (ren-nen ρ t)
  ren-nen ρ (unboxₙ t u) = unboxₙ (ren-nen ρ t) u

  ren-nev : ∀ {Γ Γ′ Δ} → Γ ⊆ Γ′ → Ren (flip (Ne Val) Δ) Γ Γ′
  ren-nev ρ (varₙ i)     = varₙ (ren-var ρ i)
  ren-nev ρ (⋆varₙ i)    = ⋆varₙ i
  ren-nev ρ (appₙ t u)   = appₙ (ren-nev ρ t) (ren-val ρ u)
  ren-nev ρ (fstₙ t)     = fstₙ (ren-nev ρ t)
  ren-nev ρ (sndₙ t)     = sndₙ (ren-nev ρ t)
  ren-nev ρ (unboxₙ t u) = unboxₙ (ren-nev ρ t) u

  ren-val : ∀ {Γ Γ′ Δ} → Γ ⊆ Γ′ → Ren (flip Val Δ) Γ Γ′
  ren-val ρ (lamᵥ γ δ t) = lamᵥ (ren-env ρ γ) δ t
  ren-val ρ (pairᵥ t u)  = pairᵥ (ren-val ρ t) (ren-val ρ u)
  ren-val ρ unitᵥ        = unitᵥ
  ren-val ρ (boxᵥ t)     = boxᵥ t
  ren-val ρ (neᵥ t)      = neᵥ (ren-nev ρ t)

  ren-env : ∀ {Γ Γ′ Δ} → Γ ⊆ Γ′ → Ren (flip Env Δ) Γ Γ′
  ren-env ρ ∅       = ∅
  ren-env ρ (γ , t) = ren-env ρ γ , ren-val ρ t

wk-val : ∀ {A Γ Δ} → Ren (flip Val Δ) Γ (Γ , A)
wk-val = ren-val (skip refl⊆)

wk-env : ∀ {A Γ Δ} → Ren (flip Env Δ) Γ (Γ , A)
wk-env = ren-env (skip refl⊆)

wk-val∅ : ∀ {Γ Δ} → Ren (flip Val Δ) ∅ Γ
wk-val∅ = ren-val zero⊆


-- Modal weakening.

mutual
  ⋆ren-no : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → Ren (No Γ) Δ Δ′
  ⋆ren-no ρ (lamₙ t)    = lamₙ (⋆ren-no ρ t)
  ⋆ren-no ρ (pairₙ t u) = pairₙ (⋆ren-no ρ t) (⋆ren-no ρ u)
  ⋆ren-no ρ unitₙ       = unitₙ
  ⋆ren-no ρ (boxₙ t)    = boxₙ (⋆ren-no ρ t)
  ⋆ren-no ρ (neₙ t)     = neₙ (⋆ren-nen ρ t)

  ⋆ren-nen : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → Ren (Ne No Γ) Δ Δ′
  ⋆ren-nen ρ (varₙ i)     = varₙ i
  ⋆ren-nen ρ (⋆varₙ i)    = ⋆varₙ (ren-var ρ i)
  ⋆ren-nen ρ (appₙ t u)   = appₙ (⋆ren-nen ρ t) (⋆ren-no ρ u)
  ⋆ren-nen ρ (fstₙ t)     = fstₙ (⋆ren-nen ρ t)
  ⋆ren-nen ρ (sndₙ t)     = sndₙ (⋆ren-nen ρ t)
  ⋆ren-nen ρ (unboxₙ t u) = unboxₙ (⋆ren-nen ρ t) u

  ⋆ren-nev : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → Ren (Ne Val Γ) Δ Δ′
  ⋆ren-nev ρ (varₙ i)     = varₙ i
  ⋆ren-nev ρ (⋆varₙ i)    = ⋆varₙ (ren-var ρ i)
  ⋆ren-nev ρ (appₙ t u)   = appₙ (⋆ren-nev ρ t) (⋆ren-val ρ u)
  ⋆ren-nev ρ (fstₙ t)     = fstₙ (⋆ren-nev ρ t)
  ⋆ren-nev ρ (sndₙ t)     = sndₙ (⋆ren-nev ρ t)
  ⋆ren-nev ρ (unboxₙ t u) = unboxₙ (⋆ren-nev ρ t) u

  ⋆ren-val : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → Ren (Val Γ) Δ Δ′
  ⋆ren-val ρ (lamᵥ γ δ t) = lamᵥ (⋆ren-env ρ γ) (⋆ren-env ρ δ) t
  ⋆ren-val ρ (pairᵥ t u)  = pairᵥ (⋆ren-val ρ t) (⋆ren-val ρ u)
  ⋆ren-val ρ unitᵥ        = unitᵥ
  ⋆ren-val ρ (boxᵥ t)     = boxᵥ (⋆ren-val ρ t)
  ⋆ren-val ρ (neᵥ t)      = neᵥ (⋆ren-nev ρ t)

  ⋆ren-env : ∀ {Γ Δ Δ′} → Δ ⊆ Δ′ → Ren (Env Γ) Δ Δ′
  ⋆ren-env ρ ∅       = ∅
  ⋆ren-env ρ (δ , t) = ⋆ren-env ρ δ , ⋆ren-val ρ t

⋆wk-env : ∀ {A Γ Δ} → Ren (Env Γ) Δ (Δ , A)
⋆wk-env = ⋆ren-env (skip refl⊆)


-- Soundness.

lookup : ∀ {A Γ Δ Ξᶜ} → Env Γ Δ Ξᶜ → A ∈ Ξᶜ → Val Γ Δ A
lookup ∅       ()
lookup (γ , t) top     = t
lookup (γ , u) (pop i) = lookup γ i

lookup∅ : ∀ {A Δ Ξᶜ} → Env ∅ Δ Ξᶜ → A ∈ Ξᶜ → Val ∅ Δ A
lookup∅ ∅       ()
lookup∅ (δ , t) top     = t
lookup∅ (δ , u) (pop i) = lookup∅ δ i

mutual
  eval : ∀ {A Γ Δ Γᶜ Δᶜ i} → Env Γ Δ Γᶜ → Env ∅ Δ Δᶜ → Tm Γᶜ Δᶜ A → Delay i (Val Γ Δ A)
  eval γ δ (var i)     = now (lookup γ i)
  eval γ δ (⋆var i)    = now (wk-val∅ (lookup∅ δ i))
  eval γ δ (lam t)     = now (lamᵥ γ δ t)
  eval γ δ (app t u)   = t′ ← eval γ δ t ⁏ u′ ← eval γ δ u ⁏ reduce⊃ t′ u′
  eval γ δ (pair t u)  = t′ ← eval γ δ t ⁏ u′ ← eval γ δ u ⁏ now (pairᵥ t′ u′)
  eval γ δ (fst t)     = t′ ← eval γ δ t ⁏ reduce∧₁ t′
  eval γ δ (snd t)     = t′ ← eval γ δ t ⁏ reduce∧₂ t′
  eval γ δ unit        = now unitᵥ
  eval γ δ (box t)     = t′ ← eval∅ δ t  ⁏ now (boxᵥ t′)
  eval γ δ (unbox t u) = t′ ← eval γ δ t ⁏ reduce□ γ δ t′ u

  eval∅ : ∀ {A Δ Δᶜ i} → Env ∅ Δ Δᶜ → Tm ∅ Δᶜ A → Delay i (Val ∅ Δ A)
  eval∅ δ (var ())
  eval∅ δ (⋆var i)    = now (lookup∅ δ i)
  eval∅ δ (lam t)     = now (lamᵥ ∅ δ t)
  eval∅ δ (app t u)   = t′ ← eval∅ δ t ⁏ u′ ← eval∅ δ u ⁏ reduce⊃ t′ u′
  eval∅ δ (pair t u)  = t′ ← eval∅ δ t ⁏ u′ ← eval∅ δ u ⁏ now (pairᵥ t′ u′)
  eval∅ δ (fst t)     = t′ ← eval∅ δ t ⁏ reduce∧₁ t′
  eval∅ δ (snd t)     = t′ ← eval∅ δ t ⁏ reduce∧₂ t′
  eval∅ δ unit        = now unitᵥ
  eval∅ δ (box t)     = t′ ← eval∅ δ t ⁏ now (boxᵥ t′)
  eval∅ δ (unbox t u) = t′ ← eval∅ δ t ⁏ reduce□ ∅ δ t′ u

  reduce⊃ : ∀ {A B Γ Δ i} → Val Γ Δ (A ⊃ B) → Val Γ Δ A → Delay i (Val Γ Δ B)
  reduce⊃ (lamᵥ γ δ t) u = later (∞eval (γ , u) δ t)
  reduce⊃ (neᵥ t)      u = now (neᵥ (appₙ t u))

  reduce∧₁ : ∀ {A B Γ Δ i} → Val Γ Δ (A ∧ B) → Delay i (Val Γ Δ A)
  reduce∧₁ (pairᵥ t u) = now t
  reduce∧₁ (neᵥ t)     = now (neᵥ (fstₙ t))

  reduce∧₂ : ∀ {A B Γ Δ i} → Val Γ Δ (A ∧ B) → Delay i (Val Γ Δ B)
  reduce∧₂ (pairᵥ t u) = now u
  reduce∧₂ (neᵥ t)     = now (neᵥ (sndₙ t))

  reduce□ : ∀ {A C Γ Δ Γᶜ Δᶜ i} → Env Γ Δ Γᶜ → Env ∅ Δ Δᶜ → Val Γ Δ (□ A) → Tm Γᶜ (Δᶜ , A) C → Delay i (Val Γ Δ C)
  reduce□ γ δ (boxᵥ t) u = later (∞eval γ (δ , wk-val∅ t) u)
  reduce□ γ δ (neᵥ t)  u = now (neᵥ (unboxₙ t u))

  ∞eval : ∀ {A Γ Δ Γᶜ Δᶜ i} → Env Γ Δ Γᶜ → Env ∅ Δ Δᶜ → Tm Γᶜ Δᶜ A → ∞Delay i (Val Γ Δ A)
  force (∞eval γ δ t) = eval γ δ t

  ∞eval∅ : ∀ {A Δ Δᶜ i} → Env ∅ Δ Δᶜ → Tm ∅ Δᶜ A → ∞Delay i (Val ∅ Δ A)
  force (∞eval∅ δ t) = eval∅ δ t


-- Completeness.

mutual
  quot : ∀ {A Γ Δ i} → Val Γ Δ A → Delay i (No Γ Δ A)
  quot {ι}     (neᵥ t)  = neₙ <$> quotₙ t
  quot {A ⊃ B} t        = later (∞expand⊃ t)
  quot {A ∧ B} t        = later (∞expand∧ t)
  quot {□ A}   (boxᵥ t) = boxₙ <$> quot t
  quot {□ A}   (neᵥ t)  = neₙ <$> quotₙ t
  quot {⊤}    t        = now unitₙ

  quotₙ : ∀ {A Γ Δ i} → Ne Val Γ Δ A → Delay i (Ne No Γ Δ A)
  quotₙ (varₙ i)     = now (varₙ i)
  quotₙ (⋆varₙ i)    = now (⋆varₙ i)
  quotₙ (appₙ t u)   = t′ ← quotₙ t ⁏ u′ ← quot u ⁏ now (appₙ t′ u′)
  quotₙ (fstₙ t)     = t′ ← quotₙ t ⁏ now (fstₙ t′)
  quotₙ (sndₙ t)     = t′ ← quotₙ t ⁏ now (sndₙ t′)
  -- TODO: Is this correct? No expansion?
  quotₙ (unboxₙ t u) = t′ ← quotₙ t ⁏ now (unboxₙ t′ u)

  ∞expand⊃ : ∀ {A B Γ Δ i} → Val Γ Δ (A ⊃ B) → ∞Delay i (No Γ Δ (A ⊃ B))
  force (∞expand⊃ t) = t′ ← reduce⊃ (wk-val t) (neᵥ (varₙ top)) ⁏
                       t″ ← quot t′ ⁏
                       now (lamₙ t″)

  ∞expand∧ : ∀ {A B Γ Δ i} → Val Γ Δ (A ∧ B) → ∞Delay i (No Γ Δ (A ∧ B))
  force (∞expand∧ t) = t₁′ ← reduce∧₁ t ⁏ t₂′ ← reduce∧₂ t ⁏
                       t₁″ ← quot t₁′   ⁏ t₂″ ← quot t₂′ ⁏
                       now (pairₙ t₁″ t₂″)


-- Normalisation.

refl-env : ∀ {Γ Δ} → Env Γ Δ Γ
refl-env {∅}     = ∅
refl-env {γ , t} = wk-env refl-env , neᵥ (varₙ top)

⋆refl-env : ∀ {Δ} → Env ∅ Δ Δ
⋆refl-env {∅}     = ∅
⋆refl-env {δ , t} = ⋆wk-env ⋆refl-env , neᵥ (⋆varₙ top)

norm? : ∀ {A Γ Δ} → Tm Γ Δ A → Delay ∞ (No Γ Δ A)
norm? t = t′ ← eval refl-env ⋆refl-env t ⁏ quot t′
