module STLC.CoinductiveNormalisationByEvaluation where

open import Common.Delay public
open import Common.OrderPreservingEmbedding public
open import STLC.Syntax public


-- Normal terms, neutral terms, and spines.

mutual
  data No (Γ : Cx Ty) : Ty → Set where
    lamₙ  : ∀ {A B} → No (Γ , A) B → No Γ (A ⊃ B)
    pairₙ : ∀ {A B} → No Γ A → No Γ B → No Γ (A ∧ B)
    unitₙ : No Γ ⊤
    neₙ   : Ne No Γ ι → No Γ ι

  data Ne (Ξ : Cx Ty → Ty → Set) (Γ : Cx Ty) : Ty → Set where
    varₙ : ∀ {A} → A ∈ Γ → Ne Ξ Γ A
    appₙ : ∀ {A B} → Ne Ξ Γ (A ⊃ B) → Ξ Γ A → Ne Ξ Γ B
    fstₙ : ∀ {A B} → Ne Ξ Γ (A ∧ B) → Ne Ξ Γ A
    sndₙ : ∀ {A B} → Ne Ξ Γ (A ∧ B) → Ne Ξ Γ B

  data Val (Γ : Cx Ty) : Ty → Set where
    lamᵥ  : ∀ {A B Γᶜ} → Env Γ Γᶜ → Tm (Γᶜ , A) B → Val Γ (A ⊃ B)
    pairᵥ : ∀ {A B} → Val Γ A → Val Γ B → Val Γ (A ∧ B)
    unitᵥ : Val Γ ⊤
    neᵥ   : ∀ {A} → Ne Val Γ A → Val Γ A

  data Env (Γ : Cx Ty) : Cx Ty → Set where
    ∅   : Env Γ ∅
    _,_ : ∀ {A Γᶜ} → Env Γ Γᶜ → Val Γ A → Env Γ (Γᶜ , A)


-- Weakening.

mutual
  ren-no : ∀ {Γ Γ′} → Γ ⊆ Γ′ → Ren No Γ Γ′
  ren-no ρ (lamₙ t)    = lamₙ (ren-no (keep ρ) t)
  ren-no ρ (pairₙ t u) = pairₙ (ren-no ρ t) (ren-no ρ u)
  ren-no ρ unitₙ       = unitₙ
  ren-no ρ (neₙ t)     = neₙ (ren-nen ρ t)

  ren-nen : ∀ {Γ Γ′} → Γ ⊆ Γ′ → Ren (Ne No) Γ Γ′
  ren-nen ρ (varₙ i)   = varₙ (ren-var ρ i)
  ren-nen ρ (appₙ t u) = appₙ (ren-nen ρ t) (ren-no ρ u)
  ren-nen ρ (fstₙ t)   = fstₙ (ren-nen ρ t)
  ren-nen ρ (sndₙ t)   = sndₙ (ren-nen ρ t)

  ren-nev : ∀ {Γ Γ′} → Γ ⊆ Γ′ → Ren (Ne Val) Γ Γ′
  ren-nev ρ (varₙ i)   = varₙ (ren-var ρ i)
  ren-nev ρ (appₙ t u) = appₙ (ren-nev ρ t) (ren-val ρ u)
  ren-nev ρ (fstₙ t)   = fstₙ (ren-nev ρ t)
  ren-nev ρ (sndₙ t)   = sndₙ (ren-nev ρ t)

  ren-val : ∀ {Γ Γ′} → Γ ⊆ Γ′ → Ren Val Γ Γ′
  ren-val ρ (lamᵥ γ t)  = lamᵥ (ren-env ρ γ) t
  ren-val ρ (pairᵥ t u) = pairᵥ (ren-val ρ t) (ren-val ρ u)
  ren-val ρ unitᵥ       = unitᵥ
  ren-val ρ (neᵥ t)     = neᵥ (ren-nev ρ t)

  ren-env : ∀ {Γ Γ′} → Γ ⊆ Γ′ → Ren Env Γ Γ′
  ren-env ρ ∅       = ∅
  ren-env ρ (γ , t) = ren-env ρ γ , ren-val ρ t

wk-val : ∀ {A Γ} → Ren Val Γ (Γ , A)
wk-val = ren-val (skip refl⊆)

wk-env : ∀ {A Γ} → Ren Env Γ (Γ , A)
wk-env = ren-env (skip refl⊆)


-- Soundness.

lookup : ∀ {A Γ Γᶜ} → Env Γ Γᶜ → A ∈ Γᶜ → Val Γ A
lookup ∅       ()
lookup (γ , t) top     = t
lookup (γ , u) (pop i) = lookup γ i

reduce∧₁ : ∀ {A B Γ i} → Val Γ (A ∧ B) → Delay i (Val Γ A)
reduce∧₁ (pairᵥ t u) = now t
reduce∧₁ (neᵥ t)     = now (neᵥ (fstₙ t))

reduce∧₂ : ∀ {A B Γ i} → Val Γ (A ∧ B) → Delay i (Val Γ B)
reduce∧₂ (pairᵥ t u) = now u
reduce∧₂ (neᵥ t)     = now (neᵥ (sndₙ t))

mutual
  eval : ∀ {A Γ Γᶜ i} → Env Γ Γᶜ → Tm Γᶜ A → Delay i (Val Γ A)
  eval γ (var i)    = now (lookup γ i)
  eval γ (lam t)    = now (lamᵥ γ t)
  eval γ (app t u)  = t′ ← eval γ t ⁏ u′ ← eval γ u ⁏ reduce⊃ t′ u′
  eval γ (pair t u) = t′ ← eval γ t ⁏ u′ ← eval γ u ⁏ now (pairᵥ t′ u′)
  eval γ (fst t)    = t′ ← eval γ t ⁏ reduce∧₁ t′
  eval γ (snd t)    = t′ ← eval γ t ⁏ reduce∧₂ t′
  eval γ unit       = now unitᵥ

  ∞eval : ∀ {A Γ Γᶜ i} → Env Γ Γᶜ → Tm Γᶜ A → ∞Delay i (Val Γ A)
  force (∞eval γ t) = eval γ t

  reduce⊃ : ∀ {A B Γ i} → Val Γ (A ⊃ B) → Val Γ A → Delay i (Val Γ B)
  reduce⊃ (lamᵥ γ t) u = later (∞eval (γ , u) t)
  reduce⊃ (neᵥ t)    u = now (neᵥ (appₙ t u))


-- Completeness.

mutual
  quot : ∀ {A Γ i} → Val Γ A → Delay i (No Γ A)
  quot {ι}     (neᵥ t) = neₙ <$> quotₙ t
  quot {A ⊃ B} t       = later (∞expand⊃ t)
  quot {A ∧ B} t       = later (∞expand∧ t)
  quot {⊤}    t       = now unitₙ

  quotₙ : ∀ {A Γ i} → Ne Val Γ A → Delay i (Ne No Γ A)
  quotₙ (varₙ i)   = now (varₙ i)
  quotₙ (appₙ t u) = t′ ← quotₙ t ⁏ u′ ← quot u ⁏ now (appₙ t′ u′)
  quotₙ (fstₙ t)   = t′ ← quotₙ t ⁏ now (fstₙ t′)
  quotₙ (sndₙ t)   = t′ ← quotₙ t ⁏ now (sndₙ t′)

  ∞expand⊃ : ∀ {A B Γ i} → Val Γ (A ⊃ B) → ∞Delay i (No Γ (A ⊃ B))
  force (∞expand⊃ t) = t′ ← reduce⊃ (wk-val t) (neᵥ (varₙ top)) ⁏
                       t″ ← quot t′ ⁏
                       now (lamₙ t″)

  ∞expand∧ : ∀ {A B Γ i} → Val Γ (A ∧ B) → ∞Delay i (No Γ (A ∧ B))
  force (∞expand∧ t) = t₁′ ← reduce∧₁ t ⁏ t₂′ ← reduce∧₂ t ⁏
                       t₁″ ← quot t₁′   ⁏ t₂″ ← quot t₂′ ⁏
                       now (pairₙ t₁″ t₂″)


-- Normalisation.

env-refl : ∀ {Γ} → Env Γ Γ
env-refl {∅}     = ∅
env-refl {γ , t} = wk-env env-refl , neᵥ (varₙ top)

norm? : ∀ {A Γ} → Tm Γ A → Delay ∞ (No Γ A)
norm? t = t′ ← eval env-refl t ⁏
          quot t′
