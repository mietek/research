{-# OPTIONS --rewriting #-}

module A201801.FullS4BidirectionalDerivationsForNormalisation where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.FullS4Propositions
open import A201801.FullS4StandardDerivations
open import A201801.FullS4EmbeddingOfFullIPL
open import A201801.FullS4ProjectionToFullIPL
import A201801.FullIPLPropositions as IPL
import A201801.FullIPLDerivations as IPL


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢_normal[_]
  data _⊢_normal[_] : List Assert → Form → List Form → Set
    where
      lam : ∀ {A B Δ Γ} → Δ ⊢ B normal[ Γ , A ]
                        → Δ ⊢ A ⊃ B normal[ Γ ]

      pair : ∀ {A B Δ Γ} → Δ ⊢ A normal[ Γ ] → Δ ⊢ B normal[ Γ ]
                         → Δ ⊢ A ∧ B normal[ Γ ]

      unit : ∀ {Δ Γ} → Δ ⊢ 𝟏 normal[ Γ ]

      abort : ∀ {A Δ Γ} → Δ ⊢ 𝟎 neutral[ Γ ]
                        → Δ ⊢ A normal[ Γ ]

      inl : ∀ {A B Δ Γ} → Δ ⊢ A normal[ Γ ]
                        → Δ ⊢ A ∨ B normal[ Γ ]

      inr : ∀ {A B Δ Γ} → Δ ⊢ B normal[ Γ ]
                        → Δ ⊢ A ∨ B normal[ Γ ]

      case : ∀ {A B C Δ Γ} → Δ ⊢ A ∨ B neutral[ Γ ] → Δ ⊢ C normal[ Γ , A ] → Δ ⊢ C normal[ Γ , B ]
                           → Δ ⊢ C normal[ Γ ]

      box : ∀ {A Δ Γ} → Δ ⊢ A valid[ ∙ ]
                      → Δ ⊢ □ A normal[ Γ ]

      letbox : ∀ {A B Δ Γ} → Δ ⊢ □ A neutral[ Γ ] → Δ , ⟪⊫ A ⟫ ⊢ B normal[ Γ ]
                           → Δ ⊢ B normal[ Γ ]

      use : ∀ {P Δ Γ} → Δ ⊢ ι P neutral[ Γ ]
                      → Δ ⊢ ι P normal[ Γ ]

  infix 3 _⊢_neutral[_]
  data _⊢_neutral[_] : List Assert → Form → List Form → Set
    where
      var : ∀ {A Δ Γ} → Γ ∋ A
                      → Δ ⊢ A neutral[ Γ ]

      app : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B neutral[ Γ ] → Δ ⊢ A normal[ Γ ]
                        → Δ ⊢ B neutral[ Γ ]

      fst : ∀ {A B Δ Γ} → Δ ⊢ A ∧ B neutral[ Γ ]
                        → Δ ⊢ A neutral[ Γ ]

      snd : ∀ {A B Δ Γ} → Δ ⊢ A ∧ B neutral[ Γ ]
                        → Δ ⊢ B neutral[ Γ ]

      mvar : ∀ {A Δ Γ} → Δ ∋ ⟪⊫ A ⟫
                       → Δ ⊢ A neutral[ Γ ]


--------------------------------------------------------------------------------


mutual
  renₗ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⊢ A normal[ Γ ]
                      → Δ ⊢ A normal[ Γ′ ]
  renₗ η (lam 𝒟)      = lam (renₗ (keep η) 𝒟)
  renₗ η (pair 𝒟 ℰ)   = pair (renₗ η 𝒟) (renₗ η ℰ)
  renₗ η unit         = unit
  renₗ η (abort 𝒟)    = abort (renᵣ η 𝒟)
  renₗ η (inl 𝒟)      = inl (renₗ η 𝒟)
  renₗ η (inr 𝒟)      = inr (renₗ η 𝒟)
  renₗ η (case 𝒟 ℰ ℱ) = case (renᵣ η 𝒟) (renₗ (keep η) ℰ) (renₗ (keep η) ℱ)
  renₗ η (box 𝒟)      = box 𝒟
  renₗ η (letbox 𝒟 ℰ) = letbox (renᵣ η 𝒟) (renₗ η ℰ)
  renₗ η (use 𝒟)      = use (renᵣ η 𝒟)

  renᵣ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⊢ A neutral[ Γ ]
                      → Δ ⊢ A neutral[ Γ′ ]
  renᵣ η (var i)   = var (ren∋ η i)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₗ η ℰ)
  renᵣ η (fst 𝒟)   = fst (renᵣ η 𝒟)
  renᵣ η (snd 𝒟)   = snd (renᵣ η 𝒟)
  renᵣ η (mvar i)  = mvar i


--------------------------------------------------------------------------------


wkᵣ : ∀ {B Δ Γ A} → Δ ⊢ A neutral[ Γ ]
                  → Δ ⊢ A neutral[ Γ , B ]
wkᵣ 𝒟 = renᵣ (drop id⊇) 𝒟


vzᵣ : ∀ {Δ Γ A} → Δ ⊢ A neutral[ Γ , A ]
vzᵣ = var zero


--------------------------------------------------------------------------------


mutual
  mrenₗ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⊢ A normal[ Γ ]
                       → Δ′ ⊢ A normal[ Γ ]
  mrenₗ η (lam 𝒟)      = lam (mrenₗ η 𝒟)
  mrenₗ η (pair 𝒟 ℰ)   = pair (mrenₗ η 𝒟) (mrenₗ η ℰ)
  mrenₗ η unit         = unit
  mrenₗ η (abort 𝒟)    = abort (mrenᵣ η 𝒟)
  mrenₗ η (inl 𝒟)      = inl (mrenₗ η 𝒟)
  mrenₗ η (inr 𝒟)      = inr (mrenₗ η 𝒟)
  mrenₗ η (case 𝒟 ℰ ℱ) = case (mrenᵣ η 𝒟) (mrenₗ η ℰ) (mrenₗ η ℱ)
  mrenₗ η (box 𝒟)      = box (mren η 𝒟)
  mrenₗ η (letbox 𝒟 ℰ) = letbox (mrenᵣ η 𝒟) (mrenₗ (keep η) ℰ)
  mrenₗ η (use 𝒟)      = use (mrenᵣ η 𝒟)

  mrenᵣ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⊢ A neutral[ Γ ]
                       → Δ′ ⊢ A neutral[ Γ ]
  mrenᵣ η (var i)   = var i
  mrenᵣ η (app 𝒟 ℰ) = app (mrenᵣ η 𝒟) (mrenₗ η ℰ)
  mrenᵣ η (fst 𝒟)   = fst (mrenᵣ η 𝒟)
  mrenᵣ η (snd 𝒟)   = snd (mrenᵣ η 𝒟)
  mrenᵣ η (mvar i)  = mvar (ren∋ η i)


--------------------------------------------------------------------------------


mwkᵣ : ∀ {B A Δ Γ} → Δ ⊢ A neutral[ Γ ]
                   → Δ , B ⊢ A neutral[ Γ ]
mwkᵣ 𝒟 = mrenᵣ (drop id⊇) 𝒟


mvzᵣ : ∀ {Δ Γ A} → Δ , ⟪⊫ A ⟫ ⊢ A neutral[ Γ ]
mvzᵣ = mvar zero


--------------------------------------------------------------------------------


mutual
  denmₗ : ∀ {Δ Γ A} → Δ ⊢ A normal[ Γ ]
                    → Δ ⊢ A valid[ Γ ]
  denmₗ (lam 𝒟)      = lam (denmₗ 𝒟)
  denmₗ (pair 𝒟 ℰ)   = pair (denmₗ 𝒟) (denmₗ ℰ)
  denmₗ unit         = unit
  denmₗ (abort 𝒟)    = abort (denmᵣ 𝒟)
  denmₗ (inl 𝒟)      = inl (denmₗ 𝒟)
  denmₗ (inr 𝒟)      = inr (denmₗ 𝒟)
  denmₗ (case 𝒟 ℰ ℱ) = case (denmᵣ 𝒟) (denmₗ ℰ) (denmₗ ℱ)
  denmₗ (box 𝒟)      = box 𝒟
  denmₗ (letbox 𝒟 ℰ) = letbox (denmᵣ 𝒟) (denmₗ ℰ)
  denmₗ (use 𝒟)      = denmᵣ 𝒟

  denmᵣ : ∀ {Δ Γ A} → Δ ⊢ A neutral[ Γ ]
                    → Δ ⊢ A valid[ Γ ]
  denmᵣ (var i)   = var i
  denmᵣ (app 𝒟 ℰ) = app (denmᵣ 𝒟) (denmₗ ℰ)
  denmᵣ (fst 𝒟)   = fst (denmᵣ 𝒟)
  denmᵣ (snd 𝒟)   = snd (denmᵣ 𝒟)
  denmᵣ (mvar i)  = mvar i


--------------------------------------------------------------------------------
