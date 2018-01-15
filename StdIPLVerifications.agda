module StdIPLVerifications where

open import Prelude
open import List
open import AllList
open import StdIPLPropositions
open import StdIPLDerivations


--------------------------------------------------------------------------------


-- We read “A verified” as “A has a verification”.

infix 7 _verified
record Verification : Set
  where
    constructor _verified
    field
      A : Prop


v→t : Verification → Truth
v→t (A verified) = A true


-- We read “A usable” as “A may be used”.

infix 7 _usable
record Use : Set
  where
    constructor _usable
    field
      A : Prop


u→t : Use → Truth
u→t (A usable) = A true


t→u : Truth → Use
t→u (A true) = A usable


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢ₙ_
  data _⊢ₙ_ : List Use → Verification → Set
    where
      lam : ∀ {A B Γ} → Γ , A usable ⊢ₙ B verified
                      → Γ ⊢ₙ A ⊃ B verified

      use : ∀ {Γ} → Γ ⊢ᵣ BASE usable
                  → Γ ⊢ₙ BASE verified

  infix 3 _⊢ᵣ_
  data _⊢ᵣ_ : List Use → Use → Set
    where
      var : ∀ {A Γ} → Γ ∋ A usable
                    → Γ ⊢ᵣ A usable

      app : ∀ {A B Γ} → Γ ⊢ᵣ A ⊃ B usable → Γ ⊢ₙ A verified
                      → Γ ⊢ᵣ B usable


--------------------------------------------------------------------------------


mutual
  nd→d : ∀ {Γ A} → Γ ⊢ₙ A verified
                  → map u→t Γ ⊢ A true
  nd→d (lam 𝒟) = lam (nd→d 𝒟)
  nd→d (use 𝒟) = rd→d 𝒟

  rd→d : ∀ {Γ A} → Γ ⊢ᵣ A usable
                  → map u→t Γ ⊢ A true
  rd→d (var 𝒾)   = var (map∋ 𝒾)
  rd→d (app 𝒟 ℰ) = app (rd→d 𝒟) (nd→d ℰ)


--------------------------------------------------------------------------------


mutual
  renₙ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ₙ A verified
                    → Γ′ ⊢ₙ A verified
  renₙ η (lam 𝒟) = lam (renₙ (keep η) 𝒟)
  renₙ η (use 𝒟) = use (renᵣ η 𝒟)

  renᵣ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ᵣ A usable
                    → Γ′ ⊢ᵣ A usable
  renᵣ η (var 𝒾)   = var (ren∋ η 𝒾)
  renᵣ η (app 𝒟 ℰ) = app (renᵣ η 𝒟) (renₙ η ℰ)


wkᵣ : ∀ {B A Γ} → Γ ⊢ᵣ A usable
                → Γ , B usable ⊢ᵣ A usable
wkᵣ 𝒟 = renᵣ (drop id⊇) 𝒟


vzᵣ : ∀ {A Γ} → Γ , A usable ⊢ᵣ A usable
vzᵣ = var zero


--------------------------------------------------------------------------------
