module Common-Properties where

open import Common public
open import Category public


----------------------------------------------------------------------------------------------------

module _ {𝓍} {X : Set 𝓍} where
  lid⊆ : ∀ {Γ Γ′ : List X} (e : Γ ⊆ Γ′) → id⊆ ∘⊆ e ≡ e
  lid⊆ stop     = refl
  lid⊆ (drop e) = drop & lid⊆ e
  lid⊆ (keep e) = keep & lid⊆ e

  rid⊆ : ∀ {Γ Γ′ : List X} (e : Γ ⊆ Γ′) → e ∘⊆ id⊆ ≡ e
  rid⊆ stop     = refl
  rid⊆ (drop e) = drop & rid⊆ e
  rid⊆ (keep e) = keep & rid⊆ e

  ass⊆ : ∀ {Γ Γ′ Γ″ Γ‴ : List X} (e″ : Γ″ ⊆ Γ‴) (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) →
         e″ ∘⊆ (e′ ∘⊆ e) ≡ (e″ ∘⊆ e′) ∘⊆ e
  ass⊆ stop      e′        e        = refl
  ass⊆ (drop e″) e′        e        = drop & ass⊆ e″ e′ e
  ass⊆ (keep e″) (drop e′) e        = drop & ass⊆ e″ e′ e
  ass⊆ (keep e″) (keep e′) (drop e) = drop & ass⊆ e″ e′ e
  ass⊆ (keep e″) (keep e′) (keep e) = keep & ass⊆ e″ e′ e

  ⟪⊆⟫ : Category 𝓍 𝓍
  ⟪⊆⟫ = record
          { Obj  = List X
          ; _▻_  = _⊆_
          ; id   = id⊆
          ; _∘_  = _∘⊆_
          ; lid▻ = lid⊆
          ; rid▻ = rid⊆
          ; ass▻ = ass⊆
          }


----------------------------------------------------------------------------------------------------

module _ {𝓍} {X : Set 𝓍} where
  idren∋ : ∀ {Γ} {A : X} (i : Γ ∋ A) → ren∋ id⊆ i ≡ i
  idren∋ zero    = refl
  idren∋ (suc i) = suc & idren∋ i

  compren∋ : ∀ {Γ Γ′ Γ″} {A : X} (e′ : Γ′ ⊆ Γ″) (e : Γ ⊆ Γ′) (i : Γ ∋ A) →
             ren∋ (e′ ∘⊆ e) i ≡ (ren∋ e′ ∘ ren∋ e) i
  compren∋ stop      e        i       = refl
  compren∋ (drop e′) e        i       = suc & compren∋ e′ e i
  compren∋ (keep e′) (drop e) i       = suc & compren∋ e′ e i
  compren∋ (keep e′) (keep e) zero    = refl
  compren∋ (keep e′) (keep e) (suc i) = suc & compren∋ e′ e i

  module _ (⚠ : Extensionality) where
    ⟪ren∋⟫ : ∀ (A : X) → Presheaf (⟪⊆⟫ ᵒᵖ) 𝓍
    ⟪ren∋⟫ A = record
                 { ƒObj = _∋ A
                 ; ƒ    = ren∋
                 ; idƒ  = ⚠ idren∋
                 ; _∘ƒ_ = λ e′ e → ⚠ (compren∋ e′ e)
                 }


----------------------------------------------------------------------------------------------------
