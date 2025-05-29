{-# OPTIONS --rewriting #-}

module A201706.IPCNormalisationExperimentalNoTerms where

open import A201706.IPCSyntaxNoTerms public
open import A201706.IPCSemanticsExperimental public
open IPCSemanticsExperimentalList public


-- Absolute values.

infix 3 _⊨_
_⊨_ : Cx → Ty → Set₁
Γ ⊨ A = ∀ {{_ : Model}} {w : World} → w ⊩⋆ Γ → w ⊩ A


-- Soundness.

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
⟦ var 𝒾 ⟧   γ = lookup⊩ γ 𝒾
⟦ lam 𝒟 ⟧   γ = λ η a → ⟦ 𝒟 ⟧ (mono⊩⋆ η γ , a)
⟦ app 𝒟 ℰ ⟧ γ = ⟦ 𝒟 ⟧ γ refl⊒ (⟦ ℰ ⟧ γ)


-- Canonical model.

private
  instance
    canon : Model
    canon = record
      { World       = Cx
      ; _⊒_         = _⊇_
      ; refl⊒       = refl⊇
      ; trans⊒      = trans⊇
      ; idtrans⊒₁   = idtrans⊇₁
      ; idtrans⊒₂   = idtrans⊇₂
      ; assoctrans⊒ = assoctrans⊇
      ; G           = _⊢ⁿᵉ •
      ; monoG       = mono⊢ⁿᵉ
      ; idmonoG     = idmono⊢ⁿᵉ
      ; assocmonoG  = assocmono⊢ⁿᵉ
      }

mutual
  reifyᶜ : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
  reifyᶜ {•}      a = neⁿᶠ a
  reifyᶜ {A ⇒ B} f = lamⁿᶠ (reifyᶜ (f (weak refl⊇) ⟦ varⁿᵉ {A = A} zero ⟧ᶜ))

  ⟦_⟧ᶜ : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
  ⟦_⟧ᶜ {•}      𝒟 = 𝒟
  ⟦_⟧ᶜ {A ⇒ B} 𝒟 = λ η a → ⟦ appⁿᵉ (mono⊢ⁿᵉ η 𝒟) (reifyᶜ a) ⟧ᶜ


-- TODO: Needs a name.

refl⊩⋆ : ∀ {Γ} → Γ ⊩⋆ Γ
refl⊩⋆ {∅}     = ∅
refl⊩⋆ {Γ , A} = mono⊩⋆ (weak refl⊇) refl⊩⋆ , ⟦ varⁿᵉ {A = A} zero ⟧ᶜ


-- Completeness.

reify : ∀ {Γ A} → Γ ⊨ A → Γ ⊢ⁿᶠ A
reify 𝔞 = reifyᶜ (𝔞 refl⊩⋆)


-- Normalisation.

nbe : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ⁿᶠ A
nbe = reify ∘ ⟦_⟧
