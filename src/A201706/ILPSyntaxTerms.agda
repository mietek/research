{-# OPTIONS --rewriting #-}

module A201706.ILPSyntaxTerms where

open import A201706.ILP public


-- Contexts.

Cx : Nat → Nat → Set
Cx d g = BoxTy⋆ d ∧ Ty⋆ g


-- Derivations.

infix 3 _⊢_∷_
data _⊢_∷_ {d g} : Cx d g → Tm d g → Ty → Set where
  var   : ∀ {Δ Γ i A} →
            Γ ∋⟨ i ⟩ A →
            Δ ⁏ Γ ⊢ VAR i ∷ A
  mvar  : ∀ {Δ Γ i} {Q : Tm d zero} {A} →
            Δ ∋⟨ i ⟩ [ Q ] A →
            Δ ⁏ Γ ⊢ MVAR i ∷ A
  lam   : ∀ {Δ Γ M A B} →
            Δ ⁏ Γ , A ⊢ M ∷ B →
            Δ ⁏ Γ ⊢ LAM M ∷ A ⇒ B
  app   : ∀ {Δ Γ M N A B} →
            Δ ⁏ Γ ⊢ M ∷ A ⇒ B → Δ ⁏ Γ ⊢ N ∷ A →
            Δ ⁏ Γ ⊢ APP M N ∷ B
  box   : ∀ {Δ Γ M A} →
            Δ ⁏ ∅ ⊢ M ∷ A →
            Δ ⁏ Γ ⊢ BOX M ∷ [ M ] A
  unbox : ∀ {Δ Γ M N} {Q : Tm d zero} {A C} →
            Δ ⁏ Γ ⊢ M ∷ [ Q ] A → Δ , [ Q ] A ⁏ Γ ⊢ N ∷ C →
            Δ ⁏ Γ ⊢ UNBOX M N ∷ C

-- TODO: What is going on here?
-- mono⊢ : ∀ {d g d′ g′} {Δ : BoxTy⋆ d} {Γ : Ty⋆ g} {Δ′ : BoxTy⋆ d′} {Γ′ : Ty⋆ g′} {M A z e} →
--            Δ′ ⊇⟨ z ⟩ Δ → Γ′ ⊇⟨ e ⟩ Γ → Δ ⁏ Γ ⊢ M ∷ A → Δ′ ⁏ Γ′ ⊢ monoTm z e M ∷ A
-- mono⊢ ζ η (var 𝒾)     = var (mono∋ η 𝒾)
-- mono⊢ ζ η (mvar 𝒾)    = mvar {!mono∋ ζ 𝒾!}
-- mono⊢ ζ η (lam 𝒟)     = lam (mono⊢ ζ (lift η) 𝒟)
-- mono⊢ ζ η (app 𝒟 ℰ)   = app (mono⊢ ζ η 𝒟) (mono⊢ ζ η ℰ)
-- mono⊢ ζ η (box 𝒟)     = {!box (mono⊢ ζ done 𝒟)!}
-- mono⊢ ζ η (unbox 𝒟 ℰ) = {!unbox (mono⊢ ζ η 𝒟) ?!}
