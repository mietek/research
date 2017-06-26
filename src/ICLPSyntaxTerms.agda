{-# OPTIONS --rewriting #-}

module ICLPSyntaxTerms where

open import ICLP public


-- Contexts.

Cx : Nat → Nat → Set
Cx d g = BoxTy⋆ d ∧ Ty⋆ g


-- Derivations.

mutual
  infix 3 _⊢_∷_
  data _⊢_∷_ {d g} : Cx d g → Tm d g → Ty → Set where
    var   : ∀ {Δ Γ i A} →
              Γ ∋⟨ i ⟩ A →
              Δ ⁏ Γ ⊢ VAR i ∷ A
    mvar  : ∀ {`g Δ Γ p} {Ψ : Ty⋆ `g} {i} {Q : Tm d `g} {A} →
              Δ ⁏ Γ ⊢⋆ p ∷ Ψ → Δ ∋⟨ i ⟩ [ Ψ ⊦ Q ] A →
              Δ ⁏ Γ ⊢ MVAR p i ∷ A
    lam   : ∀ {Δ Γ M A B} →
              Δ ⁏ Γ , A ⊢ M ∷ B →
              Δ ⁏ Γ ⊢ LAM M ∷ A ⇒ B
    app   : ∀ {Δ Γ M N A B} →
              Δ ⁏ Γ ⊢ M ∷ A ⇒ B → Δ ⁏ Γ ⊢ N ∷ A →
              Δ ⁏ Γ ⊢ APP M N ∷ B
    box   : ∀ {`g Δ Γ} {Ψ : Ty⋆ `g} {M A} →
              Δ ⁏ Ψ ⊢ M ∷ A →
              Δ ⁏ Γ ⊢ BOX M ∷ [ Ψ ⊦ M ] A
    unbox : ∀ {`g Δ Γ} {Ψ : Ty⋆ `g} {M N} {Q : Tm d `g} {A C} →
              Δ ⁏ Γ ⊢ M ∷ [ Ψ ⊦ Q ] A → Δ , [ Ψ ⊦ Q ] A ⁏ Γ ⊢ N ∷ C →
              Δ ⁏ Γ ⊢ UNBOX M N ∷ C

  infix 3 _⊢⋆_∷_
  data _⊢⋆_∷_ {d g} : ∀ {n} → Cx d g → Tm⋆ d g n → Ty⋆ n → Set where
    ∅   : ∀ {Δ Γ} →
            Δ ⁏ Γ ⊢⋆ ∅ ∷ ∅
    _,_ : ∀ {`g n Δ Γ} {Ψ : Ty⋆ `g} {x} {Ξ : Ty⋆ n} {M} {Q : Tm d `g} {A} →
            Δ ⁏ Γ ⊢⋆ x ∷ Ξ → Δ ⁏ Γ ⊢ M ∷ [ Ψ ⊦ Q ] A →
            Δ ⁏ Γ ⊢⋆ x , M ∷ Ξ , [ Ψ ⊦ Q ] A

-- TODO: What is going on here?
-- mutual
--   mono⊢ : ∀ {d g d′ g′} {Δ : BoxTy⋆ d} {Γ : Ty⋆ g} {Δ′ : BoxTy⋆ d′} {Γ′ : Ty⋆ g′} {M A z e} →
--              Δ′ ⊇⟨ z ⟩ Δ → Γ′ ⊇⟨ e ⟩ Γ → Δ ⁏ Γ ⊢ M ∷ A → Δ′ ⁏ Γ′ ⊢ monoTm z e M ∷ A
--   mono⊢ ζ η (var 𝒾)     = var (mono∋ η 𝒾)
--   mono⊢ ζ η (mvar ψ 𝒾)  = mvar (mono⊢⋆ ζ η ψ) {!mono∋ ζ 𝒾!}
--   mono⊢ ζ η (lam 𝒟)     = lam (mono⊢ ζ (lift η) 𝒟)
--   mono⊢ ζ η (app 𝒟 ℰ)   = app (mono⊢ ζ η 𝒟) (mono⊢ ζ η ℰ)
--   mono⊢ ζ η (box 𝒟)     = {!box (mono⊢ ζ refl⊇ 𝒟)!}
--   mono⊢ ζ η (unbox 𝒟 ℰ) = {!unbox (mono⊢ ζ η 𝒟) ?!}
--
--   mono⊢⋆ : ∀ {d g d′ g′ n} {Δ : BoxTy⋆ d} {Γ : Ty⋆ g} {Δ′ : BoxTy⋆ d′} {Γ′ : Ty⋆ g′} {x} {Ξ : Ty⋆ n} {z e} →
--               Δ′ ⊇⟨ z ⟩ Δ → Γ′ ⊇⟨ e ⟩ Γ → Δ ⁏ Γ ⊢⋆ x ∷ Ξ → Δ′ ⁏ Γ′ ⊢⋆ monoTm⋆ z e x ∷ Ξ
--   mono⊢⋆ ζ η ∅       = ∅
--   mono⊢⋆ ζ η (ξ , 𝒟) = {!mono⊢⋆ ζ η ξ , {!mono⊢ ζ η 𝒟!}!}
