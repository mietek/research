{-# OPTIONS --rewriting #-}

module A201706.ISLPSyntaxTerms where

open import A201706.ISLP public


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
    mvar  : ∀ {`d `g Δ Γ q p} {Φ : BoxTy⋆ `d} {Ψ : Ty⋆ `g} {i Q A} →
              Δ ⁏ ∅ ⊢⧆ q ∷ Φ → Δ ⁏ Γ ⊢⋆ p ∷ Ψ → Δ ∋⟨ i ⟩ [ Φ ⁏ Ψ ⊦ Q ] A →
              Δ ⁏ Γ ⊢ MVAR q p i ∷ A
    lam   : ∀ {Δ Γ M A B} →
              Δ ⁏ Γ , A ⊢ M ∷ B →
              Δ ⁏ Γ ⊢ LAM M ∷ A ⇒ B
    app   : ∀ {Δ Γ M N A B} →
              Δ ⁏ Γ ⊢ M ∷ A ⇒ B → Δ ⁏ Γ ⊢ N ∷ A →
              Δ ⁏ Γ ⊢ APP M N ∷ B
    box   : ∀ {`d `g Δ Γ} {Φ : BoxTy⋆ `d} {Ψ : Ty⋆ `g} {M A} →
              Φ ⁏ Ψ ⊢ M ∷ A →
              Δ ⁏ Γ ⊢ BOX M ∷ [ Φ ⁏ Ψ ⊦ M ] A
    unbox : ∀ {`d `g Δ Γ} {Φ : BoxTy⋆ `d} {Ψ : Ty⋆ `g} {M N Q A C} →
              Δ ⁏ Γ ⊢ M ∷ [ Φ ⁏ Ψ ⊦ Q ] A → Δ , [ Φ ⁏ Ψ ⊦ Q ] A ⁏ Γ ⊢ N ∷ C →
              Δ ⁏ Γ ⊢ UNBOX M N ∷ C

  infix 3 _⊢⧆_∷_
  data _⊢⧆_∷_ {d g} : ∀ {n} → Cx d g → Tm⋆ d g n → BoxTy⋆ n → Set where
    ∅   : ∀ {Δ Γ} →
            Δ ⁏ Γ ⊢⧆ ∅ ∷ ∅
    _,_ : ∀ {`d `g n Δ Γ} {Φ : BoxTy⋆ `d} {Ψ : Ty⋆ `g} {x} {Ξ : BoxTy⋆ n} {M Q A} →
            Δ ⁏ Γ ⊢⧆ x ∷ Ξ → Δ ⁏ Γ ⊢ M ∷ [ Φ ⁏ Ψ ⊦ Q ] A →
            Δ ⁏ Γ ⊢⧆ x , M ∷ Ξ , [ Φ ⁏ Ψ ⊦ Q ] A

  infix 3 _⊢⋆_∷_
  data _⊢⋆_∷_ {d g} : ∀ {n} → Cx d g → Tm⋆ d g n → Ty⋆ n → Set where
    ∅   : ∀ {Δ Γ} →
            Δ ⁏ Γ ⊢⋆ ∅ ∷ ∅
    _,_ : ∀ {n Δ Γ x} {Ξ : Ty⋆ n} {M A} →
            Δ ⁏ Γ ⊢⋆ x ∷ Ξ → Δ ⁏ Γ ⊢ M ∷ A →
            Δ ⁏ Γ ⊢⋆ x , M ∷ Ξ , A

mutual
  mono⊢ : ∀ {d g d′ g′} {Δ : BoxTy⋆ d} {Γ : Ty⋆ g} {Δ′ : BoxTy⋆ d′} {Γ′ : Ty⋆ g′} {M A z e} →
             Δ′ ⊇⟨ z ⟩ Δ → Γ′ ⊇⟨ e ⟩ Γ → Δ ⁏ Γ ⊢ M ∷ A → Δ′ ⁏ Γ′ ⊢ monoTm z e M ∷ A
  mono⊢ ζ η (var 𝒾)      = var (mono∋ η 𝒾)
  mono⊢ ζ η (mvar φ ψ 𝒾) = mvar (mono⊢⧆ ζ done φ) (mono⊢⋆ ζ η ψ) (mono∋ ζ 𝒾)
  mono⊢ ζ η (lam 𝒟)      = lam (mono⊢ ζ (lift η) 𝒟)
  mono⊢ ζ η (app 𝒟 ℰ)    = app (mono⊢ ζ η 𝒟) (mono⊢ ζ η ℰ)
  mono⊢ ζ η (box 𝒟)      = box 𝒟
  mono⊢ ζ η (unbox 𝒟 ℰ)  = unbox (mono⊢ ζ η 𝒟) (mono⊢ (lift ζ) η ℰ)

  mono⊢⧆ : ∀ {d g d′ g′ n} {Δ : BoxTy⋆ d} {Γ : Ty⋆ g} {Δ′ : BoxTy⋆ d′} {Γ′ : Ty⋆ g′} {x} {Ξ : BoxTy⋆ n} {z e} →
               Δ′ ⊇⟨ z ⟩ Δ → Γ′ ⊇⟨ e ⟩ Γ → Δ ⁏ Γ ⊢⧆ x ∷ Ξ → Δ′ ⁏ Γ′ ⊢⧆ monoTm⋆ z e x ∷ Ξ
  mono⊢⧆ ζ η ∅       = ∅
  mono⊢⧆ ζ η (ξ , 𝒟) = mono⊢⧆ ζ η ξ , mono⊢ ζ η 𝒟

  mono⊢⋆ : ∀ {d g d′ g′ n} {Δ : BoxTy⋆ d} {Γ : Ty⋆ g} {Δ′ : BoxTy⋆ d′} {Γ′ : Ty⋆ g′} {x} {Ξ : Ty⋆ n} {z e} →
              Δ′ ⊇⟨ z ⟩ Δ → Γ′ ⊇⟨ e ⟩ Γ → Δ ⁏ Γ ⊢⋆ x ∷ Ξ → Δ′ ⁏ Γ′ ⊢⋆ monoTm⋆ z e x ∷ Ξ
  mono⊢⋆ ζ η ∅       = ∅
  mono⊢⋆ ζ η (ξ , 𝒟) = mono⊢⋆ ζ η ξ , mono⊢ ζ η 𝒟

refl⊢⋆ : ∀ {d g} {Δ : BoxTy⋆ d} {Γ : Ty⋆ g} → Δ ⁏ Γ ⊢⋆ reflTm⋆ ∷ Γ
refl⊢⋆ {Γ = ∅}     = ∅
refl⊢⋆ {Γ = Γ , A} = mono⊢⋆ refl⊇ (weak refl⊇) refl⊢⋆ , var zero

-- TODO: What is going on here?
-- mrefl⊢⋆ : ∀ {d g} {Δ : BoxTy⋆ d} {Γ : Ty⋆ g} → Δ ⁏ Γ ⊢⧆ {!!} ∷ Δ
-- mrefl⊢⋆ {Δ = ∅}                   = ∅
-- mrefl⊢⋆ {Δ = Δ , [ Φ ⁏ Ψ ⊦ M ] A} =
--   mono⊢⧆ (weak refl⊇) refl⊇ mrefl⊢⋆ ,
--   {!box (mvar ? ? zero)!}
