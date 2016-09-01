module NewBasicILP.Syntax.Projection where

open import Common.UntypedContext public

import NewBasicILP.UntypedSyntax.ClosedHilbertSequential as CHS
import NewBasicILP.UntypedSyntax.ClosedHilbert as CH


-- Projection of types and derivations to a form parametrised by a closed, untyped representation of syntax.

module ClosedHilbertSequential where
  open import NewBasicILP.Syntax.ClosedHilbertSequential

  mutual
    ⌊_⌋ᵀ : Ty → CHS.Ty
    ⌊ α P ⌋ᵀ   = CHS.α P
    ⌊ A ▻ B ⌋ᵀ = ⌊ A ⌋ᵀ CHS.▻ ⌊ B ⌋ᵀ
    ⌊ p ⦂ A ⌋ᵀ = ⌊ p ⌋ᴾ CHS.⦂ ⌊ A ⌋ᵀ
    ⌊ A ∧ B ⌋ᵀ = ⌊ A ⌋ᵀ CHS.∧ ⌊ B ⌋ᵀ
    ⌊ ⊤ ⌋ᵀ    = CHS.⊤

    -- FIXME: WHat is going on here?
    postulate
      ⌊_⌋ᴾ : ∀ {Ξ A} → Proof Ξ A → CHS.Proof

    ⌊_⌋ᵀ⋆ : Cx Ty → Cx CHS.Ty
    ⌊ ∅ ⌋ᵀ⋆     = ∅
    ⌊ Γ , A ⌋ᵀ⋆ = ⌊ Γ ⌋ᵀ⋆ , ⌊ A ⌋ᵀ

    ⌊_⌋∈ : ∀ {Ξ A} → A ∈ Ξ → ⌊ A ⌋ᵀ ∈ ⌊ Ξ ⌋ᵀ⋆
    ⌊ top ⌋∈   = top
    ⌊ pop i ⌋∈ = pop ⌊ i ⌋∈

    ⌊_⌋ᴰ : ∀ {Ξ} → ⊢ᴰ Ξ → CHS.⊢ᴰ ⌊ Ξ ⌋ᵀ⋆
    ⌊ nil ⌋ᴰ      = CHS.nil
    ⌊ mp i j d ⌋ᴰ = CHS.mp ⌊ i ⌋∈ ⌊ j ⌋∈ ⌊ d ⌋ᴰ
    ⌊ ci d ⌋ᴰ     = CHS.ci ⌊ d ⌋ᴰ
    ⌊ ck d ⌋ᴰ     = CHS.ck ⌊ d ⌋ᴰ
    ⌊ cs d ⌋ᴰ     = CHS.cs ⌊ d ⌋ᴰ
    ⌊ nec `d d ⌋ᴰ = {!CHS.nec ⌊ `d ⌋ᴰ ⌊ d ⌋ᴰ!}
    ⌊ cdist d ⌋ᴰ  = {!CHS.cdist ⌊ d ⌋ᴰ!}
    ⌊ cup d ⌋ᴰ    = {!CHS.cup ⌊ d ⌋ᴰ!}
    ⌊ cdown d ⌋ᴰ  = CHS.cdown ⌊ d ⌋ᴰ
    ⌊ cpair d ⌋ᴰ  = CHS.cpair ⌊ d ⌋ᴰ
    ⌊ cfst d ⌋ᴰ   = CHS.cfst ⌊ d ⌋ᴰ
    ⌊ csnd d ⌋ᴰ   = CHS.csnd ⌊ d ⌋ᴰ
    ⌊ tt d ⌋ᴰ     = CHS.tt ⌊ d ⌋ᴰ

    ⌊_⌋ : ∀ {A} → ⊢ A → CHS.⊢ ⌊ A ⌋ᵀ
    ⌊ Ξ , d ⌋ = ⌊ Ξ ⌋ᵀ⋆ , ⌊ d ⌋ᴰ


-- Projection of types and derivations to a form parametrised by a closed, untyped representation of syntax.

module ClosedHilbert where
  open import NewBasicILP.Syntax.ClosedHilbert

  mutual
    ⌊_⌋ᵀ : Ty → CH.Ty
    ⌊ α P ⌋ᵀ   = CH.α P
    ⌊ A ▻ B ⌋ᵀ = ⌊ A ⌋ᵀ CH.▻ ⌊ B ⌋ᵀ
    ⌊ p ⦂ A ⌋ᵀ = ⌊ p ⌋ᴾ CH.⦂ ⌊ A ⌋ᵀ
    ⌊ A ∧ B ⌋ᵀ = ⌊ A ⌋ᵀ CH.∧ ⌊ B ⌋ᵀ
    ⌊ ⊤ ⌋ᵀ    = CH.⊤

    ⌊_⌋ᴾ : ∀ {A} → Proof A → CH.Proof
    ⌊ [ d ] ⌋ᴾ = CH.[ CH.ᴿ⌊ ⌊ d ⌋ ⌋ ]

    ⌊_⌋ : ∀ {A} → ⊢ A → CH.⊢ ⌊ A ⌋ᵀ
    ⌊ app d₁ d₂ ⌋ = CH.app ⌊ d₁ ⌋ ⌊ d₂ ⌋
    ⌊ ci ⌋        = CH.ci
    ⌊ ck ⌋        = CH.ck
    ⌊ cs ⌋        = CH.cs
    ⌊ box d ⌋     = CH.box ⌊ d ⌋
    ⌊ cdist ⌋     = CH.cdist
    ⌊ cup ⌋       = CH.cup
    ⌊ cdown ⌋     = CH.cdown
    ⌊ cpair ⌋     = CH.cpair
    ⌊ cfst ⌋      = CH.cfst
    ⌊ csnd ⌋      = CH.csnd
    ⌊ tt ⌋        = CH.tt
