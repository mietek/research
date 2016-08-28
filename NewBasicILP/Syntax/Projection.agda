module NewBasicILP.Syntax.Projection where

open import Common.UntypedContext public

import NewBasicILP.UntypedSyntax.ClosedHilbertSequential as CHS
import NewBasicILP.UntypedSyntax.ClosedHilbert as CH


-- Projection of types and derivations to a form parametrised by a closed, untyped representation of syntax.

module ClosedHilbertSequential where
  open import NewBasicILP.Syntax.ClosedHilbertSequential

  mutual
    ⌊_⌋ᵀ : Ty → CHS.Ty
    ⌊ α P ⌋ᵀ      = CHS.α P
    ⌊ A ▻ B ⌋ᵀ    = ⌊ A ⌋ᵀ CHS.▻ ⌊ B ⌋ᵀ
    ⌊ [ ps ] A ⌋ᵀ = CHS.[ ⌊ ps ⌋⊦ᴿ ] ⌊ A ⌋ᵀ -- NOTE: Must use ⌊_⌋⊦ᴿ here.
    ⌊ A ∧ B ⌋ᵀ    = ⌊ A ⌋ᵀ CHS.∧ ⌊ B ⌋ᵀ
    ⌊ ⊤ ⌋ᵀ       = CHS.⊤

    ⌊_⌋ᵀ⋆ : Cx Ty → Cx CHS.Ty
    ⌊ ⌀ ⌋ᵀ⋆     = ⌀
    ⌊ Γ , A ⌋ᵀ⋆ = ⌊ Γ ⌋ᵀ⋆ , ⌊ A ⌋ᵀ

    ⌊_⌋∈ : ∀ {Ξ A} → A ∈ Ξ → ⌊ A ⌋ᵀ ∈ ⌊ Ξ ⌋ᵀ⋆
    ⌊ top ⌋∈   = top
    ⌊ pop i ⌋∈ = pop ⌊ i ⌋∈

    ⌊_⌋⊦ : ∀ {Ξ} → ⊦⊢ Ξ → CHS.⊦⊢ ⌊ Ξ ⌋ᵀ⋆
    ⌊ nil ⌋⊦       = CHS.nil
    ⌊ mp i j ts ⌋⊦ = CHS.mp ⌊ i ⌋∈ ⌊ j ⌋∈ ⌊ ts ⌋⊦
    ⌊ ci ts ⌋⊦     = CHS.ci ⌊ ts ⌋⊦
    ⌊ ck ts ⌋⊦     = CHS.ck ⌊ ts ⌋⊦
    ⌊ cs ts ⌋⊦     = CHS.cs ⌊ ts ⌋⊦
    ⌊ nec ps ts ⌋⊦ = {!CHS.nec ⌊ ps ⌋⊦ ⌊ ts ⌋⊦!} -- NOTE: Fills then fails.
    ⌊ cdist ts ⌋⊦  = {!CHS.cdist ⌊ ts ⌋⊦!}       -- NOTE: Does not fill.
    ⌊ cup ts ⌋⊦    = {!CHS.cup ⌊ ts ⌋⊦!}         -- NOTE: Fills then fails.
    ⌊ cdown ts ⌋⊦  = CHS.cdown ⌊ ts ⌋⊦
    ⌊ cpair ts ⌋⊦  = CHS.cpair ⌊ ts ⌋⊦
    ⌊ cfst ts ⌋⊦   = CHS.cfst ⌊ ts ⌋⊦
    ⌊ csnd ts ⌋⊦   = CHS.csnd ⌊ ts ⌋⊦
    ⌊ tt ts ⌋⊦     = CHS.tt ⌊ ts ⌋⊦

    ⌊_⌋⊦ᴿ : ∀ {Ξ A} → ⊦⊢ Ξ , A → CHS.Rep
    ⌊ ts ⌋⊦ᴿ = CHS.REP ⌊ ts ⌋⊦

    ⌊_⌋ : ∀ {A} → ⊢ A → CHS.⊢ ⌊ A ⌋ᵀ
    ⌊ Ξ , ts ⌋ = ⌊ Ξ ⌋ᵀ⋆ , ⌊ ts ⌋⊦


-- Projection of types and derivations to a form parametrised by a closed, untyped representation of syntax.

module ClosedHilbert where
  open import NewBasicILP.Syntax.ClosedHilbert

  mutual
    ⌊_⌋ᵀ : Ty → CH.Ty
    ⌊ α P ⌋ᵀ     = CH.α P
    ⌊ A ▻ B ⌋ᵀ   = ⌊ A ⌋ᵀ CH.▻ ⌊ B ⌋ᵀ
    ⌊ [ p ] A ⌋ᵀ = CH.[ CH.REP ⌊ p ⌋ ] ⌊ A ⌋ᵀ -- NOTE: Must not use ⌊_⌋ᴿ here.
    ⌊ A ∧ B ⌋ᵀ   = ⌊ A ⌋ᵀ CH.∧ ⌊ B ⌋ᵀ
    ⌊ ⊤ ⌋ᵀ      = CH.⊤

    ⌊_⌋ : ∀ {A} → ⊢ A → CH.⊢ ⌊ A ⌋ᵀ
    ⌊ app t u ⌋ = CH.app ⌊ t ⌋ ⌊ u ⌋
    ⌊ ci ⌋      = CH.ci
    ⌊ ck ⌋      = CH.ck
    ⌊ cs ⌋      = CH.cs
    ⌊ box p ⌋   = CH.box ⌊ p ⌋
    ⌊ cdist ⌋   = CH.cdist
    ⌊ cup ⌋     = CH.cup
    ⌊ cdown ⌋   = CH.cdown
    ⌊ cpair ⌋   = CH.cpair
    ⌊ cfst ⌋    = CH.cfst
    ⌊ csnd ⌋    = CH.csnd
    ⌊ tt ⌋      = CH.tt

    ⌊_⌋ᴿ : ∀ {A} → ⊢ A → CH.Rep
    ⌊ t ⌋ᴿ = CH.REP ⌊ t ⌋
