module IPLStandardDerivationsWithAFriendlyFish where

open import Prelude
open import Category
open import List
open import ListLemmas
open import ListConcatenation
open import AllList
open import IPLPropositions


--------------------------------------------------------------------------------


data Lost (X : Set) : Set
  where
    ∙   : Lost X
    _,_ : X → Lost X → Lost X

infix 4 _∈_
data _∈_ {X} : X → Lost X → Set
  where
    zero : ∀ {Ξ A} → A ∈ A , Ξ

    suc : ∀ {B Ξ A} → A ∈ Ξ
                    → A ∈ B , Ξ


--------------------------------------------------------------------------------


infix 3 _⊢_true
data _⊢_true : Lost Prop → Prop → Set
  where
    var : ∀ {A Γ} → A ∈ Γ
                  → Γ ⊢ A true

    lam : ∀ {A B Γ} → A , Γ ⊢ B true
                    → Γ ⊢ A ⊃ B true

    app : ∀ {A B Γ} → Γ ⊢ A ⊃ B true → Γ ⊢ A true
                    → Γ ⊢ B true


-- infix 3 _⊢_alltrue
-- _⊢_alltrue : Lost Prop → Lost Prop → Set
-- Γ ⊢ Ξ alltrue = All (Γ ⊢_true) Ξ


--------------------------------------------------------------------------------


-- _‘_ : ∀ {X} → X → Lost X
--             → Lost X
-- A ‘ ∙       = ∙ , A
-- A ‘ (Ξ , B) = (A ‘ Ξ) , B
--
-- _+_ : ∀ {X} → Lost X → Lost X
--             → Lost X
-- ∙       + Ψ = Ψ
-- (Ξ , A) + Ψ = Ξ + (A ‘ Ψ)

_+_ : ∀ {X} → Lost X → Lost X
            → Lost X
Ξ + ∙       = Ξ
Ξ + (A , Ψ) = (A , Ξ) + Ψ

Ren : Lost Prop → Lost Prop → Set
Ren Γ Γ′ = ∀ {A} → A ∈ Γ → A ∈ Γ′

Sub : Lost Prop → Lost Prop → Set
Sub Ξ Γ = ∀ {A} → A ∈ Ξ → Γ ⊢ A true

Shub : Lost Prop → Lost Prop → Set
Shub Ξ Γ = ∀ Ψ → Sub (Ξ + Ψ) (Γ + Ψ)

lift : ∀ {A Γ Ξ} → Shub Ξ Γ → Shub (A , Ξ) (A , Γ)
lift {A} ξ = λ Ψ i → ξ (A , Ψ) i

shub : ∀ {Γ Ξ A} → Shub Ξ Γ → Ξ ⊢ A true
                 → Γ ⊢ A true
shub ξ (var i)     = ξ ∙ i
shub ξ (lam {A} 𝒟) = lam (shub (lift ξ) 𝒟)
shub ξ (app 𝒟 ℰ)   = app (shub ξ 𝒟) (shub ξ ℰ)
