----------------------------------------------------------------------------------------------------

-- higher-order renamings

module HOR {𝓍} {X : Set 𝓍} where

open import DBI public
open import GAN
import FOR


----------------------------------------------------------------------------------------------------

infix 4 _⊑_
_⊑_ : Tsil X → Tsil X → Set 𝓍
Γ ⊑ Γ′ = ∀ {A} → Γ ∋ A → Γ′ ∋ A


----------------------------------------------------------------------------------------------------

-- first-order renamings are isomorphic to higher-order renamings

private
  to : ∀ {Γ Γ′} → Γ FOR.⊑ Γ′ → Γ ⊑ Γ′
  to (ρ FOR., j) zero    = j
  to (ρ FOR., j) (wk∋ i) = to ρ i

  from : ∀ {Γ Γ′} → Γ ⊑ Γ′ → Γ FOR.⊑ Γ′
  from {∙}     ρ = FOR.∙
  from {Γ , A} ρ = from (ρ ∘ wk∋) FOR., ρ zero

  from∘to : ∀ {Γ Γ′} (is : Γ FOR.⊑ Γ′) → (from ∘ to) is ≡ is
  from∘to FOR.∙       = refl
  from∘to (ρ FOR., i) = (FOR._, i) & from∘to ρ

  pointwise-to∘from : ∀ {Γ Γ′} (ρ : Γ ⊑ Γ′) → (∀ {A : X} (i : Γ ∋ A) → (to ∘ from) ρ i ≡ ρ i)
  pointwise-to∘from ρ zero    = refl
  pointwise-to∘from ρ (wk∋ i) = pointwise-to∘from (ρ ∘ wk∋) i

  module _ (⚠ : FunExt) where
    ⚠′ = implify ⚠

    to∘from : ∀ {Γ Γ′} (ρ : Γ ⊑ Γ′) → (to ∘ from) ρ ≡ ρ :> (Γ ⊑ Γ′)
    to∘from ρ = ⚠′ (⚠ (pointwise-to∘from ρ))

    FOR≃HOR : ∀ {Γ Γ′} → (Γ FOR.⊑ Γ′) ≃ (Γ ⊑ Γ′)
    FOR≃HOR = record
                { to      = to
                ; from    = from
                ; from∘to = from∘to
                ; to∘from = to∘from
                }

  -- TODO: name?
  extfrom : ∀ {Γ Γ′} (ρ ρ′ : Γ ⊑ Γ′) → (∀ {A : X} (i : Γ ∋ A) → ρ i ≡ ρ′ i) → from ρ ≡ from ρ′
  extfrom {∙}     ρ ρ′ peq = refl
  extfrom {Γ , A} ρ ρ′ peq = FOR._,_ & extfrom (ρ ∘ wk∋) (ρ′ ∘ wk∋) (peq ∘ wk∋) ⊗ peq zero


----------------------------------------------------------------------------------------------------
