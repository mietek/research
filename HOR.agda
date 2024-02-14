----------------------------------------------------------------------------------------------------

-- higher-order renamings

module HOR {𝓍} {X : Set 𝓍} where

open import DBI public
open import GAN
import FOR


----------------------------------------------------------------------------------------------------

infix 4 _⊑_
_⊑_ : List X → List X → Set 𝓍
Γ ⊑ Γ′ = ∀ {A} → Γ ∋ A → Γ′ ∋ A


----------------------------------------------------------------------------------------------------

-- first-order renamings are isomorphic to higher-order renamings

private
  to : ∀ {Γ Γ′} → Γ FOR.⊆ Γ′ → Γ ⊑ Γ′
  to (j FOR.∷ js) zero    = j
  to (j FOR.∷ js) (suc i) = to js i

  from : ∀ {Γ Γ′} → Γ ⊑ Γ′ → Γ FOR.⊆ Γ′
  from {[]}    ρ = FOR.[]
  from {A ∷ Γ} ρ = ρ zero FOR.∷ from (ρ ∘ suc)

  from∘to : ∀ {Γ Γ′} (is : Γ FOR.⊆ Γ′) → (from ∘ to) is ≡ is
  from∘to FOR.[]       = refl
  from∘to (i FOR.∷ is) = (i FOR.∷_) & from∘to is

  pointwise-to∘from : ∀ {Γ Γ′} (ρ : Γ ⊑ Γ′) → (∀ {A : X} (i : Γ ∋ A) → (to ∘ from) ρ i ≡ ρ i)
  pointwise-to∘from {A ∷ Γ} ρ zero    = refl
  pointwise-to∘from {A ∷ Γ} ρ (suc i) = pointwise-to∘from (ρ ∘ suc) i

  module _ (⚠ : FunExt) where
    ⚠′ = implify ⚠

    to∘from : ∀ {Γ Γ′} (ρ : Γ ⊑ Γ′) → (to ∘ from) ρ ≡ ρ :> (Γ ⊑ Γ′)
    to∘from ρ = ⚠′ (⚠ (pointwise-to∘from ρ))

    FOR≃HOR : ∀ {Γ Γ′} → (Γ FOR.⊆ Γ′) ≃ (Γ ⊑ Γ′)
    FOR≃HOR = record
                { to      = to
                ; from    = from
                ; from∘to = from∘to
                ; to∘from = to∘from
                }

  -- TODO: name?
  extfrom : ∀ {Γ Γ′} (ρ ρ′ : Γ ⊑ Γ′) → (∀ {A : X} (i : Γ ∋ A) → ρ i ≡ ρ′ i) → from ρ ≡ from ρ′
  extfrom {[]}    ρ ρ′ peq = refl
  extfrom {A ∷ Γ} ρ ρ′ peq = FOR._∷_ & peq zero ⊗ extfrom (ρ ∘ suc) (ρ′ ∘ suc) (peq ∘ suc)


----------------------------------------------------------------------------------------------------
