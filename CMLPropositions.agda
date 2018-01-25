module CMLPropositions where

open import Prelude
open import Category
open import List


--------------------------------------------------------------------------------


infixr 8 _⊃_
data Prop : Set
  where
    ι_   : String → Prop
    _⊃_  : Prop → Prop → Prop
    [_]_ : List Prop → Prop → Prop


instance
  PropVar : IsString Prop
  PropVar =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → ι s
      }


--------------------------------------------------------------------------------


record Assert : Set
  where
    constructor ⟪_⊫_⟫
    field
      Γ : List Prop
      A : Prop


--------------------------------------------------------------------------------


injι : ∀ {P₁ P₂} → ι P₁ ≡ ι P₂
                 → P₁ ≡ P₂
injι refl = refl


inj⊃₁ : ∀ {A₁ A₂ B₁ B₂} → A₁ ⊃ B₁ ≡ A₂ ⊃ B₂
                        → A₁ ≡ A₂
inj⊃₁ refl = refl


inj⊃₂ : ∀ {A₁ A₂ B₁ B₂} → A₁ ⊃ B₁ ≡ A₂ ⊃ B₂
                        → B₁ ≡ B₂
inj⊃₂ refl = refl


inj[]₁ : ∀ {Ψ₁ Ψ₂ A₁ A₂} → [ Ψ₁ ] A₁ ≡ [ Ψ₂ ] A₂
                         → Ψ₁ ≡ Ψ₂
inj[]₁ refl = refl


inj[]₂ : ∀ {Ψ₁ Ψ₂ A₁ A₂} → [ Ψ₁ ] A₁ ≡ [ Ψ₂ ] A₂
                         → A₁ ≡ A₂
inj[]₂ refl = refl


mutual
  _≟ₚ_ : (A₁ A₂ : Prop) → Dec (A₁ ≡ A₂)
  (ι P₁)      ≟ₚ (ι P₂)      with P₁ ≟ₛ P₂
  ...                        | yes refl = yes refl
  ...                        | no P₁≢P₂ = no (P₁≢P₂ ∘ injι)
  (ι P₁)      ≟ₚ (A₂ ⊃ B₂)   = no (\ ())
  (ι P₁)      ≟ₚ ([ Ψ₂ ] A₂) = no (\ ())
  (A₁ ⊃ B₁)   ≟ₚ (ι P₂)      = no (\ ())
  (A₁ ⊃ B₁)   ≟ₚ (A₂ ⊃ B₂)   with A₁ ≟ₚ A₂ | B₁ ≟ₚ B₂
  ...                        | yes refl | yes refl = yes refl
  ...                        | yes refl | no B₁≢B₂ = no (B₁≢B₂ ∘ inj⊃₂)
  ...                        | no A₁≢A₂ | _        = no (A₁≢A₂ ∘ inj⊃₁)
  (A₁ ⊃ B₁)   ≟ₚ ([ Ψ₂ ] A₂) = no (\ ())
  ([ Ψ₁ ] A₁) ≟ₚ (ι P₂)      = no (\ ())
  ([ Ψ₁ ] A₁) ≟ₚ (A₂ ⊃ B₂)   = no (\ ())
  ([ Ψ₁ ] A₁) ≟ₚ ([ Ψ₂ ] A₂) with Ψ₁ ≟ₚₛ Ψ₂ | A₁ ≟ₚ A₂
  ...                        | yes refl | yes refl = yes refl
  ...                        | yes refl | no A₁≢A₂ = no (A₁≢A₂ ∘ inj[]₂)
  ...                        | no Ψ₁≢Ψ₂ | _        = no (Ψ₁≢Ψ₂ ∘ inj[]₁)

  _≟ₚₛ_ : (Ξ₁ Ξ₂ : List Prop) → Dec (Ξ₁ ≡ Ξ₂)
  ∙         ≟ₚₛ ∙         = yes refl
  ∙         ≟ₚₛ (Ξ₂ , A₂) = no (λ ())
  (Ξ₁ , A₁) ≟ₚₛ ∙         = no (λ ())
  (Ξ₁ , A₁) ≟ₚₛ (Ξ₂ , A₂) with Ξ₁ ≟ₚₛ Ξ₂ | A₁ ≟ₚ A₂
  ...                     | yes refl | yes refl = yes refl
  ...                     | yes refl | no A₁≢A₂ = no (A₁≢A₂ ∘ inj,₂)
  ...                     | no Ξ₁≢Ξ₂ | _        = no (Ξ₁≢Ξ₂ ∘ inj,₁)


--------------------------------------------------------------------------------
