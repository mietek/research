module CMTTTypes where

open import Prelude
open import Category
open import Vec
open import AllVec
open import CMTTScopes


--------------------------------------------------------------------------------


mutual
  infixr 8 _⊃_
  data Type : Set
    where
      ι_   : String → Type
      _⊃_  : Type → Type → Type
      [_]_ : ∀ {g} → Types g → Type → Type


  Types : Nat → Set
  Types g = Vec Type g


instance
  TypeVar : IsString Type
  TypeVar =
    record
      { Constraint = \ s → 𝟙
      ; fromString = \ s → ι s
      }


--------------------------------------------------------------------------------


record Assert (g : Nat) : Set
  where
    constructor ⟪_⊫_⟫
    field
      Γ : Types g
      A : Type


Asserts : ∀ {d} → Scopes d → Set
Asserts σ = All Assert σ


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


inj[]₀ : ∀ {n₁ n₂ A₁ A₂} → {Ψ₁ : Types n₁} {Ψ₂ : Types n₂}
                         → [ Ψ₁ ] A₁ ≡ [ Ψ₂ ] A₂
                         → n₁ ≡ n₂
inj[]₀ refl = refl


inj[]₁ : ∀ {n A₁ A₂} → {Ψ₁ Ψ₂ : Types n}
                     → [ Ψ₁ ] A₁ ≡ [ Ψ₂ ] A₂
                     → Ψ₁ ≡ Ψ₂
inj[]₁ refl = refl


inj[]₂ : ∀ {n A₁ A₂} → {Ψ₁ Ψ₂ : Types n}
                     → [ Ψ₁ ] A₁ ≡ [ Ψ₂ ] A₂
                     → A₁ ≡ A₂
inj[]₂ refl = refl


mutual
  _≟ₚ_ : (A₁ A₂ : Type) → Dec (A₁ ≡ A₂)
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
  [_]_ {g₁} Ψ₁ A₁ ≟ₚ [_]_ {g₂} Ψ₂ A₂ with g₁ ≟ₙ g₂
  [_]_ {g}  Ψ₁ A₁ ≟ₚ [_]_ {.g} Ψ₂ A₂ | yes refl with Ψ₁ ≟ₚₛ Ψ₂ | A₁ ≟ₚ A₂
  [_]_ {g}  Ψ  A  ≟ₚ [_]_ {.g} .Ψ .A | yes refl | yes refl | yes refl = yes refl
  [_]_ {g}  Ψ  A₁ ≟ₚ [_]_ {.g} .Ψ A₂ | yes refl | yes refl | no A₁≢A₂ = no (A₁≢A₂ ∘ inj[]₂)
  [_]_ {g}  Ψ₁ A₁ ≟ₚ [_]_ {.g} Ψ₂ A₂ | yes refl | no Ψ₁≢Ψ₂ | _        = no (Ψ₁≢Ψ₂ ∘ inj[]₁)
  [_]_ {g₁} Ψ₁ A₁ ≟ₚ [_]_ {g₂} Ψ₂ A₂ | no g₁≢g₂ = no (g₁≢g₂ ∘ inj[]₀)

  _≟ₚₛ_ : ∀ {n} → (Ξ₁ Ξ₂ : Types n) → Dec (Ξ₁ ≡ Ξ₂)
  ∙         ≟ₚₛ ∙         = yes refl
  (Ξ₁ , A₁) ≟ₚₛ (Ξ₂ , A₂) with Ξ₁ ≟ₚₛ Ξ₂ | A₁ ≟ₚ A₂
  ...                     | yes refl | yes refl = yes refl
  ...                     | yes refl | no A₁≢A₂ = no (A₁≢A₂ ∘ inj,₂)
  ...                     | no Ξ₁≢Ξ₂ | _        = no (Ξ₁≢Ξ₂ ∘ inj,₁)


--------------------------------------------------------------------------------


_⊃⋯⊃_ : ∀ {n} → Types n → Type → Type
∙       ⊃⋯⊃ A = A
(Ξ , B) ⊃⋯⊃ A = Ξ ⊃⋯⊃ (B ⊃ A)


--------------------------------------------------------------------------------
