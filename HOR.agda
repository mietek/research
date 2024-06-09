----------------------------------------------------------------------------------------------------

-- higher-order renamings

module A202401.HOR {𝓍} {X : Set 𝓍} where

open import A202401.DBI public
open import A202401.GAN
import A202401.FOR as FOR
open FOR using (∙ ; _,_)


----------------------------------------------------------------------------------------------------

infix 4 _⊑_
_⊑_ : Rist X → Rist X → Set 𝓍
Γ ⊑ Γ′ = ∀ {A} → Γ ∋ A → Γ′ ∋ A


----------------------------------------------------------------------------------------------------

-- first-order renamings are isomorphic to higher-order renamings

private
  to : ∀ {Γ Γ′} → Γ FOR.⊑ Γ′ → Γ ⊑ Γ′
  to (ϱ , j) zero    = j
  to (ϱ , j) (wk∋ i) = to ϱ i

  from : ∀ {Γ Γ′} → Γ ⊑ Γ′ → Γ FOR.⊑ Γ′
  from {∙}     ϱ = ∙
  from {Γ , A} ϱ = from (ϱ ∘ wk∋) , ϱ zero

  from∘to : ∀ {Γ Γ′} (is : Γ FOR.⊑ Γ′) → (from ∘ to) is ≡ is
  from∘to ∙       = refl
  from∘to (ϱ , i) = (_, i) & from∘to ϱ

  pointwise-to∘from : ∀ {Γ Γ′} (ϱ : Γ ⊑ Γ′) → (∀ {A : X} (i : Γ ∋ A) → (to ∘ from) ϱ i ≡ ϱ i)
  pointwise-to∘from ϱ zero    = refl
  pointwise-to∘from ϱ (wk∋ i) = pointwise-to∘from (ϱ ∘ wk∋) i

  module _ (⚠ : FunExt) where
    ⚠′ = implify ⚠

    to∘from : ∀ {Γ Γ′} (ϱ : Γ ⊑ Γ′) → (to ∘ from) ϱ ≡ ϱ :> (Γ ⊑ Γ′)
    to∘from ϱ = ⚠′ (⚠ (pointwise-to∘from ϱ))

    FOR≃HOR : ∀ {Γ Γ′} → (Γ FOR.⊑ Γ′) ≃ (Γ ⊑ Γ′)
    FOR≃HOR = record
                { to      = to
                ; from    = from
                ; from∘to = from∘to
                ; to∘from = to∘from
                }

  -- TODO: name?
  extfrom : ∀ {Γ Γ′} (ϱ ϱ′ : Γ ⊑ Γ′) → (∀ {A : X} (i : Γ ∋ A) → ϱ i ≡ ϱ′ i) → from ϱ ≡ from ϱ′
  extfrom {∙}     ϱ ϱ′ peq = refl
  extfrom {Γ , A} ϱ ϱ′ peq = _,_ & extfrom (ϱ ∘ wk∋) (ϱ′ ∘ wk∋) (peq ∘ wk∋) ⊗ peq zero


----------------------------------------------------------------------------------------------------
