module StdIPLLemmasScratch where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open GetAllList
open import AllListLemmas
open GetsAllList
open import StdIPL
open import StdIPLLemmas


--------------------------------------------------------------------------------
{-
                       rens (drop η) ξ ≡ (wks ∘ rens η) ξ                       drop-wks-rens

                   subs (rens η ids) ξ ≡ rens η ξ                               lid-rens-subs
                   subs (rens η ξ) ids ≡ rens η ξ                               rid-rens-subs

                      subs (wks ids) ξ ≡ wks ξ                                  lid-wks-subs
                      subs (wks ξ) ids ≡ wks ξ                                  rid-wks-subs
-}
--------------------------------------------------------------------------------


drop-wks-rens : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                             → rens (drop {A = A} η) ξ ≡ wks (rens η ξ)
drop-wks-rens η ∙       = refl
drop-wks-rens η (ξ , 𝒟) = _,_ & drop-wks-rens η ξ
                              ⊗ ( (\ η′ → ren (drop η′) 𝒟) & rid∘⊇ η ⁻¹
                                ⋮ comp-ren η (drop id⊇) 𝒟
                                )


--------------------------------------------------------------------------------


lid-rens-subs : ∀ {Γ Γ′ Ξ} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                           → subs (rens η ids) ξ ≡ rens η ξ
lid-rens-subs η ξ = comp-rens-subs η ids ξ ⋮ (rens η & lid-subs ξ)


rid-rens-subs : ∀ {Γ Γ′ Ξ} → (η : Γ′ ⊇ Γ) (ξ : Γ ⊢⋆ Ξ)
                           → subs (rens η ξ) ids ≡ rens η ξ
rid-rens-subs η ξ = comp-rens-subs η ξ ids ⋮ (rens η & rid-subs ξ)


lid-wks-subs : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                         → subs (wks {A} ids) ξ ≡ wks ξ
lid-wks-subs ξ = lid-rens-subs (drop id⊇) ξ


rid-wks-subs : ∀ {Γ Ξ A} → (ξ : Γ ⊢⋆ Ξ)
                         → subs (wks {A} ξ) ids ≡ wks ξ
rid-wks-subs ξ = rid-rens-subs (drop id⊇) ξ


--------------------------------------------------------------------------------
