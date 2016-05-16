module AbelChapmanExtended.RenamingLemmas.Semantics where

open import Data.Product using (_,_)
open import Data.Unit using () renaming (tt to unit)
open import Relation.Binary.PropositionalEquality using (sym ; subst)

open import AbelChapmanExtended.Convergence
open import AbelChapmanExtended.Normalization
open import AbelChapmanExtended.OPE
open import AbelChapmanExtended.RenamingLemmas.Convergence
open import AbelChapmanExtended.RenamingLemmas.OPE
open import AbelChapmanExtended.Renaming
open import AbelChapmanExtended.Semantics
open import AbelChapmanExtended.Syntax




ren-V⟦⟧ : ∀ {Δ Δ′} (a : Ty) (η : Δ′ ⊇ Δ) (v : Val Δ a) →
          V⟦ a ⟧ v → V⟦ a ⟧ (ren-val η v)
ren-V⟦⟧ ⊥       η (ne v)  (v′ , ⇓v′)     = (ren-nen η v′ , ⇓ren-readback-ne η v ⇓v′)
ren-V⟦⟧ (a ∨ b)  η (ne v)  (w , ⇓w)       =
      let w′  = ren-nen η w
          ⇓w′ = ⇓ren-readback-ne η v ⇓w
      in  (w′ , ⇓w′)
ren-V⟦⟧ (a ∨ b)  η (inl v) (w , ⇓w , ⟦w⟧) =
      let w′             = ren-val η w
          ⇓w′            = ⇓map (ren-val η) ⇓w
          ⟦w⟧′           = ren-V⟦⟧ a η w ⟦w⟧
      in  (w′ , ⇓w′ , ⟦w⟧′)
ren-V⟦⟧ (a ∨ b)  η (inr v) (w , ⇓w , ⟦w⟧) =
      let w′             = ren-val η w
          ⇓w′            = ⇓map (ren-val η) ⇓w
          ⟦w⟧′           = ren-V⟦⟧ b η w ⟦w⟧
      in  (w′ , ⇓w′ , ⟦w⟧′)
ren-V⟦⟧ (a ⇒ b) η v       ⟦v⟧            = λ η′ w ⟦w⟧ →
      let (vw , ⇓vw , ⟦vw⟧) = ⟦v⟧ (η′ • η) w ⟦w⟧
          ⇓vw′              = subst (λ v′ → β-reduce v′ w ⇓ vw)
                                    (sym (ren-val-• η′ η v))
                                    ⇓vw
      in  (vw , ⇓vw′ , ⟦vw⟧)
ren-V⟦⟧ (a ∧ b)  η v       (c₁ , c₂)      =
      let (v₁ , ⇓v₁ , ⟦v₁⟧) = c₁
          (v₂ , ⇓v₂ , ⟦v₂⟧) = c₂
          v₁′               = ren-val η v₁
          v₂′               = ren-val η v₂
          ⇓v₁′              = ⇓ren-π₁-reduce η v ⇓v₁
          ⇓v₂′              = ⇓ren-π₂-reduce η v ⇓v₂
          ⟦v₁⟧′             = ren-V⟦⟧ a η v₁ ⟦v₁⟧
          ⟦v₂⟧′             = ren-V⟦⟧ b η v₂ ⟦v₂⟧
      in  (v₁′ , ⇓v₁′ , ⟦v₁⟧′) , (v₂′ , ⇓v₂′ , ⟦v₂⟧′)
ren-V⟦⟧ ⊤       η v       unit           = unit


ren-E⟦⟧ : ∀ {Γ Δ Δ′} (η : Δ′ ⊇ Δ) (ρ : Env Δ Γ) →
          E⟦ Γ ⟧ ρ → E⟦ Γ ⟧ (ren-env η ρ)
ren-E⟦⟧ η ∅       unit        = unit
ren-E⟦⟧ η (ρ , v) (⟦ρ⟧ , ⟦v⟧) = (ren-E⟦⟧ η ρ ⟦ρ⟧ , ren-V⟦⟧ _ η v ⟦v⟧)
