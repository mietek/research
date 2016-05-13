module AbelChapmanExtended.RenamingLemmas.Convergence where

open import AbelChapmanExtended.Convergence
open import AbelChapmanExtended.Normalization
open import AbelChapmanExtended.OPE
open import AbelChapmanExtended.Renaming
open import AbelChapmanExtended.RenamingLemmas.Normalization1
open import AbelChapmanExtended.RenamingLemmas.Normalization2
open import AbelChapmanExtended.Syntax




⇓ren-readback-ne : ∀ {Δ Δ′ a} (η : Δ′ ⊇ Δ) (v : Ne Val Δ a) {v′ : Ne Nf Δ a} →
                   readback-ne v ⇓ v′ → readback-ne (ren-nev η v) ⇓ ren-nen η v′
⇓ren-readback-ne η v ⇓v′ = ⇓≈subst (⇓map (ren-nen η) ⇓v′) (ren-readback-ne η v)


⇓ren-π₁-reduce : ∀ {Δ Δ′ a b} (η : Δ′ ⊇ Δ) (v : Val Δ (a ∧ b)) {v′ : Val Δ a} →
                 π₁-reduce v ⇓ v′ → π₁-reduce (ren-val η v) ⇓ ren-val η v′
⇓ren-π₁-reduce η v ⇓v′ = ⇓≈subst (⇓map (ren-val η) ⇓v′) (ren-π₁-reduce η v)


⇓ren-π₂-reduce : ∀ {Δ Δ′ a b} (η : Δ′ ⊇ Δ) (v : Val Δ (a ∧ b)) {v′ : Val Δ b} →
                 π₂-reduce v ⇓ v′ → π₂-reduce (ren-val η v) ⇓ ren-val η v′
⇓ren-π₂-reduce η v ⇓v′ = ⇓≈subst (⇓map (ren-val η) ⇓v′) (ren-π₂-reduce η v)
