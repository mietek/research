import A202103.GenericRenaming
import A202103.GenericSubstitution

module A202103.GenericSubstitution-Part2 {s} {S : Set s}
  {rs : A202103.GenericRenaming.RenSpec {S = S}}
  (ss : A202103.GenericSubstitution.SubSpec rs) where

open import A202103.Prelude
open import A202103.Category
open import A202103.List

open A202103.GenericRenaming
open RenSpec rs
open A202103.GenericSubstitution rs
open SubSpec ss

------------------------------------------------------------------------------

-- To substitute the topmost index in a term.
cut : ∀ {Γ A C} → Γ ⊢ A → Γ , A ⊢ C → Γ ⊢ C
cut t = sub (conss ids t)

-- Compatibility of cutting terms and renaming a term.
comp-cut-ren : ∀ {Γ Γ′ A C} (η : Γ′ ⊒ Γ) (t₁ : Γ ⊢ A) (t₂ : Γ , A ⊢ C) →
               cut (ren η t₁) (ren (liftr η) t₂) ≡ ren η (cut t₁ t₂)
comp-cut-ren η t₁ t₂ = comp-sub-subr (conss ids (ren η t₁)) (liftr η) t₂ ⁻¹
                     ⋮ flip sub t₂ & fu′ (fu λ { top → refl
                                               ; (pop x) → lid-subr η x
                                                          ⋮ rid-rens η x ⁻¹
                                               })
                     ⋮ comp-sub-rens η (conss ids t₁) t₂

------------------------------------------------------------------------------

-- To compose substitutions, or to substitute (all indices in) a substitution.
-- XXX: Was `_●_` with reversed arguments.
subs : ∀ {Γ Ξ Ψ} → Γ ⊢* Ξ → Ξ ⊢* Ψ → Γ ⊢* Ψ
subs σ′ σ top     = sub σ′ (σ top)
subs σ′ σ (pop x) = subs σ′ (σ ∘ pop) x

------------------------------------------------------------------------------

-- Compatibility of substituting an index and composing substitutions.
-- XXX: Was `get●`.
comp-subi-subs : ∀ {Γ Ξ Ψ A} (σ′ : Γ ⊢* Ξ) (σ : Ξ ⊢* Ψ) (x : Ψ ∋ A) →
                 subi (subs σ′ σ) x ≡ sub σ′ (subi σ x)
comp-subi-subs σ′ σ top     = refl
comp-subi-subs σ′ σ (pop x) = comp-subi-subs σ′ (σ ∘ pop) x

------------------------------------------------------------------------------

-- Compatibility of composing substitutions and substituting a renaming.
-- XXX: Was `comp●◑`.
comp-subs-subr : ∀ {Γ Ξ Ξ′ Ψ A} (σ′ : Γ ⊢* Ξ′) (η : Ξ′ ⊒ Ξ) (σ : Ξ ⊢* Ψ) (x : Ψ ∋ A) →
                 subs (subr σ′ η) σ x ≡ subs σ′ (rens η σ) x
comp-subs-subr σ′ η σ top     = comp-sub-subr σ′ η (σ top)
comp-subs-subr σ′ η σ (pop x) = comp-subs-subr σ′ η (σ ∘ pop) x

-- Compatibility of composing substitutions and renaming a substitution.
-- XXX: Was `comp●◐`.
comp-subs-rens : ∀ {Γ Γ′ Ξ Ψ A} (η : Γ′ ⊒ Γ) (σ′ : Γ ⊢* Ξ) (σ : Ξ ⊢* Ψ) (x : Ψ ∋ A) →
                 subs (rens η σ′) σ x ≡ rens η (subs σ′ σ) x
comp-subs-rens η σ′ σ top     = comp-sub-rens η σ′ (σ top)
comp-subs-rens η σ′ σ (pop x) = comp-subs-rens η σ′ (σ ∘ pop) x

-- Compatibility of lifting a substitution and composing substitutions.
comp-lifts-subs : ∀ {Γ Ξ Ψ C A} (σ′ : Γ ⊢* Ξ) (σ : Ξ ⊢* Ψ) (x : Ψ , C ∋ A) →
                  lifts (subs σ′ σ) x ≡ subs (lifts σ′) (lifts σ) x
comp-lifts-subs σ′ σ top     = comp-sub-var (lifts σ′) top ⁻¹
comp-lifts-subs σ′ σ (pop x) = comp-subs-rens pop σ′ σ x ⁻¹
                             ⋮ comp-subs-subr (lifts σ′) pop σ x

------------------------------------------------------------------------------

-- TODO: Kind of like a presheaf...
record SubSpec-Part2 : Set (lsuc s) where
  field
    comp-sub-subs : ∀ {Γ Ξ Ψ A} (σ′ : Γ ⊢* Ξ) (σ : Ξ ⊢* Ψ) (t : Ψ ⊢ A) →
                    sub (subs σ′ σ) t ≡ sub σ′ (sub σ t)

------------------------------------------------------------------------------
