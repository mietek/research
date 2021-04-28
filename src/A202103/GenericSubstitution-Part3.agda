import A202103.GenericRenaming
import A202103.GenericSubstitution
import A202103.GenericSubstitution-Part2

module A202103.GenericSubstitution-Part3 {s} {S : Set s}
  {rs : A202103.GenericRenaming.RenSpec {S = S}}
  {ss : A202103.GenericSubstitution.SubSpec rs}
  (ss2 : A202103.GenericSubstitution-Part2.SubSpec-Part2 ss) where

open import A202103.Prelude
open import A202103.Category
open import A202103.List

open A202103.GenericRenaming
open RenSpec rs
open A202103.GenericSubstitution rs
open SubSpec ss
open A202103.GenericSubstitution-Part2 ss
open SubSpec-Part2 ss2

------------------------------------------------------------------------------

-- Left identity of composing substitutions.
lid-subs : ∀ {Γ Ξ A} (σ : Γ ⊢* Ξ) (x : Ξ ∋ A) →
           subs ids σ x ≡ σ x
lid-subs σ top     = id-sub (σ top)
lid-subs σ (pop x) = lid-subs (σ ∘ pop) x

-- Right identity of composing substitutions.
rid-subs : ∀ {Γ Ξ A} (σ : Γ ⊢* Ξ) (x : Ξ ∋ A) →
           subs σ ids x ≡ σ x
rid-subs σ top     = comp-sub-var σ top
rid-subs σ (pop x) = ha (ha′ ( subs σ ⦂ (_ ⊢* _ → _ ⊢* _)
                             & fu′ (fu λ x → lid-subr pop x
                                            ⋮ rid-rens pop x ⁻¹))) x
                   ⋮ comp-subs-subr σ pop ids x ⁻¹
                   ⋮ rid-subs (subr σ pop) x

-- Associativity of composing substitutions.
ass-subs : ∀ {Γ Ξ Ψ Φ A} (σ″ : Γ ⊢* Ξ) (σ′ : Ξ ⊢* Ψ) (σ : Ψ ⊢* Φ) (x : Φ ∋ A) →
           subs (subs σ″ σ′) σ x ≡ subs σ″ (subs σ′ σ) x
ass-subs σ″ σ′ σ top     = comp-sub-subs σ″ σ′ (σ top)
ass-subs σ″ σ′ σ (pop x) = ass-subs σ″ σ′ (σ ∘ pop) x

-- Category of substitutions.
SUB : Category (List S) _⊢*_
SUB = record
        { id   = ids
        ; _∘_  = subs
        ; lid∘ = λ σ → fu′ (fu (lid-subs σ))
        ; rid∘ = λ σ → fu′ (fu (rid-subs σ))
        ; ass∘ = λ σ″ σ′ σ → fu′ (fu (ass-subs σ″ σ′ σ))
        }

-- Substituting a term yields a presheaf in the category of substitutions.
Sub : ∀ A → Presheaf SUB (_⊢ A)
Sub A = record
          { φ     = sub
          ; idφ   = fu id-sub
          ; compφ = λ η η′ → fu (comp-sub-subs η′ η)
          }

------------------------------------------------------------------------------
