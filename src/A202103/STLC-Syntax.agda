module A202103.STLC-Syntax where

open import A202103.Prelude public
open import A202103.Category public
open import A202103.List public
open import A202103.GenericRenaming public
import A202103.GenericSubstitution
import A202103.GenericSubstitution-Part2
import A202103.GenericSubstitution-Part3

------------------------------------------------------------------------------

-- Types.
infixr 7 _⊃_
data Type : Set where
  ◦   : Type
  _⊃_ : Type → Type → Type

-- Intrinsically well-typed terms.
infix 3 _⊢_
data _⊢_ (Γ : List Type) : Type → Set where
  var : ∀ {A} → Γ ∋ A → Γ ⊢ A
  lam : ∀ {A B} → Γ , A ⊢ B → Γ ⊢ A ⊃ B
  app : ∀ {A B} → Γ ⊢ A ⊃ B → Γ ⊢ A → Γ ⊢ B

------------------------------------------------------------------------------

-- To rename (all indices in) a term, or monotonicity of `_⊢_` wrt. renaming.
ren : ∀ {Γ Γ′ A} → Γ′ ⊒ Γ → Γ ⊢ A → Γ′ ⊢ A
ren η (var x)     = var (η x)
ren η (lam t)     = lam (ren (liftr η) t)
ren η (app t₁ t₂) = app (ren η t₁) (ren η t₂)

-- Identity of renaming a term.
id-ren : ∀ {Γ A} (t : Γ ⊢ A) →
         ren idr t ≡ t
id-ren (var x)     = refl
id-ren (lam t)     = lam & ( flip ren t & fu′ (fu id-liftr)
                           ⋮ id-ren t)
id-ren (app t₁ t₂) = app & id-ren t₁ ⊗ id-ren t₂

-- Compatibility of renaming a term and composing renamings.
-- XXX: Was `ren○`.
comp-ren-renr : ∀ {Γ Γ′ Γ″ A} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (t : Γ ⊢ A) →
                ren (renr η′ η) t ≡ ren η′ (ren η t)
comp-ren-renr η′ η (var x)     = refl
comp-ren-renr η′ η (lam t)     = lam & ( flip ren t & fu′ (fu (comp-liftr-renr η′ η))
                                       ⋮ comp-ren-renr (liftr η′) (liftr η) t)
comp-ren-renr η′ η (app t₁ t₂) = app & comp-ren-renr η′ η t₁ ⊗ comp-ren-renr η′ η t₂

-- Renaming a term yields a presheaf.
Ren : ∀ A → Presheaf REN (_⊢ A)
Ren A = record
          { φ     = ren
          ; idφ   = fu id-ren
          ; compφ = λ η η′ → fu (comp-ren-renr η′ η)
          }

private
  -- TODO: Close to a presheaf.
  rs : RenSpec
  rs = record
         { _⊢_           = _⊢_
         ; ren           = ren
         ; id-ren        = id-ren
         ; comp-ren-renr = comp-ren-renr
         ; var           = var
         ; comp-ren-var  = λ η x → refl
         }

------------------------------------------------------------------------------

open A202103.GenericSubstitution rs public

-- To substitute (all indices in) a term, or monotonicity of `_⊢_` wrt. substituting.
sub : ∀ {Γ Ξ A} → Γ ⊢* Ξ → Ξ ⊢ A → Γ ⊢ A
sub σ (var x)     = σ x
sub σ (lam t)     = lam (sub (lifts σ) t)
sub σ (app t₁ t₂) = app (sub σ t₁) (sub σ t₂)

-- Identity of substituting a term.
id-sub : ∀ {Γ A} (t : Γ ⊢ A) →
         sub ids t ≡ t
id-sub (var x)     = refl
id-sub (lam t)     = lam & ( flip sub t & fu′ (fu id-lifts)
                           ⋮ id-sub t)
id-sub (app t₁ t₂) = app & id-sub t₁ ⊗ id-sub t₂

-- Compatibility of substituting a term and substituting a renaming.
-- XXX: Was `sub◑`.
comp-sub-subr : ∀ {Γ Ξ Ξ′ A} (σ : Γ ⊢* Ξ′) (η : Ξ′ ⊒ Ξ) (t : Ξ ⊢ A) →
                sub (subr σ η) t ≡ sub σ (ren η t)
comp-sub-subr σ η (var x)     = refl
comp-sub-subr σ η (lam t)     = lam & ( flip sub t & fu′ (fu (comp-lifts-subr σ η))
                                      ⋮ comp-sub-subr (lifts σ) (liftr η) t)
comp-sub-subr σ η (app t₁ t₂) = app & comp-sub-subr σ η t₁ ⊗ comp-sub-subr σ η t₂

-- Compatibility of substituting a term and renaming a substitution.
-- XXX: Was `sub◐`.
comp-sub-rens : ∀ {Γ Γ′ Ξ A} (η : Γ′ ⊒ Γ) (σ : Γ ⊢* Ξ) (t : Ξ ⊢ A) →
                sub (rens η σ) t ≡ ren η (sub σ t)
comp-sub-rens η σ (var x)     = comp-subi-rens η σ x
comp-sub-rens η σ (lam t)     = lam & ( flip sub t & fu′ (fu (comp-lifts-rens η σ))
                                      ⋮ comp-sub-rens (liftr η) (lifts σ) t)
comp-sub-rens η σ (app t₁ t₂) = app & comp-sub-rens η σ t₁ ⊗ comp-sub-rens η σ t₂

-- TODO: Not a presheaf?
private
  ss : SubSpec
  ss = record
         { sub           = sub
         ; id-sub        = id-sub
         ; comp-sub-subr = comp-sub-subr
         ; comp-sub-rens = comp-sub-rens
         ; comp-sub-var  = λ σ x → refl
         }

------------------------------------------------------------------------------

open A202103.GenericSubstitution-Part2 ss public

-- Compatibility of substituting a term and composing substitutions.
-- XXX: Was `sub●`.
comp-sub-subs : ∀ {Γ Ξ Ψ A} (σ′ : Γ ⊢* Ξ) (σ : Ξ ⊢* Ψ) (t : Ψ ⊢ A) →
                sub (subs σ′ σ) t ≡ sub σ′ (sub σ t)
comp-sub-subs σ′ σ (var x)     = comp-subi-subs σ′ σ x
comp-sub-subs σ′ σ (lam t)     = lam & ( flip sub t & fu′ (fu (comp-lifts-subs σ′ σ))
                                       ⋮ comp-sub-subs (lifts σ′) (lifts σ) t
                                       )
comp-sub-subs σ′ σ (app t₁ t₂) = app & comp-sub-subs σ′ σ t₁ ⊗ comp-sub-subs σ′ σ t₂

-- TODO: Kind of like a presheaf...
private
  ss2 : SubSpec-Part2
  ss2 = record
          { comp-sub-subs = comp-sub-subs
          }

------------------------------------------------------------------------------

open A202103.GenericSubstitution-Part3 ss2 public

------------------------------------------------------------------------------
