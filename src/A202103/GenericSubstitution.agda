import A202103.GenericRenaming

module A202103.GenericSubstitution {s} {S : Set s}
  (rs : A202103.GenericRenaming.RenSpec {S = S}) where

open import A202103.Prelude
open import A202103.Category
open import A202103.List

open A202103.GenericRenaming
open RenSpec rs

------------------------------------------------------------------------------

-- To weaken a term.
wk : ∀ {Γ A C} → Γ ⊢ A → Γ , C ⊢ A
wk = ren (wkr idr)

-- Compatibility of weakening a term and renaming a term.
comp-wk-ren : ∀ {Γ Γ′ A C} (η : Γ′ ⊒ Γ) (t : Γ ⊢ A) →
              wk {C = C} (ren η t) ≡ ren (liftr η) (wk t)
comp-wk-ren η t = comp-ren-renr (wkr idr) η t ⁻¹
                ⋮ comp-ren-renr (liftr η) (wkr idr) t

-- XXX
lift-wk : ∀ {Γ A C D} → Γ , C ⊢ A → (Γ , D) , C ⊢ A
lift-wk = ren (liftr (wkr idr))

-- XXX
comp-ren-liftr : ∀ {Γ Γ′ Γ″ A C} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (t : Γ , C ⊢ A) →
                 ren (liftr (renr η′ η)) t ≡ ren (liftr η′) (ren (liftr η) t)
comp-ren-liftr η′ η t = flip ren t & fu′ (fu (comp-liftr-renr η′ η))
                      ⋮ comp-ren-renr (liftr η′) (liftr η) t

-- XXX
comp-lift-wk-ren : ∀ {Γ Γ′ A C D} (η : Γ′ ⊒ Γ) (t : Γ , C ⊢ A) →
                   lift-wk {D = D} (ren (liftr η) t) ≡ ren (liftr (liftr η)) (lift-wk t)
comp-lift-wk-ren η t = comp-ren-liftr pop η t ⁻¹
                     ⋮ comp-ren-liftr (liftr η) pop t

------------------------------------------------------------------------------

-- Higher-order representation of (a simultaneous) substitution.
infix 3 _⊢*_
_⊢*_ : List S → List S → Set s
Γ ⊢* Ξ = ∀ {A} → Ξ ∋ A → Γ ⊢ A

-- To obtain the result of substituting the topmost index.
heads : ∀ {Γ Ξ A} → Γ ⊢* Ξ , A → Γ ⊢ A
heads σ = σ top

-- To shorten a substitution.
-- XXX: Was `unskip⊢*`.
tails : ∀ {Γ Ξ A} → Γ ⊢* Ξ , A → Γ ⊢* Ξ
tails σ = σ ∘ pop

-- To construct an empty substitution.
nils : ∀ {Γ} → Γ ⊢* ·
nils ()

-- To extend a substitution.
conss : ∀ {Γ Ξ A} → Γ ⊢* Ξ → Γ ⊢ A → Γ ⊢* Ξ , A
conss σ t top     = t
conss σ t (pop x) = σ x

------------------------------------------------------------------------------

-- To substitute (all indices in) a renaming, or to compose a substitution with a renaming.
-- XXX: Was `_◑_` with reversed arguments.
subr : ∀ {Γ Ξ Ξ′} → Γ ⊢* Ξ′ → Ξ′ ⊒ Ξ → Γ ⊢* Ξ
subr σ η = σ ∘ η

-- To rename (all indices in) a substitution, or to compose a renaming with a substitution.
-- XXX: Was `_◐_` with reversed arguments.
rens : ∀ {Γ Γ′ Ξ} → Γ′ ⊒ Γ → Γ ⊢* Ξ → Γ′ ⊢* Ξ
rens η σ top     = ren η (σ top)
rens η σ (pop x) = rens η (σ ∘ pop) x

-- Identity of substitution.
ids : ∀ {Γ} → Γ ⊢* Γ
ids = var

-- To weaken a substitution.
-- XXX: Was `skip⊢*`.
wks : ∀ {Γ Ξ C} → Γ ⊢* Ξ → Γ , C ⊢* Ξ
wks σ = rens (wkr idr) σ

-- To lift a substitution.
-- XXX: Was `keep⊢*`.
lifts : ∀ {Γ Ξ C} → Γ ⊢* Ξ → Γ , C ⊢* Ξ , C
lifts σ top     = var top
lifts σ (pop x) = wks σ x

-- To turn a renaming into a substitution.
vars : ∀ {Γ Γ′} → Γ′ ⊒ Γ → Γ′ ⊢* Γ
vars η top     = var (η top)
vars η (pop x) = vars (η ∘ pop) x

-- XXX
-- ids : ∀ {Γ} → Γ ⊢* Γ
-- ids = vars idr

------------------------------------------------------------------------------

-- To substitute an index.
subi : ∀ {Γ Ξ A} → Γ ⊢* Ξ → Ξ ∋ A → Γ ⊢ A
subi σ x = σ x

-- Compatibility of substituting an index and substituting a renaming.
-- XXX: Was `get◑`.
comp-subi-subr : ∀ {Γ Ξ Ξ′ A} (σ : Γ ⊢* Ξ′) (η : Ξ′ ⊒ Ξ) (x : Ξ ∋ A) →
                 subi (subr σ η) x ≡ subi σ (reni η x)
comp-subi-subr σ η x = refl

-- Compatibility of substituting an index and renaming a substitution.
-- XXX: Was `get◐`.
comp-subi-rens : ∀ {Γ Γ′ Ξ A} (η : Γ′ ⊒ Γ) (σ : Γ ⊢* Ξ) (x : Ξ ∋ A) →
                 subi (rens η σ) x ≡ ren η (subi σ x)
comp-subi-rens η σ top     = refl
comp-subi-rens η σ (pop x) = comp-subi-rens η (σ ∘ pop) x

-- Identity of substituting an index.
id-subi : ∀ {Γ A} (x : Γ ∋ A) →
          subi ids x ≡ ids x
id-subi x = refl
-- id-subi top     = refl
-- id-subi (pop x) = comp-subi-subr ids pop x
--                 ⋮ hm pop x

------------------------------------------------------------------------------

-- Compatibility of renaming a substitution and composing renamings.
-- XXX: Was `comp◐○`.
comp-rens-renr : ∀ {Γ Γ′ Γ″ Ξ A} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (σ : Γ ⊢* Ξ) (x : Ξ ∋ A) →
                 rens (renr η′ η) σ x ≡ rens η′ (rens η σ) x
comp-rens-renr η′ η σ top     = comp-ren-renr η′ η (σ top)
comp-rens-renr η′ η σ (pop x) = comp-rens-renr η′ η (σ ∘ pop) x

-- Compatibility of substituting a renaming and renaming a substitution.
-- XXX: Was `comp◑◐`.
comp-subr-rens : ∀ {Γ Γ′ Ξ Ξ′ A} (η′ : Γ′ ⊒ Γ) (σ : Γ ⊢* Ξ′) (η : Ξ′ ⊒ Ξ) (x : Ξ ∋ A) →
                 subr (rens η′ σ) η x ≡ rens η′ (subr σ η) x
comp-subr-rens η′ σ η top     = comp-subi-rens η′ σ (η top)
comp-subr-rens η′ σ η (pop x) = comp-subr-rens η′ σ (η ∘ pop) x

------------------------------------------------------------------------------

{-
-- XXX
ugh₁ : ∀ {Γ Γ′ A} (η : Γ′ ⊒ Γ) (x : Γ ∋ A) →
       vars η x ≡ var (η x)
ugh₁ η top     = refl
ugh₁ η (pop x) = ugh₁ (η ∘ pop) x

-- XXX
ugh₂ : ∀ {Γ Γ′ Γ″ A} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (x : Γ ∋ A) →
       vars (renr η′ η) x ≡ vars η′ (η x)
ugh₂ η′ η top     = ugh₁ η′ (η top) ⁻¹
ugh₂ η′ η (pop x) = ugh₂ η′ (η ∘ pop) x

-- XXX
ugh₃ : ∀ {Γ Γ′ Γ″ A} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (x : Γ ∋ A) →
       vars (renr η′ η) x ≡ ren η′ (vars η x)
ugh₃ η′ η top     = comp-ren-var η′ (η top) ⁻¹
ugh₃ η′ η (pop x) = ugh₃ η′ (η ∘ pop) x

-- XXX
ugh₄ : ∀ {Γ Γ′ Γ″ A} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (x : Γ ∋ A) →
       vars η′ (η x) ≡ ren η′ (vars η x)
ugh₄ η′ η x = ugh₂ η′ η x ⁻¹ ⋮ ugh₃ η′ η x
-}

------------------------------------------------------------------------------

-- Left identity of substituting a renaming.
-- XXX: Was `rid-◑`.
lid-subr : ∀ {Γ Γ′ A} (η : Γ′ ⊒ Γ) (x : Γ ∋ A) →
           subr ids η x ≡ vars η x
lid-subr η top     = refl
-- lid-subr η top     = ugh₁ idr (η top)
lid-subr η (pop x) = lid-subr (η ∘ pop) x

-- Right identity of substituting a renaming.
-- XXX: Was `lid◑`.
rid-subr : ∀ {Γ Ξ A} (σ : Γ ⊢* Ξ) (x : Ξ ∋ A) →
           subr σ idr x ≡ σ x
rid-subr σ x = refl

-- Left identity of renaming a substitution.
lid-rens : ∀ {Γ Ξ A} (σ : Γ ⊢* Ξ) (x : Ξ ∋ A) →
           rens idr σ x ≡ σ x
lid-rens σ top     = id-ren (σ top)
lid-rens σ (pop x) = lid-rens (σ ∘ pop) x

-- Right identity of renaming a substitution.
-- XXX: Was `lid-◐`.
rid-rens : ∀ {Γ Γ′ A} (η : Γ′ ⊒ Γ) (x : Γ ∋ A) →
           rens η ids x ≡ vars η x
rid-rens η top     = comp-ren-var η top
rid-rens η (pop x) = ha (ha′ ( rens η ⦂ (_ ⊢* _ → _ ⊢* _)
                             & fu′ (fu (λ x → lid-subr pop x
                                             ⋮ rid-rens pop x ⁻¹)))) x
                   ⋮ comp-rens-renr η pop ids x ⁻¹
                   ⋮ rid-rens (η ∘ pop) x

------------------------------------------------------------------------------

-- Identity of lifting a substitution.
id-lifts : ∀ {Γ C A} (x : Γ , C ∋ A) →
           lifts ids x ≡ ids x
id-lifts top     = refl
id-lifts (pop x) = comp-subi-rens pop ids x
                 ⋮ comp-ren-var pop x
--                 ⋮ ugh₄ pop idr x ⁻¹

-- Compatibility of lifting a substitution and substituting a renaming.
comp-lifts-subr : ∀ {Γ Ξ Ξ′ A C} (σ : Γ ⊢* Ξ′) (η : Ξ′ ⊒ Ξ) (x : Ξ , C ∋ A) →
                  lifts (subr σ η) x ≡ subr (lifts σ) (liftr η) x
comp-lifts-subr σ η top     = refl
comp-lifts-subr σ η (pop x) = comp-subr-rens pop σ η x ⁻¹

-- Compatibility of lifting a substitution and renaming a substitution.
comp-lifts-rens : ∀ {Γ Γ′ Ξ A C} (η : Γ′ ⊒ Γ) (σ : Γ ⊢* Ξ) (x : Ξ , C ∋ A) →
                  lifts (rens η σ) x ≡ rens (liftr η) (lifts σ) x
comp-lifts-rens η σ top     = comp-ren-var (liftr η) top ⁻¹
comp-lifts-rens η σ (pop x) = comp-rens-renr pop η σ x ⁻¹
                            ⋮ comp-rens-renr (liftr η) pop σ x

------------------------------------------------------------------------------

-- TODO: Not a presheaf?
record SubSpec : Set (lsuc s) where
  field
    sub : ∀ {Γ Ξ A} → Γ ⊢* Ξ → Ξ ⊢ A → Γ ⊢ A

    id-sub : ∀ {Γ A} (t : Γ ⊢ A) →
             sub ids t ≡ t

    comp-sub-subr : ∀ {Γ Ξ Ξ′ A} (σ : Γ ⊢* Ξ′) (η : Ξ′ ⊒ Ξ) (t : Ξ ⊢ A) →
                    sub (subr σ η) t ≡ sub σ (ren η t)

    comp-sub-rens : ∀ {Γ Γ′ Ξ A} (η : Γ′ ⊒ Γ) (σ : Γ ⊢* Ξ) (t : Ξ ⊢ A) →
                    sub (rens η σ) t ≡ ren η (sub σ t)

    comp-sub-var : ∀ {Γ Ξ A} (σ : Γ ⊢* Ξ) (x : Ξ ∋ A) →
                   sub σ (var x) ≡ subi σ x

------------------------------------------------------------------------------
