module A202103.GenericRenaming {s} {S : Set s} where

open import A202103.Prelude
open import A202103.Category
open import A202103.List

------------------------------------------------------------------------------

-- Higher-order representation of (a simultaneous) renaming.
infix 3 _⊒_
_⊒_ : List S → List S → Set s
Γ′ ⊒ Γ = ∀ {A} → Γ ∋ A → Γ′ ∋ A

-- To obtain the result of renaming the topmost index.
headr : ∀ {Γ Ξ A} → Γ ⊒ Ξ , A → Γ ∋ A
headr η = η top

-- To shorten a renaming.
-- XXX: Was `unskip⊒`.
tailr : ∀ {Γ Ξ A} → Γ ⊒ Ξ , A → Γ ⊒ Ξ
tailr η = η ∘ pop

-- To construct an empty renaming.
nilr : ∀ {Γ} → Γ ⊒ ·
nilr ()

-- To extend a renaming.
consr : ∀ {Γ Ξ A} → Γ ⊒ Ξ → Γ ∋ A → Γ ⊒ Ξ , A
consr η t top     = t
consr η t (pop x) = η x

------------------------------------------------------------------------------

-- Identity of renaming.
idr : ∀ {Γ} → Γ ⊒ Γ
idr = id

-- To compose renamings, or to rename (all indices in) a renaming.
-- XXX: Was `_○_` with reversed arguments.
renr : ∀ {Γ Γ′ Γ″} → Γ″ ⊒ Γ′ → Γ′ ⊒ Γ → Γ″ ⊒ Γ
renr η′ η = η′ ∘ η

-- Left identity of composing renamings.
lid-renr : ∀ {Γ Γ′ A} (η : Γ′ ⊒ Γ) (x : Γ ∋ A) →
           (renr η idr) x ≡ η x
lid-renr η x = refl

-- Right identity of composing renamings.
rid-renr : ∀ {Γ Γ′ A} (η : Γ′ ⊒ Γ) (x : Γ ∋ A) →
           (renr idr η) x ≡ η x
rid-renr η x = refl

-- Associativity of composing renamings.
ass-renr : ∀ {Γ Γ′ Γ″ Γ‴ A} (η″ : Γ‴ ⊒ Γ″) (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (x : Γ ∋ A) →
           renr (renr η″ η′) η x ≡ renr η″ (renr η′ η) x
ass-renr η″ η′ η x = refl

-- Category of renamings.
REN : Category (List S) _⊒_
REN = record
        { id   = idr
        ; _∘_  = renr
        ; lid∘ = λ η → fu′ (fu (lid-renr η))
        ; rid∘ = λ η → fu′ (fu (rid-renr η))
        ; ass∘ = λ η″ η′ η → fu′ (fu (ass-renr η″ η′ η))
        }

-----------------------------------------------------------------------------

-- To rename an index, or monotonicity of `_∋_` wrt. renaming.
reni : ∀ {Γ Γ′ A} → Γ′ ⊒ Γ → Γ ∋ A → Γ′ ∋ A
reni η x = η x

-- Identity of renaming an index.
id-reni : ∀ {Γ A} (x : Γ ∋ A) →
          reni idr x ≡ x
id-reni x = refl

-- Compatibility of renaming an index and composing renamings.
comp-reni-renr : ∀ {Γ Γ′ Γ″ A} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (x : Γ ∋ A) →
                 reni (renr η′ η) x ≡ reni η′ (reni η x)
comp-reni-renr η′ η x = refl

-- Renaming an index yields a presheaf.
Reni : ∀ A → Presheaf REN (_∋ A)
Reni A = record
           { φ     = reni
           ; idφ   = fu id-reni
           ; compφ = λ η η′ → fu (comp-reni-renr η′ η)
           }

------------------------------------------------------------------------------

-- To weaken a renaming.
-- XXX: Was `skip⊒`.
wkr : ∀ {Γ Γ′ C} → Γ′ ⊒ Γ → Γ′ , C ⊒ Γ
wkr η = pop ∘ η

-- To lift a renaming.
-- XXX: Was `keep⊒`.
liftr : ∀ {Γ Γ′ C} → Γ′ ⊒ Γ → Γ′ , C ⊒ Γ , C
liftr η top     = top
liftr η (pop x) = pop (η x)

-- Identity of lifting a renaming.
id-liftr : ∀ {Γ A C} (x : Γ , C ∋ A) →
           liftr idr x ≡ idr x
id-liftr top     = refl
id-liftr (pop x) = refl

-- Compatibility of lifting a renaming and composing renamings.
comp-liftr-renr : ∀ {Γ Γ′ Γ″ A C} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (x : Γ , C ∋ A) →
                  liftr (renr η′ η) x ≡ renr (liftr η′) (liftr η) x
comp-liftr-renr η′ η top     = refl
comp-liftr-renr η′ η (pop x) = refl

------------------------------------------------------------------------------

-- TODO: Close to a presheaf.
record RenSpec : Set (lsuc s) where
  infix 3 _⊢_
  field
    _⊢_ : List S → S → Set s

    ren : ∀ {Γ Γ′ A} → Γ′ ⊒ Γ → Γ ⊢ A → Γ′ ⊢ A

    id-ren : ∀ {Γ A} (t : Γ ⊢ A) →
             ren idr t ≡ t

    comp-ren-renr : ∀ {Γ Γ′ Γ″ A} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (t : Γ ⊢ A) →
                    ren (renr η′ η) t ≡ ren η′ (ren η t)

    var : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A

    comp-ren-var : ∀ {Γ Γ′ A} (η : Γ′ ⊒ Γ) (x : Γ ∋ A) →
                   ren η (var x) ≡ var (reni η x)

------------------------------------------------------------------------------
