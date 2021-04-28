module A202103.S4-Syntax-DualContext where

open import A202103.Prelude public
open import A202103.Category public
open import A202103.List public
open import A202103.GenericRenaming public
import A202103.GenericSubstitution

------------------------------------------------------------------------------

infixr 7 _⊃_
data Type : Set where
  ◦   : Type
  _⊃_ : Type → Type → Type
  □_  : Type → Type

infix 5 _true
record Truth : Set where
  constructor _true
  field
    T : Type

{-# DISPLAY Truth.T A = A #-}

infix 5 _valid
record Validity : Set where
  constructor _valid
  field
    V : Type

{-# DISPLAY Validity.V A = A #-}

infix 3 _⁏_⊢_
data _⁏_⊢_ (Δ : List Validity) (Γ : List Truth) : Truth → Set where
  var    : ∀ {A} → Γ ∋ A true → Δ ⁏ Γ ⊢ A true
  lam    : ∀ {A B} → Δ ⁏ Γ , A true ⊢ B true → Δ ⁏ Γ ⊢ A ⊃ B true
  app    : ∀ {A B} → Δ ⁏ Γ ⊢ A ⊃ B true → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ ⊢ B true
  mvar   : ∀ {A} → Δ ∋ A valid → Δ ⁏ Γ ⊢ A true
  box    : ∀ {A} → Δ ⁏ · ⊢ A true → Δ ⁏ Γ ⊢ □ A true
  letbox : ∀ {A C} → Δ ⁏ Γ ⊢ □ A true → Δ , A valid ⁏ Γ ⊢ C true → Δ ⁏ Γ ⊢ C true

infix 3 _⊢_
_⊢_ : List Validity → Validity → Set
Δ ⊢ A valid = Δ ⁏ · ⊢ A true

------------------------------------------------------------------------------

ren : ∀ {Δ Γ Γ′ A} → Γ′ ⊒ Γ → Δ ⁏ Γ ⊢ A true → Δ ⁏ Γ′ ⊢ A true
ren η (var x)        = var (η x)
ren η (lam t)        = lam (ren (liftr η) t)
ren η (app t₁ t₂)    = app (ren η t₁) (ren η t₂)
ren η (mvar x)       = mvar x
ren η (box t)        = box t
ren η (letbox t₁ t₂) = letbox (ren η t₁) (ren η t₂)

id-ren : ∀ {Δ Γ A} (t : Δ ⁏ Γ ⊢ A true) →
         ren idr t ≡ t
id-ren (var x)        = refl
id-ren (lam t)        = lam & ( flip ren t & fu′ (fu id-liftr)
                              ⋮ id-ren t)
id-ren (app t₁ t₂)    = app & id-ren t₁ ⊗ id-ren t₂
id-ren (mvar x)       = refl
id-ren (box t)        = refl
id-ren (letbox t₁ t₂) = letbox & id-ren t₁ ⊗ id-ren t₂

comp-ren-renr : ∀ {Δ Γ Γ′ Γ″ A} (η′ : Γ″ ⊒ Γ′) (η : Γ′ ⊒ Γ) (t : Δ ⁏ Γ ⊢ A true) →
                ren (renr η′ η) t ≡ ren η′ (ren η t)
comp-ren-renr η′ η (var x)        = refl
comp-ren-renr η′ η (lam t)        = lam & ( flip ren t & fu′ (fu (comp-liftr-renr η′ η))
                                          ⋮ comp-ren-renr (liftr η′) (liftr η) t)
comp-ren-renr η′ η (app t₁ t₂)    = app & comp-ren-renr η′ η t₁ ⊗ comp-ren-renr η′ η t₂
comp-ren-renr η′ η (mvar x)       = refl
comp-ren-renr η′ η (box t)        = refl
comp-ren-renr η′ η (letbox t₁ t₂) = letbox & comp-ren-renr η′ η t₁ ⊗ comp-ren-renr η′ η t₂

Ren : ∀ Δ A → Presheaf REN (λ Γ → Δ ⁏ Γ ⊢ A true)
Ren Δ A = record
            { φ     = ren
            ; idφ   = fu id-ren
            ; compφ = λ η η′ → fu (comp-ren-renr η′ η)
            }

private
  rs : ∀ Δ → RenSpec
  rs Δ = record
           { _⊢_           = λ { Γ (A true) → Δ ⁏ Γ ⊢ A true }
           ; ren           = ren
           ; id-ren        = id-ren
           ; comp-ren-renr = comp-ren-renr
           ; var           = var
           ; comp-ren-var  = λ η x → refl
           }

------------------------------------------------------------------------------

mren : ∀ {Δ Δ′ Γ A} → Δ′ ⊒ Δ → Δ ⁏ Γ ⊢ A true → Δ′ ⁏ Γ ⊢ A true
mren η (var x)        = var x
mren η (lam t)        = lam (mren η t)
mren η (app t₁ t₂)    = app (mren η t₁) (mren η t₂)
mren η (mvar x)       = mvar (η x)
mren η (box t)        = box (mren η t)
mren η (letbox t₁ t₂) = letbox (mren η t₁) (mren (liftr η) t₂)

id-mren : ∀ {Δ Γ A} (t : Δ ⁏ Γ ⊢ A true) →
          mren idr t ≡ t
id-mren (var x)        = refl
id-mren (lam t)        = lam & id-mren t
id-mren (app t₁ t₂)    = app & id-mren t₁ ⊗ id-mren t₂
id-mren (mvar x)       = refl
id-mren (box t)        = box & id-mren t
id-mren (letbox t₁ t₂) = letbox & id-mren t₁
                                ⊗ ( flip mren t₂ & fu′ (fu id-liftr)
                                  ⋮ id-mren t₂)

comp-mren-renr : ∀ {Δ Δ′ Δ″ Γ A} (η′ : Δ″ ⊒ Δ′) (η : Δ′ ⊒ Δ) (t : Δ ⁏ Γ ⊢ A true) →
                 mren (renr η′ η) t ≡ mren η′ (mren η t)
comp-mren-renr η′ η (var x)       = refl
comp-mren-renr η′ η (lam t)        = lam & comp-mren-renr η′ η t
comp-mren-renr η′ η (app t₁ t₂)    = app & comp-mren-renr η′ η t₁ ⊗ comp-mren-renr η′ η t₂
comp-mren-renr η′ η (mvar x)       = refl
comp-mren-renr η′ η (box t)        = box & comp-mren-renr η′ η t
comp-mren-renr η′ η (letbox t₁ t₂) = letbox & comp-mren-renr η′ η t₁
                                            ⊗ ( flip mren t₂ & fu′ (fu (comp-liftr-renr η′ η))
                                              ⋮ comp-mren-renr (liftr η′) (liftr η) t₂)

MRen : ∀ Γ A → Presheaf REN (λ Δ → Δ ⁏ Γ ⊢ A true)
MRen Γ A = record
             { φ     = mren
             ; idφ   = fu id-mren
             ; compφ = λ η η′ → fu (comp-mren-renr η′ η)
             }

private
  mrs : ∀ Γ → RenSpec
  mrs Γ = record
            { _⊢_           = λ { Δ (A valid) → Δ ⁏ Γ ⊢ A true }
            ; ren           = mren
            ; id-ren        = id-mren
            ; comp-ren-renr = comp-mren-renr
            ; var           = mvar
            ; comp-ren-var  = λ η x → refl
            }

------------------------------------------------------------------------------

module TruthSubstitution {Δ} = A202103.GenericSubstitution (rs Δ)

infix 3 _⁏_⊢*_
_⁏_⊢*_ : List Validity → List Truth → List Truth → Set
Δ ⁏ Γ ⊢* Ξ = TruthSubstitution._⊢*_ {Δ} Γ Ξ

open TruthSubstitution public
  hiding (_⊢*_)

------------------------------------------------------------------------------

module ValiditySubstitution {Γ} = A202103.GenericSubstitution (mrs Γ)

infix 3 _⊢*_
_⊢*_ : List Validity → List Validity → Set
Δ ⊢* Ξ = ValiditySubstitution._⊢*_ {·} Δ Ξ

--open VS public
--  using ()
--  renaming
--    ( wk to mwk
--    ; comp-wk-ren to comp-mwk-mren
--    ; liftr-wk to liftr-mwk
--    ; comp-ren-liftr to comp-mren-liftr
--    ; comp-liftr-wk-ren to comp-liftr-mwk-mren
--    ; heads to headms
--    ; tails to tailms
--    ; nils to nilms
--    ; conss to consms
--    ; subr to msubmr
--    ; rens to mrenms
--    ; ids to idms
--    ; wks to mwkms
--    ; lifts to mliftms
--    ; vars to mvarms
--    ; subi to msubmi
--    ; id-subi to id-msubmi
--    ; comp-subi-subr to comp-msubmi-msubmr
--    ; comp-subi-rens to comp-msubmi-mrenms
--    ; comp-rens-renr to comp-mrenms-renr
--    ; comp-subr-rens to comp-msubmr-mrenms
--    ; lid-subr to lid-msubmr
--    ; rid-subr to rid-msubmr
--    ; lid-rens to lid-mrenms
--    ; rid-rens to rid-mrenms
--    ; id-lifts to id-mliftms
--    ; comp-lifts-subr to comp-mliftms-msubmr
--    ; comp-lifts-rens to comp-mliftms-mrenms
--    ; SubSpec to MSubSpec
--    )

------------------------------------------------------------------------------

mwk : ∀ {Δ Γ A C} → Δ ⁏ Γ ⊢ A → Δ , C ⁏ Γ ⊢ A
mwk = ValiditySubstitution.wk

comp-mwk-mren : ∀ {Δ Δ′ Γ A C} (η : Δ′ ⊒ Δ) (t : Δ ⁏ Γ ⊢ A) →
                mwk {C = C} (mren η t) ≡ mren (liftr η) (mwk t)
comp-mwk-mren = ValiditySubstitution.comp-wk-ren

-- liftr-mwk : ∀ {Δ Γ A C D} → Δ , C ⁏ Γ ⊢ A → (Δ , D) , C ⁏ Γ ⊢ A
-- liftr-mwk = ValiditySubstitution.liftr-wk

-- comp-mren-liftr : ∀ {Δ Δ′ Δ″ Γ A C} (η′ : Δ″ ⊒ Δ′) (η : Δ′ ⊒ Δ) (t : Δ , C ⁏ Γ ⊢ A) →
--                   mren (liftr (renr η′ η)) t ≡ mren (liftr η′) (mren (liftr η) t)
-- comp-mren-liftr = ValiditySubstitution.comp-ren-liftr

-- comp-liftr-mwk-mren : ∀ {Δ Δ′ Γ A C D} (η : Δ′ ⊒ Δ) (t : Δ , C ⁏ Γ ⊢ A) →
--                       liftr-mwk {D = D} (mren (liftr η) t) ≡ mren (liftr (liftr η)) (liftr-mwk t)
-- comp-liftr-mwk-mren = ValiditySubstitution.comp-liftr-wk-ren

-- ------------------------------------------------------------------------------

-- headms : ∀ {Δ Ξ A} → Δ ⊢* Ξ , A → Δ ⊢ A
-- headms = ValiditySubstitution.heads

-- tailms : ∀ {Δ Ξ A} → Δ ⊢* Ξ , A → Δ ⊢* Ξ
-- tailms = ValiditySubstitution.tails

-- nilms : ∀ {Δ} → Δ ⊢* ·
-- nilms = ValiditySubstitution.nils

-- consms : ∀ {Δ Ξ A} → Δ ⊢* Ξ → Δ ⊢ A → Δ ⊢* Ξ , A
-- consms = ValiditySubstitution.conss

-- ------------------------------------------------------------------------------

-- msubmr : ∀ {Δ Ξ Ξ′} → Δ ⊢* Ξ′ → Ξ′ ⊒ Ξ → Δ ⊢* Ξ
-- msubmr = ValiditySubstitution.subr

-- mrenms : ∀ {Δ Δ′ Ξ} → Δ′ ⊒ Δ → Δ ⊢* Ξ → Δ′ ⊢* Ξ
-- mrenms = ValiditySubstitution.rens

-- idms : ∀ {Δ} → Δ ⊢* Δ
-- idms = ValiditySubstitution.ids

-- mwkms : ∀ {Δ Ξ C} → Δ ⊢* Ξ → Δ , C ⊢* Ξ
-- mwkms = ValiditySubstitution.wks

-- mliftms : ∀ {Δ Ξ C} → Δ ⊢* Ξ → Δ , C ⊢* Ξ , C
-- mliftms = ValiditySubstitution.lifts

-- mvarms : ∀ {Δ Δ′} → Δ′ ⊒ Δ → Δ′ ⊢* Δ
-- mvarms = ValiditySubstitution.vars

-- ------------------------------------------------------------------------------

-- msubmi : ∀ {Δ Ξ A} → Δ ⊢* Ξ → Ξ ∋ A → Δ ⊢ A
-- msubmi = ValiditySubstitution.subi

-- -- id-msubmi : ∀ {Δ A} (x : Δ ∋ A) →
-- --            msubmi idms x ≡ mvar x
-- -- id-msubmi = {!ValiditySubstitution.id-subi!}

-- comp-msubmi-msubmr : ∀ {Δ Ξ Ξ′ A} (σ : Δ ⊢* Ξ′) (η : Ξ′ ⊒ Ξ) (x : Ξ ∋ A) →
--                      msubmi (msubmr σ η) x ≡ msubmi σ (reni η x)
-- comp-msubmi-msubmr = ValiditySubstitution.comp-subi-subr

-- comp-msubmi-mrenms : ∀ {Δ Δ′ Ξ A} (η : Δ′ ⊒ Δ) (σ : Δ ⊢* Ξ) (x : Ξ ∋ A) →
--                      msubmi (mrenms η σ) x ≡ mren η (msubmi σ x)
-- comp-msubmi-mrenms = ValiditySubstitution.comp-subi-rens

-- ------------------------------------------------------------------------------

-- comp-mrenms-renr : ∀ {Δ Δ′ Δ″ Ξ A} (η′ : Δ″ ⊒ Δ′) (η : Δ′ ⊒ Δ) (σ : Δ ⊢* Ξ) (x : Ξ ∋ A) →
--                    mrenms (renr η′ η) σ x ≡ mrenms η′ (mrenms η σ) x
-- comp-mrenms-renr = ValiditySubstitution.comp-rens-renr

-- comp-msubmr-mrenms : ∀ {Δ Δ′ Ξ Ξ′ A} (η′ : Δ′ ⊒ Δ) (σ : Δ ⊢* Ξ′) (η : Ξ′ ⊒ Ξ) (x : Ξ ∋ A) →
--                      msubmr (mrenms η′ σ) η x ≡ mrenms η′ (msubmr σ η) x
-- comp-msubmr-mrenms = ValiditySubstitution.comp-subr-rens

-- ------------------------------------------------------------------------------

-- lid-msubmr : ∀ {Δ Δ′ A} (η : Δ′ ⊒ Δ) (x : Δ ∋ A) →
--              msubmr idms η x ≡ mvarms η x
-- lid-msubmr = ValiditySubstitution.lid-subr

-- rid-msubmr : ∀ {Δ Ξ A} (σ : Δ ⊢* Ξ) (x : Ξ ∋ A) →
--              msubmr σ idr x ≡ σ x
-- rid-msubmr = ValiditySubstitution.rid-subr

-- lid-mrenms : ∀ {Δ Ξ A} (σ : Δ ⊢* Ξ) (x : Ξ ∋ A) →
--              mrenms idr σ x ≡ σ x
-- lid-mrenms = ValiditySubstitution.lid-rens

-- rid-mrenms : ∀ {Δ Δ′ A} (η : Δ′ ⊒ Δ) (x : Δ ∋ A) →
--              mrenms η idms x ≡ mvarms η x
-- rid-mrenms = ValiditySubstitution.rid-rens

-- ------------------------------------------------------------------------------

-- id-mliftms : ∀ {Δ C A} (x : Δ , C ∋ A) →
--              mliftms idms x ≡ idms x
-- id-mliftms = ValiditySubstitution.id-lifts

-- comp-mliftms-msubmr : ∀ {Δ Ξ Ξ′ A C} (σ : Δ ⊢* Ξ′) (η : Ξ′ ⊒ Ξ) (x : Ξ , C ∋ A) →
--                       mliftms (msubmr σ η) x ≡ msubmr (mliftms σ) (liftr η) x
-- comp-mliftms-msubmr = ValiditySubstitution.comp-lifts-subr

-- comp-mliftms-mrenms : ∀ {Δ Δ′ Ξ A C} (η : Δ′ ⊒ Δ) (σ : Δ ⊢* Ξ) (x : Ξ , C ∋ A) →
--                       mliftms (mrenms η σ) x ≡ mrenms (liftr η) (mliftms σ) x
-- comp-mliftms-mrenms = ValiditySubstitution.comp-lifts-rens

-- ------------------------------------------------------------------------------

-- mrens : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊒ Δ → Δ ⁏ Γ ⊢* Ξ → Δ′ ⁏ Γ ⊢* Ξ
-- mrens η σ top     = mren η (σ top)
-- mrens η σ (pop x) = mrens η (σ ∘ pop) x

-- mwks : ∀ {Δ Γ Ξ C} → Δ ⁏ Γ ⊢* Ξ → Δ , C valid ⁏ Γ ⊢* Ξ
-- mwks σ = mrens (wkr idr) σ

-- mlifts : ∀ {Δ Γ Ξ C} → Δ ⁏ Γ ⊢* Ξ → Δ , C valid ⁏ Γ ⊢* Ξ , C true
-- mlifts σ top     = mvar top
-- mlifts σ (pop x) = mwks σ x

-- ------------------------------------------------------------------------------

-- comp-subi-mrens : ∀ {Δ Δ′ Γ Ξ A} (η : Δ′ ⊒ Δ) (σ : Δ ⁏ Γ ⊢* Ξ) (x : Ξ ∋ A) →
--                   subi (mrens η σ) x ≡ mren η (subi σ x)
-- comp-subi-mrens η σ top     = refl
-- comp-subi-mrens η σ (pop x) = comp-subi-mrens η (σ ∘ pop) x

-- ------------------------------------------------------------------------------

-- comp-mrens-renr : ∀ {Δ″ Δ′ Δ Γ Ξ A} (η′ : Δ″ ⊒ Δ′) (η : Δ′ ⊒ Δ) (σ : Δ ⁏ Γ ⊢* Ξ) (x : Ξ ∋ A) →
--                   mrens (renr η′ η) σ x ≡ mrens η′ (mrens η σ) x
-- comp-mrens-renr η′ η σ top     = comp-mren-renr η′ η (σ top)
-- comp-mrens-renr η′ η σ (pop x) = comp-mrens-renr η′ η (σ ∘ pop) x

-- comp-subr-mrens : ∀ {Δ Δ′ Γ Ξ Ξ′ A} (η′ : Δ′ ⊒ Δ) (σ : Δ ⁏ Γ ⊢* Ξ′) (η : Ξ′ ⊒ Ξ) (x : Ξ ∋ A) →
--                   subr (mrens η′ σ) η x ≡ mrens η′ (subr σ η) x
-- comp-subr-mrens η′ σ η top     = comp-subi-mrens η′ σ (η top)
-- comp-subr-mrens η′ σ η (pop x) = comp-subr-mrens η′ σ (η ∘ pop) x

-- ------------------------------------------------------------------------------

-- comp-mlifts-subr : ∀ {Δ Γ Ξ Ξ′ A C} (σ : Δ ⁏ Γ ⊢* Ξ′) (η : Ξ′ ⊒ Ξ) (x : Ξ , C ∋ A) →
--                    mlifts (subr σ η) x ≡ subr (mlifts σ) (liftr η) x
-- comp-mlifts-subr σ η top     = refl
-- comp-mlifts-subr σ η (pop x) = comp-subr-mrens pop σ η x ⁻¹

-- comp-mlifts-mrens : ∀ {Δ Δ′ Γ Ξ A C} (η : Δ′ ⊒ Δ) (σ : Δ ⁏ Γ ⊢* Ξ) (x : Ξ , C ∋ A) →
--                     mlifts (mrens η σ) x ≡ mrens (liftr η) (mlifts σ) x
-- comp-mlifts-mrens η σ top     = refl -- Or, comp-mren-mvar (liftr η) top ⁻¹
-- comp-mlifts-mrens η σ (pop x) = comp-mrens-renr pop η σ x ⁻¹
--                               ⋮ comp-mrens-renr (liftr η) pop σ x

-- {-
-- comp-lifts-mrens : ∀ {Δ Δ′ Γ Ξ A C} (η : Δ′ ⊒ Δ) (σ : Δ ⁏ Γ ⊢* Ξ) (x : Ξ , C ∋ A) →
--                    lifts (mrens η σ) x ≡ mrens η (lifts σ) x
-- comp-lifts-mrens η σ top     = refl
-- comp-lifts-mrens η σ (pop x) = {!!}
-- -}

-- ------------------------------------------------------------------------------

-- lid-mrens : ∀ {Δ Γ Ξ A} (σ : Δ ⁏ Γ ⊢* Ξ) (x : Ξ ∋ A) →
--             mrens idr σ x ≡ σ x
-- lid-mrens σ top     = id-mren (σ top)
-- lid-mrens σ (pop x) = lid-mrens (σ ∘ pop) x

-- -- subr (mrens η′ σ) η x ≡ ren η (mrens η′ σ x)


-- rid-mrens : ∀ {Δ Δ′ Γ A} (η : Δ′ ⊒ Δ) (x : Γ ∋ A) →
--             mrens η ids x ≡ ids x
-- rid-mrens η top     = refl
-- rid-mrens η (pop x) = comp-subr-mrens η ids pop x ⁻¹
--                     ⋮ {!!}
-- -- rid-mrens η (pop x) = comp-subr-mrens η ids pop x ⁻¹
-- --                     ⋮ {!!}
-- --                     ⋮ ren pop & rid-mrens η x
-- --                     ⋮ comp-subi-rens pop ids x ⁻¹
-- --                     ⋮ rid-rens pop x

-- {-
-- mrens η ids (pop x)
-- mrens η (ids ∘ pop) x

-- ren pop (mren η ids x)
--   by IH under congruence
-- ren pop (ids x)
--   by comp-subi-rens pop ids x ⁻¹
-- rens pop ids x
--   by rid-rens pop x
-- vars pop x
-- -}


-- ------------------------------------------------------------------------------

-- sub : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢* Ξ → Δ ⁏ Ξ ⊢ A true → Δ ⁏ Γ ⊢ A true
-- sub σ (var x)       = σ x
-- sub σ (lam t)        = lam (sub (lifts σ) t)
-- sub σ (app t₁ t₂)    = app (sub σ t₁) (sub σ t₂)
-- sub σ (mvar x)       = mvar x
-- sub σ (box t)        = box t
-- sub σ (letbox t₁ t₂) = letbox (sub σ t₁) (sub (mwks σ) t₂)

-- id-sub : ∀ {Δ Γ A} (t : Δ ⁏ Γ ⊢ A) →
--          sub ids t ≡ t
-- id-sub (var x)        = refl
-- id-sub (lam t)        = lam & ( flip sub t & fu′ (fu id-lifts)
--                               ⋮ id-sub t
--                               )
-- id-sub (app t₁ t₂)    = app & id-sub t₁ ⊗ id-sub t₂
-- id-sub (mvar x)       = refl
-- id-sub (box t)        = box & refl
-- id-sub (letbox t₁ t₂) = letbox & id-sub t₁
--                                ⊗ ( flip sub t₂ & fu′ (fu (rid-mrens pop))
--                                  ⋮ id-sub t₂)

-- -- -- -- -- -- -- -- -- -- rid-mrens : mrens η ids ≡ ids
-- -- -- -- -- -- -- -- -- --       mrens pop ids ≡ ids
-- -- -- -- -- -- -- -- -- --            mwks ids ≡ ids
-- -- -- -- -- -- -- -- -- -- mrens (wkr idr) ids ≡ ids

-- -- -- -- -- -- -- -- -- comp-sub-subr : ∀ {Δ Γ Ξ Ξ′ A} (σ : Δ ⁏ Γ ⊢* Ξ′) (η : Ξ′ ⊒ Ξ) (t : Δ ⁏ Ξ ⊢ A) →
-- -- -- -- -- -- -- -- --                 sub (subr σ η) t ≡ sub σ (ren η t)
-- -- -- -- -- -- -- -- -- comp-sub-subr σ η (var x)        = refl
-- -- -- -- -- -- -- -- -- comp-sub-subr σ η (lam t)        = lam & ( flip sub t & fu′ (fu (comp-lifts-subr σ η))
-- -- -- -- -- -- -- -- --                                          ⋮ comp-sub-subr (lifts σ) (liftr η) t)
-- -- -- -- -- -- -- -- -- comp-sub-subr σ η (app t₁ t₂)    = app & comp-sub-subr σ η t₁ ⊗ comp-sub-subr σ η t₂
-- -- -- -- -- -- -- -- -- comp-sub-subr σ η (mvar x)       = refl
-- -- -- -- -- -- -- -- -- comp-sub-subr σ η (box t)        = refl
-- -- -- -- -- -- -- -- -- comp-sub-subr σ η (letbox t₁ t₂) = letbox & comp-sub-subr σ η t₁
-- -- -- -- -- -- -- -- --                                           ⊗ ( flip sub t₂ & {!!}
-- -- -- -- -- -- -- -- --                                             ⋮ comp-sub-subr {!mwks σ!} η t₂)

-- -- -- -- -- -- -- -- -- --       mrens pop (subr σ η) ≡ subr (mrens pop σ) η
-- -- -- -- -- -- -- -- -- --            mwks (subr σ η) ≡ subr (mwks σ) η
-- -- -- -- -- -- -- -- -- -- mrens (wkr idr) (subr σ η) ≡ subr (mrens (wkr idr) σ) η

-- -- -- -- -- -- -- -- -- comp-sub-rens : ∀ {Δ Γ Γ′ Ξ A} (η : Γ′ ⊒ Γ) (σ : Δ ⁏ Γ ⊢* Ξ) (t : Δ ⁏ Ξ ⊢ A) →
-- -- -- -- -- -- -- -- --                 sub (rens η σ) t ≡ ren η (sub σ t)
-- -- -- -- -- -- -- -- -- comp-sub-rens η σ (var x)        = comp-subi-rens η σ x
-- -- -- -- -- -- -- -- -- comp-sub-rens η σ (lam t)        = lam & ( flip sub t & fu′ (fu (comp-lifts-rens η σ))
-- -- -- -- -- -- -- -- --                                          ⋮ comp-sub-rens (liftr η) (lifts σ) t
-- -- -- -- -- -- -- -- --                                          )
-- -- -- -- -- -- -- -- -- comp-sub-rens η σ (app t₁ t₂)    = app & comp-sub-rens η σ t₁ ⊗ comp-sub-rens η σ t₂
-- -- -- -- -- -- -- -- -- comp-sub-rens η σ (mvar x)       = refl
-- -- -- -- -- -- -- -- -- comp-sub-rens η σ (box t)        = refl
-- -- -- -- -- -- -- -- -- comp-sub-rens η σ (letbox t₁ t₂) = letbox & comp-sub-rens η σ t₁
-- -- -- -- -- -- -- -- --                                           ⊗ ( flip sub t₂ & {!!}
-- -- -- -- -- -- -- -- --                                             ⋮ comp-sub-rens η {!mwks σ!} t₂)

-- -- -- -- -- -- -- -- -- --       mrens pop (rens η σ) ≡ rens η (mrens pop σ)
-- -- -- -- -- -- -- -- -- --            mwks (rens η σ) ≡ rens η (mwks σ)
-- -- -- -- -- -- -- -- -- -- mrens (wkr idr) (rens η σ) ≡ rens η (mrens (wkr idr) σ)

-- -- -- -- -- -- -- -- -- -- private
-- -- -- -- -- -- -- -- -- --   ss : SubSpec
-- -- -- -- -- -- -- -- -- --   ss = record
-- -- -- -- -- -- -- -- -- --          { sub           = sub
-- -- -- -- -- -- -- -- -- --          ; id-sub        = id-sub
-- -- -- -- -- -- -- -- -- --          ; comp-sub-subr = comp-sub-subr
-- -- -- -- -- -- -- -- -- --          ; comp-sub-rens = comp-sub-rens
-- -- -- -- -- -- -- -- -- --          ; comp-sub-var  = λ σ x → refl
-- -- -- -- -- -- -- -- -- --          }

-- -- -- -- -- -- -- -- -- ------------------------------------------------------------------------------
