module StdCML where

open import Prelude
open import List


--------------------------------------------------------------------------------


mutual
  infixr 8 _⊃_
  data Prop : Set
    where
      BASE : Prop
      _⊃_  : Prop → Prop → Prop
      [_]_ : List Truth → Prop → Prop

  infix 7 _true
  record Truth : Set
    where
      inductive
      constructor _true
      field
        A : Prop


infix 7 _valid[_]
record Validity : Set
  where
    constructor _valid[_]
    field
      A : Prop
      Ψ : List Truth


--------------------------------------------------------------------------------


infix 5 _⨾_
record Context : Set
  where
    constructor _⨾_
    field
      Δ : List Validity
      Γ : List Truth


infix 4 _⊇²_
_⊇²_ : Context → Context → Set
Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ = Δ′ ⊇ Δ × Γ′ ⊇ Γ


drop⊇² : ∀ {A Δ Δ′ Γ Γ′} → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ
                         → Δ′ ⨾ Γ′ , A true ⊇² Δ ⨾ Γ
drop⊇² η = proj₁ η , drop (proj₂ η)


mdrop⊇² : ∀ {A Ψ Δ Δ′ Γ Γ′} → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ
                            → Δ′ , A valid[ Ψ ] ⨾ Γ′ ⊇² Δ ⨾ Γ
mdrop⊇² η = drop (proj₁ η) , proj₂ η


id⊇² : ∀ {Δ Γ} → Δ ⨾ Γ ⊇² Δ ⨾ Γ
id⊇² = id⊇ , id⊇


_∘⊇²_ : ∀ {Δ Δ′ Δ″ Γ Γ′ Γ″} → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ → Δ″ ⨾ Γ″ ⊇² Δ′ ⨾ Γ′
                            → Δ″ ⨾ Γ″ ⊇² Δ ⨾ Γ
η₁ ∘⊇² η₂ = (proj₁ η₁ ∘⊇ proj₁ η₂) , (proj₂ η₁ ∘⊇ proj₂ η₂)


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢_
  data _⊢_ : Context → Truth → Set
    where
      var : ∀ {A Δ Γ} → Γ ∋ A true
                      → Δ ⨾ Γ ⊢ A true

      lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A true ⊢ B true
                        → Δ ⨾ Γ ⊢ A ⊃ B true

      app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true → Δ ⨾ Γ ⊢ A true
                        → Δ ⨾ Γ ⊢ B true

      mvar : ∀ {A Ψ Δ Γ} → Δ ∋ A valid[ Ψ ] → Δ ⨾ Γ ⊢⋆ Ψ
                         → Δ ⨾ Γ ⊢ A true

      box : ∀ {A Ψ Δ Γ} → Δ ⨾ Ψ ⊢ A true
                        → Δ ⨾ Γ ⊢ [ Ψ ] A true

      letbox : ∀ {A B Ψ Δ Γ} → Δ ⨾ Γ ⊢ [ Ψ ] A true → Δ , A valid[ Ψ ] ⨾ Γ ⊢ B true
                             → Δ ⨾ Γ ⊢ B true

  infix 3 _⊢⋆_
  _⊢⋆_ : Context → List Truth → Set
  Δ ⨾ Γ ⊢⋆ Ξ = All (Δ ⨾ Γ ⊢_) Ξ


--------------------------------------------------------------------------------


mutual
  ren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ A true
                     → Δ ⨾ Γ′ ⊢ A true
  ren η (var 𝒾)      = var (ren∋ η 𝒾)
  ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
  ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
  ren η (mvar 𝒾 ψ)   = mvar 𝒾 (rens η ψ)
  ren η (box 𝒟)      = box 𝒟
  ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren η ℰ)

  rens : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢⋆ Ξ
                      → Δ ⨾ Γ′ ⊢⋆ Ξ
  rens η ∙       = ∙
  rens η (ξ , 𝒟) = rens η ξ , ren η 𝒟
  -- NOTE: Equivalent to
  -- rens η ξ = mapAll (ren η) ξ


wk : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ A true
                 → Δ ⨾ Γ , B true ⊢ A true
wk 𝒟 = ren (drop id⊇) 𝒟


vz : ∀ {A Δ Γ} → Δ ⨾ Γ , A true ⊢ A true
vz = var zero


wks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                  → Δ ⨾ Γ , A true ⊢⋆ Ξ
wks ξ = rens (drop id⊇) ξ


lifts : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                    → Δ ⨾ Γ , A true ⊢⋆ Ξ , A true
lifts ξ = wks ξ , vz


ids : ∀ {Γ Δ} → Δ ⨾ Γ ⊢⋆ Γ
ids {∙}          = ∙
ids {Γ , A true} = lifts ids


--------------------------------------------------------------------------------


mutual
  mren : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ A true
                      → Δ′ ⨾ Γ ⊢ A true
  mren η (var 𝒾)      = var 𝒾
  mren η (lam 𝒟)      = lam (mren η 𝒟)
  mren η (app 𝒟 ℰ)    = app (mren η 𝒟) (mren η ℰ)
  mren η (mvar 𝒾 ψ)   = mvar (ren∋ η 𝒾) (mrens η ψ)
  mren η (box 𝒟)      = box (mren η 𝒟)
  mren η (letbox 𝒟 ℰ) = letbox (mren η 𝒟) (mren (keep η) ℰ)

  mrens : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢⋆ Ξ
                       → Δ′ ⨾ Γ ⊢⋆ Ξ
  mrens η ∙       = ∙
  mrens η (ξ , 𝒟) = mrens η ξ , mren η 𝒟
  -- NOTE: Equivalent to
  -- mrens η ξ = mapAll (mren η) ξ


mwk : ∀ {B Ψ A Δ Γ} → Δ ⨾ Γ ⊢ A true
                    → Δ , B valid[ Ψ ] ⨾ Γ ⊢ A true
mwk 𝒟 = mren (drop id⊇) 𝒟


mwks : ∀ {A Ψ Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                     → Δ , A valid[ Ψ ] ⨾ Γ ⊢⋆ Ξ
mwks ξ = mrens (drop id⊇) ξ


mvz : ∀ {A Ψ Δ Γ} → Δ ⨾ Γ ⊢⋆ Ψ
                  → Δ , A valid[ Ψ ] ⨾ Γ ⊢ A true
mvz ψ = mvar zero (mwks ψ)


--------------------------------------------------------------------------------


mutual
  sub : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢⋆ Ξ → Δ ⨾ Ξ ⊢ A true
                    → Δ ⨾ Γ ⊢ A true
  sub ξ (var 𝒾)      = lookup ξ 𝒾
  sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
  sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
  sub ξ (mvar 𝒾 ψ)   = mvar 𝒾 (subs ξ ψ)
  sub ξ (box 𝒟)      = box 𝒟
  sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)

  subs : ∀ {Δ Γ Ξ Ψ} → Δ ⨾ Γ ⊢⋆ Ξ → Δ ⨾ Ξ ⊢⋆ Ψ
                     → Δ ⨾ Γ ⊢⋆ Ψ
  subs ξ ∙       = ∙
  subs ξ (ψ , 𝒟) = subs ξ ψ , sub ξ 𝒟
  -- NOTE: Equivalent to
  -- subs ξ ψ = mapAll (sub ξ) ψ


cut : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A true → Δ ⨾ Γ , A true ⊢ B true
                  → Δ ⨾ Γ ⊢ B true
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


--------------------------------------------------------------------------------


infix 3 _⊢₁_
_⊢₁_ : List Validity → Validity → Set
Δ ⊢₁ A valid[ Ψ ] = Δ ⨾ Ψ ⊢ A true

infix 3 _⊢⋆₁_
_⊢⋆₁_ : List Validity → List Validity → Set
Δ ⊢⋆₁ Ξ = All (Δ ⊢₁_) Ξ


--------------------------------------------------------------------------------


mrens₁ : ∀ {Δ Δ′ Ξ} → Δ′ ⊇ Δ → Δ ⊢⋆₁ Ξ
                    → Δ′ ⊢⋆₁ Ξ
mrens₁ η ξ = mapAll (mren η) ξ


mwks₁ : ∀ {A Ψ Δ Ξ} → Δ ⊢⋆₁ Ξ
                    → Δ , A valid[ Ψ ] ⊢⋆₁ Ξ
mwks₁ ξ = mrens₁ (drop id⊇) ξ


mlifts₁ : ∀ {A Ψ Δ Ξ} → Δ ⊢⋆₁ Ξ
                      → Δ , A valid[ Ψ ] ⊢⋆₁ Ξ , A valid[ Ψ ]
mlifts₁ ξ = mwks₁ ξ , mvz ids


mids₁ : ∀ {Δ} → Δ ⊢⋆₁ Δ
mids₁ {∙}                = ∙
mids₁ {Δ , A valid[ Ψ ]} = mlifts₁ mids₁


--------------------------------------------------------------------------------


mutual
  msub : ∀ {Δ Γ Ξ A} → Δ ⊢⋆₁ Ξ → Ξ ⨾ Γ ⊢ A true
                     → Δ ⨾ Γ ⊢ A true
  msub ξ (var 𝒾)      = var 𝒾
  msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
  msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
  msub ξ (mvar 𝒾 ψ)   = sub (msubs ξ ψ) (lookup ξ 𝒾)
  msub ξ (box 𝒟)      = box (msub ξ 𝒟)
  msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts₁ ξ) ℰ)

  msubs : ∀ {Δ Γ Ξ Ψ} → Δ ⊢⋆₁ Ξ → Ξ ⨾ Γ ⊢⋆ Ψ
                      → Δ ⨾ Γ ⊢⋆ Ψ
  msubs ξ ∙       = ∙
  msubs ξ (ψ , 𝒟) = msubs ξ ψ , msub ξ 𝒟
  -- NOTE: Equivalent to
  -- msubs ξ ψ = mapAll (msub ξ) ψ


mcut : ∀ {Δ Γ Ψ A B} → Δ ⊢₁ A valid[ Ψ ] → Δ , A valid[ Ψ ] ⨾ Γ ⊢ B true
                     → Δ ⨾ Γ ⊢ B true
mcut 𝒟 ℰ = msub (mids₁ , 𝒟) ℰ


--------------------------------------------------------------------------------


unlam : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A ⊃ B true
                    → Δ ⨾ Γ , A true ⊢ B true
unlam 𝒟 = app (wk 𝒟) vz


ex : ∀ {Δ Γ A B C} → Δ ⨾ Γ , A true , B true ⊢ C true
                   → Δ ⨾ Γ , B true , A true ⊢ C true
ex 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------


shl : ∀ {Δ Γ Ψ A B} → Δ ⨾ Γ , [ Ψ ] A true ⊢ B true
                    → Δ , A valid[ Ψ ] ⨾ Γ ⊢ B true
shl 𝒟 = app (lam (mwk 𝒟)) (box (mvz ids))


shr : ∀ {Δ Γ Ψ A B} → Δ , A valid[ Ψ ] ⨾ Γ ⊢ B true
                    → Δ ⨾ Γ , [ Ψ ] A true ⊢ B true
shr 𝒟 = letbox vz (wk 𝒟)


mex : ∀ {Δ Γ Ψ Φ A B C} → Δ , A valid[ Ψ ] , B valid[ Φ ] ⨾ Γ ⊢ C true
                        → Δ , B valid[ Φ ] , A valid[ Ψ ] ⨾ Γ ⊢ C true
mex 𝒟 = shl (shl (ex (shr (shr 𝒟))))


--------------------------------------------------------------------------------
