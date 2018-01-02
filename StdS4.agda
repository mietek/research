module StdS4 where

open import Prelude
open import List


infixr 8 _⊃_
data Prop : Set
  where
    BASE : Prop
    _⊃_  : Prop → Prop → Prop
    □_   : Prop → Prop


infix 7 _true
record Truth : Set
  where
    constructor _true
    field
      A : Prop

infix 7 _valid
record Validity : Set
  where
    constructor _valid
    field
      A : Prop


infix 5 _⨾_
record Context : Set
  where
    constructor _⨾_
    field
      Δ : List Validity
      Γ : List Truth


infix 3 _⊢_
data _⊢_ : Context → Truth → Set
  where
    var : ∀ {A Δ Γ} → Γ ∋ A true
                    → Δ ⨾ Γ ⊢ A true

    lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A true ⊢ B true
                      → Δ ⨾ Γ ⊢ A ⊃ B true

    app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ A ⊃ B true → Δ ⨾ Γ ⊢ A true
                      → Δ ⨾ Γ ⊢ B true

    mvar : ∀ {A Δ Γ} → Δ ∋ A valid
                     → Δ ⨾ Γ ⊢ A true

    box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                    → Δ ⨾ Γ ⊢ □ A true

    letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ □ A true → Δ , A valid ⨾ Γ ⊢ B true
                         → Δ ⨾ Γ ⊢ B true


ren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ A true
                   → Δ ⨾ Γ′ ⊢ A true
ren η (var 𝒾)      = var (ren∋ η 𝒾)
ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
ren η (mvar 𝒾)     = mvar 𝒾
ren η (box 𝒟)      = box 𝒟
ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren η ℰ)

wk : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ A true
                 → Δ ⨾ Γ , B true ⊢ A true
wk 𝒟 = ren (drop id⊇) 𝒟

vz : ∀ {A Δ Γ} → Δ ⨾ Γ , A true ⊢ A true
vz = var zero


mren : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ A true
                    → Δ′ ⨾ Γ ⊢ A true
mren η (var 𝒾)      = var 𝒾
mren η (lam 𝒟)      = lam (mren η 𝒟)
mren η (app 𝒟 ℰ)    = app (mren η 𝒟) (mren η ℰ)
mren η (mvar 𝒾)     = mvar (ren∋ η 𝒾)
mren η (box 𝒟)      = box (mren η 𝒟)
mren η (letbox 𝒟 ℰ) = letbox (mren η 𝒟) (mren (keep η) ℰ)

mwk : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ A true
                  → Δ , B valid ⨾ Γ ⊢ A true
mwk 𝒟 = mren (drop id⊇) 𝒟

mvz : ∀ {A Δ Γ} → Δ , A valid ⨾ Γ ⊢ A true
mvz = mvar zero


infix 3 _⊢⋆_
_⊢⋆_ : Context → List Truth → Set
Δ ⨾ Γ ⊢⋆ Ξ = All (Δ ⨾ Γ ⊢_) Ξ


rens : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢⋆ Ξ
                    → Δ ⨾ Γ′ ⊢⋆ Ξ
rens η ξ = mapAll (ren η) ξ

wks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                  → Δ ⨾ Γ , A true ⊢⋆ Ξ
wks ξ = rens (drop id⊇) ξ

lifts : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                    → Δ ⨾ Γ , A true ⊢⋆ Ξ , A true
lifts ξ = wks ξ , vz

ids : ∀ {Γ Δ} → Δ ⨾ Γ ⊢⋆ Γ
ids {∙}          = ∙
ids {Γ , A true} = lifts ids


mrens : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢⋆ Ξ
                     → Δ′ ⨾ Γ ⊢⋆ Ξ
mrens η ξ = mapAll (mren η) ξ

mwks : ∀ {A Δ Γ Ξ} → Δ ⨾ Γ ⊢⋆ Ξ
                   → Δ , A valid ⨾ Γ ⊢⋆ Ξ
mwks ξ = mrens (drop id⊇) ξ


sub : ∀ {Δ Γ Ξ A} → Δ ⨾ Γ ⊢⋆ Ξ → Δ ⨾ Ξ ⊢ A true
                  → Δ ⨾ Γ ⊢ A true
sub ξ (var 𝒾)      = lookup ξ 𝒾
sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (mvar 𝒾)     = mvar 𝒾
sub ξ (box 𝒟)      = box 𝒟
sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)

cut : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A true → Δ ⨾ Γ , A true ⊢ B true
                  → Δ ⨾ Γ ⊢ B true
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


infix 3 _⊢₁_
_⊢₁_ : List Validity → Validity → Set
Δ ⊢₁ A valid = Δ ⨾ ∙ ⊢ A true

infix 3 _⊢⋆₁_
_⊢⋆₁_ : List Validity → List Validity → Set
Δ ⊢⋆₁ Ξ = All (Δ ⊢₁_) Ξ


mrens₁ : ∀ {Δ Δ′ Ξ} → Δ′ ⊇ Δ → Δ ⊢⋆₁ Ξ
                    → Δ′ ⊢⋆₁ Ξ
mrens₁ η ξ = mapAll (mren η) ξ

mwks₁ : ∀ {A Δ Ξ} → Δ ⊢⋆₁ Ξ
                  → Δ , A valid ⊢⋆₁ Ξ
mwks₁ ξ = mrens₁ (drop id⊇) ξ

mlifts₁ : ∀ {A Δ Ξ} → Δ ⊢⋆₁ Ξ
                    → Δ , A valid ⊢⋆₁ Ξ , A valid
mlifts₁ ξ = mwks₁ ξ , mvz

mids₁ : ∀ {Δ} → Δ ⊢⋆₁ Δ
mids₁ {∙}           = ∙
mids₁ {Δ , A valid} = mlifts₁ mids₁


msub : ∀ {Δ Γ Ξ A} → Δ ⊢⋆₁ Ξ → Ξ ⨾ Γ ⊢ A true
                   → Δ ⨾ Γ ⊢ A true
msub ξ (var 𝒾)      = var 𝒾
msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
msub ξ (mvar 𝒾)     = sub ∙ (lookup ξ 𝒾)
msub ξ (box 𝒟)      = box (msub ξ 𝒟)
msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts₁ ξ) ℰ)

mcut : ∀ {Δ Γ A B} → Δ ⊢₁ A valid → Δ , A valid ⨾ Γ ⊢ B true
                   → Δ ⨾ Γ ⊢ B true
mcut 𝒟 ℰ = msub (mids₁ , 𝒟) ℰ


unlam : ∀ {Δ Γ A B} → Δ ⨾ Γ ⊢ A ⊃ B true
                    → Δ ⨾ Γ , A true ⊢ B true
unlam 𝒟 = app (wk 𝒟) vz

shl : ∀ {Δ Γ A B} → Δ ⨾ Γ , □ A true ⊢ B true
                  → Δ , A valid ⨾ Γ ⊢ B true
shl 𝒟 = app (lam (mwk 𝒟)) (box mvz)

shr : ∀ {Δ Γ A B} → Δ , A valid ⨾ Γ ⊢ B true
                  → Δ ⨾ Γ , □ A true ⊢ B true
shr 𝒟 = letbox vz (wk 𝒟)

ex : ∀ {Δ Γ A B C} → Δ ⨾ Γ , A true , B true ⊢ C true
                   → Δ ⨾ Γ , B true , A true ⊢ C true
ex 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)

mex : ∀ {Δ Γ A B C} → Δ , A valid , B valid ⨾ Γ ⊢ C true
                    → Δ , B valid , A valid ⨾ Γ ⊢ C true
mex 𝒟 = shl (shl (ex (shr (shr 𝒟))))


mutual
  infix 3 _⊢ₙₘ_
  data _⊢ₙₘ_ : Context → Truth → Set
    where
      lam : ∀ {A B Δ Γ} → Δ ⨾ Γ , A true ⊢ₙₘ B true
                        → Δ ⨾ Γ ⊢ₙₘ A ⊃ B true

      box : ∀ {A Δ Γ} → Δ ⨾ ∙ ⊢ A true
                      → Δ ⨾ Γ ⊢ₙₘ □ A true

      letbox : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ₙₜ □ A true → Δ , A valid ⨾ Γ ⊢ₙₘ B true
                           → Δ ⨾ Γ ⊢ₙₘ B true

      nt : ∀ {Δ Γ} → Δ ⨾ Γ ⊢ₙₜ BASE true
                   → Δ ⨾ Γ ⊢ₙₘ BASE true

  infix 3 _⊢ₙₜ_
  data _⊢ₙₜ_ : Context → Truth → Set
    where
      var : ∀ {A Δ Γ} → Γ ∋ A true
                      → Δ ⨾ Γ ⊢ₙₜ A true

      app : ∀ {A B Δ Γ} → Δ ⨾ Γ ⊢ₙₜ A ⊃ B true → Δ ⨾ Γ ⊢ₙₘ A true
                        → Δ ⨾ Γ ⊢ₙₜ B true

      mvar : ∀ {A Δ Γ} → Δ ∋ A valid
                       → Δ ⨾ Γ ⊢ₙₜ A true


mutual
  embₙₘ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ₙₘ A true
                    → Δ ⨾ Γ ⊢ A true
  embₙₘ (lam 𝒟)      = lam (embₙₘ 𝒟)
  embₙₘ (box 𝒟)      = box 𝒟
  embₙₘ (letbox 𝒟 ℰ) = letbox (embₙₜ 𝒟) (embₙₘ ℰ)
  embₙₘ (nt 𝒟)       = embₙₜ 𝒟

  embₙₜ : ∀ {Δ Γ A} → Δ ⨾ Γ ⊢ₙₜ A true
                    → Δ ⨾ Γ ⊢ A true
  embₙₜ (var 𝒾)   = var 𝒾
  embₙₜ (app 𝒟 ℰ) = app (embₙₜ 𝒟) (embₙₘ ℰ)
  embₙₜ (mvar 𝒾)  = mvar 𝒾


mutual
  renₙₘ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ₙₘ A true
                       → Δ ⨾ Γ′ ⊢ₙₘ A true
  renₙₘ η (lam 𝒟)      = lam (renₙₘ (keep η) 𝒟)
  renₙₘ η (box 𝒟)      = box 𝒟
  renₙₘ η (letbox 𝒟 ℰ) = letbox (renₙₜ η 𝒟) (renₙₘ η ℰ)
  renₙₘ η (nt 𝒟)       = nt (renₙₜ η 𝒟)

  renₙₜ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⨾ Γ ⊢ₙₜ A true
                       → Δ ⨾ Γ′ ⊢ₙₜ A true
  renₙₜ η (var 𝒾)   = var (ren∋ η 𝒾)
  renₙₜ η (app 𝒟 ℰ) = app (renₙₜ η 𝒟) (renₙₘ η ℰ)
  renₙₜ η (mvar 𝒾)  = mvar 𝒾

wkₙₜ : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ₙₜ A true
                   → Δ ⨾ Γ , B true ⊢ₙₜ A true
wkₙₜ 𝒟 = renₙₜ (drop id⊇) 𝒟

vzₙₜ : ∀ {A Δ Γ} → Δ ⨾ Γ , A true ⊢ₙₜ A true
vzₙₜ = var zero


mutual
  mrenₙₘ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ₙₘ A true
                        → Δ′ ⨾ Γ ⊢ₙₘ A true
  mrenₙₘ η (lam 𝒟)      = lam (mrenₙₘ η 𝒟)
  mrenₙₘ η (box 𝒟)      = box (mren η 𝒟)
  mrenₙₘ η (letbox 𝒟 ℰ) = letbox (mrenₙₜ η 𝒟) (mrenₙₘ (keep η) ℰ)
  mrenₙₘ η (nt 𝒟)       = nt (mrenₙₜ η 𝒟)

  mrenₙₜ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⨾ Γ ⊢ₙₜ A true
                        → Δ′ ⨾ Γ ⊢ₙₜ A true
  mrenₙₜ η (var 𝒾)   = var 𝒾
  mrenₙₜ η (app 𝒟 ℰ) = app (mrenₙₜ η 𝒟) (mrenₙₘ η ℰ)
  mrenₙₜ η (mvar 𝒾)  = mvar (ren∋ η 𝒾)

mwkₙₜ : ∀ {B A Δ Γ} → Δ ⨾ Γ ⊢ₙₜ A true
                    → Δ , B valid ⨾ Γ ⊢ₙₜ A true
mwkₙₜ 𝒟 = mrenₙₜ (drop id⊇) 𝒟

mvzₙₜ : ∀ {A Δ Γ} → Δ , A valid ⨾ Γ ⊢ₙₜ A true
mvzₙₜ = mvar zero


infix 4 _⊇²_
_⊇²_ : Context → Context → Set
Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ = Δ′ ⊇ Δ × Γ′ ⊇ Γ

drop⊇² : ∀ {A Δ Δ′ Γ Γ′} → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ
                        → Δ′ ⨾ Γ′ , A true ⊇² Δ ⨾ Γ
drop⊇² η = proj₁ η , drop (proj₂ η)

mdrop⊇² : ∀ {A Δ Δ′ Γ Γ′} → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ
                         → Δ′ , A valid ⨾ Γ′ ⊇² Δ ⨾ Γ
mdrop⊇² η = drop (proj₁ η) , proj₂ η

id⊇² : ∀ {Δ Γ} → Δ ⨾ Γ ⊇² Δ ⨾ Γ
id⊇² = id⊇ , id⊇

_∘⊇²_ : ∀ {Δ Δ′ Δ″ Γ Γ′ Γ″} → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ → Δ″ ⨾ Γ″ ⊇² Δ′ ⨾ Γ′
                           → Δ″ ⨾ Γ″ ⊇² Δ ⨾ Γ
η₁ ∘⊇² η₂ = (proj₁ η₁ ∘⊇ proj₁ η₂) , (proj₂ η₁ ∘⊇ proj₂ η₂)


renₙₜ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⨾ Γ′ ⊇² Δ ⨾ Γ → Δ ⨾ Γ ⊢ₙₜ A true
                         → Δ′ ⨾ Γ′ ⊢ₙₜ A true
renₙₜ² η 𝒟 = mrenₙₜ (proj₁ η) (renₙₜ (proj₂ η) 𝒟)
