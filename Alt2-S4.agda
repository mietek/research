module Alt2-S4 where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList


--------------------------------------------------------------------------------


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


infix 7 _valid[_]
record HypotheticalValidity : Set
  where
    constructor _valid[_]
    field
      A : Prop
      Ψ : List Truth


infix 7 _valid
record CategoricalValidity : Set
  where
    constructor _valid
    field
      A : Prop


--------------------------------------------------------------------------------


infix 3 _⊢_
data _⊢_ : List CategoricalValidity → HypotheticalValidity → Set
  where
    var : ∀ {A Δ Γ} → Γ ∋ A true
                    → Δ ⊢ A valid[ Γ ]

    lam : ∀ {A B Δ Γ} → Δ ⊢ B valid[ Γ , A true ]
                      → Δ ⊢ A ⊃ B valid[ Γ ]

    app : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B valid[ Γ ] → Δ ⊢ A valid[ Γ ]
                      → Δ ⊢ B valid[ Γ ]

    mvar : ∀ {A Δ Γ} → Δ ∋ A valid
                     → Δ ⊢ A valid[ Γ ]

    box : ∀ {A Δ Γ} → Δ ⊢ A valid[ ∙ ]
                    → Δ ⊢ □ A valid[ Γ ]

    letbox : ∀ {A B Δ Γ} → Δ ⊢ □ A valid[ Γ ] → Δ , A valid ⊢ B valid[ Γ ]
                         → Δ ⊢ B valid[ Γ ]


--------------------------------------------------------------------------------


ren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⊢ A valid[ Γ ]
                   → Δ ⊢ A valid[ Γ′ ]
ren η (var 𝒾)      = var (ren∋ η 𝒾)
ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
ren η (mvar 𝒾)     = mvar 𝒾
ren η (box 𝒟)      = box 𝒟
ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren η ℰ)


wk : ∀ {B A Δ Γ} → Δ ⊢ A valid[ Γ ]
                 → Δ ⊢ A valid[ Γ , B ]
wk 𝒟 = ren (drop id) 𝒟


vz : ∀ {A Δ Γ} → Δ ⊢ A valid[ Γ , A true ]
vz = var zero


--------------------------------------------------------------------------------


mren : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⊢ A valid[ Γ ]
                    → Δ′ ⊢ A valid[ Γ ]
mren η (var 𝒾)      = var 𝒾
mren η (lam 𝒟)      = lam (mren η 𝒟)
mren η (app 𝒟 ℰ)    = app (mren η 𝒟) (mren η ℰ)
mren η (mvar 𝒾)     = mvar (ren∋ η 𝒾)
mren η (box 𝒟)      = box (mren η 𝒟)
mren η (letbox 𝒟 ℰ) = letbox (mren η 𝒟) (mren (keep η) ℰ)


mwk : ∀ {B A Δ Γ} → Δ ⊢ A valid[ Γ ]
                  → Δ , B valid ⊢ A valid[ Γ ]
mwk 𝒟 = mren (drop id) 𝒟


mvz : ∀ {A Δ Γ} → Δ , A valid ⊢ A valid[ Γ ]
mvz = mvar zero


--------------------------------------------------------------------------------


infix 4 _allvalid[_]
record HypotheticalValidities : Set
  where
    constructor _allvalid[_]
    field
      Ξ : List Prop
      Γ : List Truth


pac : List Truth → List Prop → List HypotheticalValidity
pac Γ ∙       = ∙
pac Γ (Ξ , A) = pac Γ Ξ , A valid[ Γ ]


pac∋ : ∀ {Γ Ξ A} → Ξ ∋ A
                 → pac Γ Ξ ∋ A valid[ Γ ]
pac∋ zero    = zero
pac∋ (suc 𝒾) = suc (pac∋ 𝒾)


infix 3 _⊢⋆_
_⊢⋆_ : List CategoricalValidity → HypotheticalValidities → Set
Δ ⊢⋆ Ξ allvalid[ Γ ] = All (Δ ⊢_) (pac Γ Ξ)


--------------------------------------------------------------------------------


rens : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⊢⋆ Ξ allvalid[ Γ ]
                    → Δ ⊢⋆ Ξ allvalid[ Γ′ ]
rens {Ξ = ∙}     η ∙       = ∙
rens {Ξ = Ξ , A} η (ξ , 𝒟) = rens η ξ , ren η 𝒟
-- NOTE: Equivalent to
-- rens η ξ = maps (ren η) ξ


wks : ∀ {A Δ Γ Ξ} → Δ ⊢⋆ Ξ allvalid[ Γ ]
                  → Δ ⊢⋆ Ξ allvalid[ Γ , A ]
wks ξ = rens (drop id) ξ


lifts : ∀ {A Δ Γ Ξ} → Δ ⊢⋆ Ξ allvalid[ Γ ]
                    → Δ ⊢⋆ Ξ , A allvalid[ Γ , A true ]
lifts ξ = wks ξ , vz


vars : ∀ {Δ Γ Γ′} → Γ′ ⊇ Γ
                  → Δ ⊢⋆ Γ allvalid[ {!Γ′!} ]
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {Δ Γ} → Δ ⊢⋆ Γ allvalid[ {!Γ!} ]
ids = vars id


--------------------------------------------------------------------------------


mrens : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⊢⋆ Ξ allvalid[ Γ ]
                     → Δ′ ⊢⋆ Ξ allvalid[ Γ ]
mrens η ξ = maps (mren η) ξ


mwks : ∀ {A Δ Γ Ξ} → Δ ⊢⋆ Ξ allvalid[ Γ ]
                   → Δ , A valid ⊢⋆ Ξ allvalid[ Γ ]
mwks ξ = mrens (drop id) ξ


--------------------------------------------------------------------------------


sub : ∀ {Δ Γ Ξ A} → Δ ⊢⋆ Ξ allvalid[ Γ ] → Δ ⊢ A valid[ {!Ξ!} ]
                  → Δ ⊢ A valid[ Γ ]
sub ξ (var 𝒾)      = get ξ {!pac∋ 𝒾!}
sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (mvar 𝒾)     = mvar 𝒾
sub ξ (box 𝒟)      = box 𝒟
sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)


cut : ∀ {Δ Γ A B} → Δ ⊢ A valid[ Γ ] → Δ ⊢ B valid[ Γ , A true ]
                  → Δ ⊢ B valid[ Γ ]
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


--------------------------------------------------------------------------------


subs : ∀ {Δ Γ Ξ Ψ} → Δ ⊢⋆ Ξ allvalid[ Γ ] → Δ ⊢⋆ Ψ allvalid[ {!Ξ!} ]
                   → Δ ⊢⋆ Ψ allvalid[ Γ ]
subs {Ψ = ∙}     ξ ∙       = ∙
subs {Ψ = Ξ , A} ξ (ψ , 𝒟) = subs ξ ψ , sub ξ 𝒟
-- NOTE: Equivalent to
-- subs ξ ψ = maps (sub ξ) ψ


--------------------------------------------------------------------------------


infix 3 _⊢₁_
_⊢₁_ : List CategoricalValidity → CategoricalValidity → Set
Δ ⊢₁ A valid = Δ ⊢ A valid[ ∙ ]


infix 3 _⊢⋆₁_
_⊢⋆₁_ : List CategoricalValidity → List CategoricalValidity → Set
Δ ⊢⋆₁ Ξ = All (Δ ⊢₁_) Ξ


--------------------------------------------------------------------------------


mrens₁ : ∀ {Δ Δ′ Ξ} → Δ′ ⊇ Δ → Δ ⊢⋆₁ Ξ
                    → Δ′ ⊢⋆₁ Ξ
mrens₁ η ξ = maps (mren η) ξ


mwks₁ : ∀ {A Δ Ξ} → Δ ⊢⋆₁ Ξ
                  → Δ , A valid ⊢⋆₁ Ξ
mwks₁ ξ = mrens₁ (drop id) ξ


mlifts₁ : ∀ {A Δ Ξ} → Δ ⊢⋆₁ Ξ
                    → Δ , A valid ⊢⋆₁ Ξ , A valid
mlifts₁ ξ = mwks₁ ξ , mvz


mvars₁ : ∀ {Δ Δ′} → Δ′ ⊇ Δ
                  → Δ′ ⊢⋆₁ Δ
mvars₁ done     = ∙
mvars₁ (drop η) = mwks₁ (mvars₁ η)
mvars₁ (keep η) = mlifts₁ (mvars₁ η)


mids₁ : ∀ {Δ} → Δ ⊢⋆₁ Δ
mids₁ = mvars₁ id


--------------------------------------------------------------------------------


msub : ∀ {Δ Γ Ξ A} → Δ ⊢⋆₁ Ξ → Ξ ⊢ A valid[ Γ ]
                   → Δ ⊢ A valid[ Γ ]
msub ξ (var 𝒾)      = var 𝒾
msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
msub ξ (mvar 𝒾)     = sub ∙ (get ξ 𝒾)
msub ξ (box 𝒟)      = box (msub ξ 𝒟)
msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts₁ ξ) ℰ)


mcut : ∀ {Δ Γ A B} → Δ ⊢₁ A valid → Δ , A valid ⊢ B valid[ Γ ]
                   → Δ ⊢ B valid[ Γ ]
mcut 𝒟 ℰ = msub (mids₁ , 𝒟) ℰ


--------------------------------------------------------------------------------


msubs : ∀ {Δ Γ Ξ Ψ} → Δ ⊢⋆₁ Ξ → Ξ ⊢⋆ Ψ allvalid[ Γ ]
                    → Δ ⊢⋆ Ψ allvalid[ Γ ]
msubs ξ ψ = maps (msub ξ) ψ


msubs₁ : ∀ {Δ Ξ Ψ} → Δ ⊢⋆₁ Ξ → Ξ ⊢⋆₁ Ψ
                   → Δ ⊢⋆₁ Ψ
msubs₁ ξ ψ = maps (msub ξ) ψ


--------------------------------------------------------------------------------


unlam : ∀ {Δ Γ A B} → Δ ⊢ A ⊃ B valid[ Γ ]
                    → Δ ⊢ B valid[ Γ , A true ]
unlam 𝒟 = app (wk 𝒟) vz


ex : ∀ {Δ Γ A B C} → Δ ⊢ C valid[ Γ , A , B ]
                   → Δ ⊢ C valid[ Γ , B , A ]
ex 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------


up : ∀ {Δ Γ A B} → Δ ⊢ B valid[ Γ , □ A true ]
                 → Δ , A valid ⊢ B valid[ Γ ]
up 𝒟 = app (lam (mwk 𝒟)) (box mvz)


down : ∀ {Δ Γ A B} → Δ , A valid ⊢ B valid[ Γ ]
                   → Δ ⊢ B valid[ Γ , □ A true ]
down 𝒟 = letbox vz (wk 𝒟)


mex : ∀ {Δ Γ A B C} → Δ , A valid , B valid ⊢ C valid[ Γ ]
                    → Δ , B valid , A valid ⊢ C valid[ Γ ]
mex 𝒟 = up (up (ex (down (down 𝒟))))


--------------------------------------------------------------------------------


-- import StdIPL as IPL
-- open IPL using (BASE ; _⊃_ ; _true ; var ; lam ; app)


-- ⌈_⌉ₚ : IPL.Prop → Prop
-- ⌈ BASE ⌉ₚ  = BASE
-- ⌈ A ⊃ B ⌉ₚ = ⌈ A ⌉ₚ ⊃ ⌈ B ⌉ₚ

-- ⌈_⌉ₕ : List IPL.Truth → List Prop
-- ⌈ ∙ ⌉ₕ          = ∙
-- ⌈ Γ , A true ⌉ₕ = ⌈ Γ ⌉ₕ , ⌈ A ⌉ₚ

-- ⌈_⌉ᵢ : ∀ {Γ A} → Γ ∋ A true
--                → ⌈ Γ ⌉ₕ ∋ ⌈ A ⌉ₚ
-- ⌈ zero ⌉ᵢ  = zero
-- ⌈ suc 𝒾 ⌉ᵢ = suc ⌈ 𝒾 ⌉ᵢ

-- ⌈_⌉ : ∀ {Γ A} → Γ IPL.⊢ A true
--               → ∙ ⊢ ⌈ A ⌉ₚ valid[ {!⌈ Γ ⌉ₕ!} ]
-- ⌈ var 𝒾 ⌉   = var {!⌈ 𝒾 ⌉ᵢ!}
-- ⌈ lam 𝒟 ⌉   = lam ⌈ 𝒟 ⌉
-- ⌈ app 𝒟 ℰ ⌉ = app ⌈ 𝒟 ⌉ ⌈ ℰ ⌉


-- ⌊_⌋ₚ : Prop → IPL.Prop
-- ⌊ BASE ⌋ₚ  = BASE
-- ⌊ A ⊃ B ⌋ₚ = ⌊ A ⌋ₚ ⊃ ⌊ B ⌋ₚ
-- ⌊ □ A ⌋ₚ   = ⌊ A ⌋ₚ

-- ⌊_⌋ₕ : List Prop → List IPL.Truth
-- ⌊ ∙ ⌋ₕ     = ∙
-- ⌊ Γ , A ⌋ₕ = ⌊ Γ ⌋ₕ , ⌊ A ⌋ₚ true

-- ⌊_⌋ᵢ : ∀ {Γ A} → Γ ∋ A
--                → ⌊ Γ ⌋ₕ ∋ ⌊ A ⌋ₚ true
-- ⌊ zero ⌋ᵢ  = zero
-- ⌊ suc 𝒾 ⌋ᵢ = suc ⌊ 𝒾 ⌋ᵢ

-- -- {-# TERMINATING #-}
-- -- ⌊_⌋ : ∀ {Γ A} → ∙ ⊢ A valid[ Γ ]
-- --               → ⌊ Γ ⌋ₕ IPL.⊢ ⌊ A ⌋ₚ true
-- -- ⌊ var 𝒾 ⌋      = var ⌊ 𝒾 ⌋ᵢ
-- -- ⌊ lam 𝒟 ⌋      = lam ⌊ 𝒟 ⌋
-- -- ⌊ app 𝒟 ℰ ⌋    = app ⌊ 𝒟 ⌋ ⌊ ℰ ⌋
-- -- ⌊ mvar () ⌋
-- -- ⌊ box 𝒟 ⌋      = IPL.sub ∙ ⌊ 𝒟 ⌋
-- -- ⌊ letbox 𝒟 ℰ ⌋ = ⌊ cut 𝒟 (down ℰ) ⌋ -- woah!


-- -- --------------------------------------------------------------------------------
