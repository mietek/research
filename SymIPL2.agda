module SymIPL2 where

open import Prelude
open import List
open import AllList


--------------------------------------------------------------------------------


infixr 8 _⊃_
data Prop : Set
  where
    BASE : Prop
    _⊃_  : Prop → Prop → Prop


infix 7 _true
record Truth : Set
  where
    constructor _true
    field
      A : Prop


--------------------------------------------------------------------------------


infix 3 _⊢_
data _⊢_ : List Truth → Truth → Set
  where
    var : ∀ {A Γ} → Γ ∋ A true
                  → Γ ⊢ A true

    cut : ∀ {A B Γ} → Γ ⊢ A true → Γ , A true ⊢ B true
                    → Γ ⊢ B true

    lam : ∀ {A B Γ} → Γ , A true ⊢ B true
                    → Γ ⊢ A ⊃ B true

    unlam : ∀ {A B Γ} → Γ ⊢ A ⊃ B true
                      → Γ , A true ⊢ B true


infix 3 _⊢⋆_
_⊢⋆_ : List Truth → List Truth → Set
Γ ⊢⋆ Ξ = All (Γ ⊢_) Ξ


--------------------------------------------------------------------------------



app : ∀ {Γ A B} → Γ ⊢ A ⊃ B true → Γ ⊢ A true
                → Γ ⊢ B true
app 𝒟 ℰ = cut ℰ (unlam 𝒟)


vz : ∀ {A Γ} → Γ , A true ⊢ A true
vz = var zero


mutual
  wk : ∀ {B A Γ} → Γ ⊢ A true
                 → Γ , B true ⊢ A true
  wk (var 𝒾)   = var (suc 𝒾)
  wk (cut 𝒟 ℰ) = unlam (cut 𝒟 (lam (wk ℰ)))
  wk (lam 𝒟)   = lam (ex (wk 𝒟))
  wk (unlam 𝒟) = ex (unlam (wk 𝒟))

  ex : ∀ {Γ A B C} → Γ , A true , B true ⊢ C true
                   → Γ , B true , A true ⊢ C true
  ex (var 𝒾)   = {!!}
  ex (cut 𝒟 ℰ) = {!!}
  ex (lam 𝒟)   = {!!}
  ex (unlam 𝒟) = {!!}


wks : ∀ {A Γ Ξ} → Γ ⊢⋆ Ξ
                → Γ , A true ⊢⋆ Ξ
wks ξ = {!!} -- rens (drop id⊇) ξ


lifts : ∀ {A Γ Ξ} → Γ ⊢⋆ Ξ
                  → Γ , A true ⊢⋆ Ξ , A true
lifts ξ = wks ξ , vz


sub : ∀ {Γ Ξ A} → Γ ⊢⋆ Ξ → Ξ ⊢ A true
                → Γ ⊢ A true
sub ξ       (var 𝒾)   = get ξ 𝒾
sub ξ       (cut 𝒟 ℰ) = cut (sub ξ 𝒟) (sub (lifts ξ) ℰ)
sub ξ       (lam 𝒟)   = lam (sub (lifts ξ) 𝒟)
sub (ξ , 𝒞) (unlam 𝒟) = cut 𝒞 (unlam (sub ξ 𝒟))


--------------------------------------------------------------------------------


-- ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A true
--                  → Γ′ ⊢ A true
-- ren η (var 𝒾)   = var (ren∋ η 𝒾)
-- ren η (cut 𝒟 ℰ) = cut (ren η 𝒟) (ren (keep η) ℰ)
-- ren η (lam 𝒟)   = lam (ren (keep η) 𝒟)
-- ren (drop η) (unlam 𝒟) = {!!}
-- ren (keep η) (unlam 𝒟) = unlam (ren η 𝒟)


-- --------------------------------------------------------------------------------

-- --------------------------------------------------------------------------------


-- rens : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢⋆ Ξ
--                   → Γ′ ⊢⋆ Ξ
-- rens η ξ = maps (ren η) ξ




-- vars : ∀ {Γ Γ′} → Γ′ ⊇ Γ
--                 → Γ′ ⊢⋆ Γ
-- vars done     = ∙
-- vars (drop η) = wks (vars η)
-- vars (keep η) = lifts (vars η)


-- ids : ∀ {Γ} → Γ ⊢⋆ Γ
-- ids = vars id⊇


-- --------------------------------------------------------------------------------



-- cut : ∀ {Γ A B} → Γ ⊢ A true → Γ , A true ⊢ B true
--                 → Γ ⊢ B true
-- cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


-- --------------------------------------------------------------------------------


-- subs : ∀ {Γ Ξ Ψ} → Γ ⊢⋆ Ξ → Ξ ⊢⋆ Ψ
--                  → Γ ⊢⋆ Ψ
-- subs ξ ψ = maps (sub ξ) ψ


-- --------------------------------------------------------------------------------


-- unlam : ∀ {Γ A B} → Γ ⊢ A ⊃ B true
--                   → Γ , A true ⊢ B true
-- unlam 𝒟 = app (wk 𝒟) vz



-- --------------------------------------------------------------------------------
