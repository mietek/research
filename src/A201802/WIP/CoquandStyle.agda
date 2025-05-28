{-# OPTIONS --rewriting #-}

module A201802.WIP.CoquandStyle where

open import A201801.Prelude
open import A201801.Category
open import A201801.FullIPLPropositions

open import A201802.WIP.Bool
open import A201802.WIP.Name
open import A201802.WIP.CoquandList


--------------------------------------------------------------------------------


infix 3 _⊢_true
data _⊢_true : List Form → Form → Set
  where
    var : ∀ {A Γ} x → Γ ∋ x ⦂ A
                    → Γ ⊢ A true

    lam : ∀ {A B Γ} x → {{_ : T (fresh x Γ)}}
                      → Γ , x ⦂ A ⊢ B true
                      → Γ ⊢ A ⊃ B true

    app : ∀ {A B Γ} → Γ ⊢ A ⊃ B true → Γ ⊢ A true
                    → Γ ⊢ B true

    pair : ∀ {A B Γ} → Γ ⊢ A true → Γ ⊢ B true
                     → Γ ⊢ A ∧ B true

    fst : ∀ {A B Γ} → Γ ⊢ A ∧ B true
                    → Γ ⊢ A true

    snd : ∀ {A B Γ} → Γ ⊢ A ∧ B true
                    → Γ ⊢ B true

    unit : ∀ {Γ} → Γ ⊢ 𝟏 true

    abort : ∀ {A Γ} → Γ ⊢ 𝟎 true
                    → Γ ⊢ A true

    inl : ∀ {A B Γ} → Γ ⊢ A true
                    → Γ ⊢ A ∨ B true

    inr : ∀ {A B Γ} → Γ ⊢ B true
                    → Γ ⊢ A ∨ B true

    case : ∀ {A B C Γ} x y → {{_ : T (fresh x Γ)}} {{_ : T (fresh y Γ)}}
                           → Γ ⊢ A ∨ B true
                           → Γ , x ⦂ A ⊢ C true
                           → Γ , y ⦂ B ⊢ C true
                           → Γ ⊢ C true

infix 3 _⊢_alltrue
_⊢_alltrue : List Form → List Form → Set
Γ ⊢ Ξ alltrue = All (Γ ⊢_true) Ξ


--------------------------------------------------------------------------------


-- TODO: unfinished
postulate
  oopsᵣ : ∀ {𝔄 x} → {Γ Γ′ : List 𝔄} {{_ : T (fresh x Γ)}}
                  → Γ′ ⊇ Γ
                  → T (fresh x Γ′)


ren : ∀ {Γ′ Γ A} → Γ′ ⊇ Γ → Γ ⊢ A true
                 → Γ′ ⊢ A true
ren η (var x i)        = var x (get⊇ η i)
ren η (lam x 𝒟)        = lam x {{oopsᵣ η}} (ren (keep⊇ {{oopsᵣ η}} η) 𝒟)
ren η (app 𝒟 ℰ)        = app (ren η 𝒟) (ren η ℰ)
ren η (pair 𝒟 ℰ)       = pair (ren η 𝒟) (ren η ℰ)
ren η (fst 𝒟)          = fst (ren η 𝒟)
ren η (snd 𝒟)          = snd (ren η 𝒟)
ren η unit             = unit
ren η (abort 𝒟)        = abort (ren η 𝒟)
ren η (inl 𝒟)          = inl (ren η 𝒟)
ren η (inr 𝒟)          = inr (ren η 𝒟)
ren η (case x y 𝒟 ℰ ℱ) = case x y {{oopsᵣ η}} {{oopsᵣ η}}
                              (ren η 𝒟)
                              (ren (keep⊇ {{oopsᵣ η}} η) ℰ)
                              (ren (keep⊇ {{oopsᵣ η}} η) ℱ)


rens : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢ Ξ alltrue
                  → Γ′ ⊢ Ξ alltrue
rens η ξ = maps (ren η) ξ


--------------------------------------------------------------------------------


wk : ∀ {A x C Γ} → {{_ : T (fresh x Γ)}}
                 → Γ ⊢ C true
                 → Γ , x ⦂ A ⊢ C true
wk 𝒟 = ren (drop⊇ id) 𝒟


wks : ∀ {A x Γ Ξ} → {{_ : T (fresh x Γ)}}
                  → Γ ⊢ Ξ alltrue
                  → Γ , x ⦂ A ⊢ Ξ alltrue
wks ξ = rens (drop⊇ id) ξ


vz : ∀ {Γ A} x → {{_ : T (fresh x Γ)}}
               → Γ , x ⦂ A ⊢ A true
vz x = var x zero


lifts : ∀ {A x Γ Ξ} → {{_ : T (fresh x Γ)}} {{_ : T (fresh x Ξ)}}
                    → Γ ⊢ Ξ alltrue
                    → Γ , x ⦂ A ⊢ Ξ , x ⦂ A alltrue
lifts {x = x} ξ = wks ξ , vz x


vars : ∀ {Γ Γ′} → Γ′ ⊇ Γ
                → Γ′ ⊢ Γ alltrue
vars done               = ∙
vars (step {x = x} η i) = vars η , var x i


ids : ∀ {Γ} → Γ ⊢ Γ alltrue
ids = vars id


--------------------------------------------------------------------------------


-- TODO: unfinished
postulate
  oopsₛ : ∀ {Γ Ξ x} → {{_ : T (fresh x Ξ)}}
                    → Γ ⊢ Ξ alltrue
                    → T (fresh x Γ)


sub : ∀ {Γ Ξ A} → Γ ⊢ Ξ alltrue → Ξ ⊢ A true
                → Γ ⊢ A true
sub ξ (var x i)        = get ξ i
sub ξ (lam x 𝒟)        = lam x {{oopsₛ ξ}} (sub (lifts {{oopsₛ ξ}} ξ) 𝒟)
sub ξ (app 𝒟 ℰ)        = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (pair 𝒟 ℰ)       = pair (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (fst 𝒟)          = fst (sub ξ 𝒟)
sub ξ (snd 𝒟)          = snd (sub ξ 𝒟)
sub ξ unit             = unit
sub ξ (abort 𝒟)        = abort (sub ξ 𝒟)
sub ξ (inl 𝒟)          = inl (sub ξ 𝒟)
sub ξ (inr 𝒟)          = inr (sub ξ 𝒟)
sub ξ (case x y 𝒟 ℰ ℱ) = case x y {{oopsₛ ξ}} {{oopsₛ ξ}}
                              (sub ξ 𝒟)
                              (sub (lifts {{oopsₛ ξ}} ξ) ℰ)
                              (sub (lifts {{oopsₛ ξ}} ξ) ℱ)


--------------------------------------------------------------------------------
