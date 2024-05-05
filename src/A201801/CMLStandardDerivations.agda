module A201801.CMLStandardDerivations where

open import A201801.Prelude
open import A201801.Category
open import A201801.List
open import A201801.ListLemmas
open import A201801.AllList
open import A201801.CMLPropositions


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢_valid[_]
  data _⊢_valid[_] : List Assert → Form → List Form → Set
    where
      var : ∀ {A Δ Γ} → Γ ∋ A
                      → Δ ⊢ A valid[ Γ ]

      lam : ∀ {A B Δ Γ} → Δ ⊢ B valid[ Γ , A ]
                        → Δ ⊢ A ⊃ B valid[ Γ ]

      app : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B valid[ Γ ] → Δ ⊢ A valid[ Γ ]
                        → Δ ⊢ B valid[ Γ ]

      mvar : ∀ {A Ψ Δ Γ} → Δ ∋ ⟪ Ψ ⊫ A ⟫ → Δ ⊢ Ψ allvalid[ Γ ]
                         → Δ ⊢ A valid[ Γ ]

      box : ∀ {A Ψ Δ Γ} → Δ ⊢ A valid[ Ψ ]
                        → Δ ⊢ [ Ψ ] A valid[ Γ ]

      letbox : ∀ {A B Ψ Δ Γ} → Δ ⊢ [ Ψ ] A valid[ Γ ] → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ B valid[ Γ ]
                             → Δ ⊢ B valid[ Γ ]

  infix 3 _⊢_allvalid[_]
  _⊢_allvalid[_] : List Assert → List Form → List Form → Set
  Δ ⊢ Ξ allvalid[ Γ ] = All (\ A → Δ ⊢ A valid[ Γ ]) Ξ


infix 3 _⊢_allvalid*
_⊢_allvalid* : List Assert → List Assert → Set
Δ ⊢ Ξ allvalid* = All (\ { ⟪ Γ ⊫ A ⟫ → Δ ⊢ A valid[ Γ ] }) Ξ


--------------------------------------------------------------------------------


mutual
  ren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⊢ A valid[ Γ ]
                     → Δ ⊢ A valid[ Γ′ ]
  ren η (var i)      = var (ren∋ η i)
  ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
  ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
  ren η (mvar i ψ)   = mvar i (rens η ψ)
  ren η (box 𝒟)      = box 𝒟
  ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren η ℰ)

  rens : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⊢ Ξ allvalid[ Γ ]
                      → Δ ⊢ Ξ allvalid[ Γ′ ]
  rens η ∙       = ∙
  rens η (ξ , 𝒟) = rens η ξ , ren η 𝒟


--------------------------------------------------------------------------------


mutual
  mren : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⊢ A valid[ Γ ]
                      → Δ′ ⊢ A valid[ Γ ]
  mren η (var i)      = var i
  mren η (lam 𝒟)      = lam (mren η 𝒟)
  mren η (app 𝒟 ℰ)    = app (mren η 𝒟) (mren η ℰ)
  mren η (mvar i ψ)   = mvar (ren∋ η i) (mrens η ψ)
  mren η (box 𝒟)      = box (mren η 𝒟)
  mren η (letbox 𝒟 ℰ) = letbox (mren η 𝒟) (mren (keep η) ℰ)

  mrens : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⊢ Ξ allvalid[ Γ ]
                       → Δ′ ⊢ Ξ allvalid[ Γ ]
  mrens η ∙       = ∙
  mrens η (ξ , 𝒟) = mrens η ξ , mren η 𝒟


mrens* : ∀ {Δ Δ′ Ξ} → Δ′ ⊇ Δ → Δ ⊢ Ξ allvalid*
                    → Δ′ ⊢ Ξ allvalid*
mrens* η ξ = maps (mren η) ξ


--------------------------------------------------------------------------------


wk : ∀ {B Δ Γ A} → Δ ⊢ A valid[ Γ ]
                 → Δ ⊢ A valid[ Γ , B ]
wk 𝒟 = ren (drop id) 𝒟


wks : ∀ {A Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                  → Δ ⊢ Ξ allvalid[ Γ , A ]
wks ξ = rens (drop id) ξ


vz : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ , A ]
vz = var zero


lifts : ∀ {A Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                    → Δ ⊢ Ξ , A allvalid[ Γ , A ]
lifts ξ = wks ξ , vz


vars : ∀ {Δ Γ Γ′} → Γ′ ⊇ Γ
                  → Δ ⊢ Γ allvalid[ Γ′ ]
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {Δ Γ} → Δ ⊢ Γ allvalid[ Γ ]
ids = vars id


--------------------------------------------------------------------------------


mwk : ∀ {B Ψ Δ Γ A} → Δ ⊢ A valid[ Γ ]
                    → Δ , ⟪ Ψ ⊫ B ⟫ ⊢ A valid[ Γ ]
mwk 𝒟 = mren (drop id) 𝒟


mwks : ∀ {A Ψ Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                     → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ Ξ allvalid[ Γ ]
mwks ξ = mrens (drop id) ξ


mwks* : ∀ {A Ψ Δ Ξ} → Δ ⊢ Ξ allvalid*
                    → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ Ξ allvalid*
mwks* ξ = mrens* (drop id) ξ


mvz : ∀ {Δ Γ Ψ A} → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ Ψ allvalid[ Γ ]
                  → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ A valid[ Γ ]
mvz ψ = mvar zero ψ


mlifts* : ∀ {A Ψ Δ Ξ} → Δ ⊢ Ξ allvalid*
                      → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ Ξ , ⟪ Ψ ⊫ A ⟫ allvalid*
mlifts* ξ = mwks* ξ , mvz ids


mvars* : ∀ {Δ Δ′} → Δ′ ⊇ Δ
                  → Δ′ ⊢ Δ allvalid*
mvars* done     = ∙
mvars* (drop η) = mwks* (mvars* η)
mvars* (keep η) = mlifts* (mvars* η)


mids* : ∀ {Δ} → Δ ⊢ Δ allvalid*
mids* = mvars* id


--------------------------------------------------------------------------------


mutual
  sub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid[ Γ ] → Δ ⊢ A valid[ Ξ ]
                    → Δ ⊢ A valid[ Γ ]
  sub ξ (var i)      = get ξ i
  sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
  sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
  sub ξ (mvar i ψ)   = mvar i (subs ξ ψ)
  sub ξ (box 𝒟)      = box 𝒟
  sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)

  subs : ∀ {Δ Γ Ξ Ψ} → Δ ⊢ Ξ allvalid[ Γ ] → Δ ⊢ Ψ allvalid[ Ξ ]
                     → Δ ⊢ Ψ allvalid[ Γ ]
  subs ξ ∙       = ∙
  subs ξ (ψ , 𝒟) = subs ξ ψ , sub ξ 𝒟


--------------------------------------------------------------------------------


mutual
  msub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid* → Ξ ⊢ A valid[ Γ ]
                     → Δ ⊢ A valid[ Γ ]
  msub ξ (var i)      = var i
  msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
  msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
  msub ξ (mvar i ψ)   = sub (msubs ξ ψ) (get ξ i)
  msub ξ (box 𝒟)      = box (msub ξ 𝒟)
  msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts* ξ) ℰ)

  msubs : ∀ {Δ Γ Ξ Ψ} → Δ ⊢ Ξ allvalid* → Ξ ⊢ Ψ allvalid[ Γ ]
                      → Δ ⊢ Ψ allvalid[ Γ ]
  msubs ξ ∙       = ∙
  msubs ξ (ψ , 𝒟) = msubs ξ ψ , msub ξ 𝒟


msubs* : ∀ {Δ Ξ Ψ} → Δ ⊢ Ξ allvalid* → Ξ ⊢ Ψ allvalid*
                   → Δ ⊢ Ψ allvalid*
msubs* ξ ψ = maps (msub ξ) ψ


--------------------------------------------------------------------------------


unlam : ∀ {Δ Γ A B} → Δ ⊢ A ⊃ B valid[ Γ ]
                    → Δ ⊢ B valid[ Γ , A ]
unlam 𝒟 = app (wk 𝒟) vz


cut : ∀ {Δ Γ A B} → Δ ⊢ A valid[ Γ ] → Δ ⊢ B valid[ Γ , A ]
                  → Δ ⊢ B valid[ Γ ]
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


pseudocut : ∀ {Δ Γ A B} → Δ ⊢ A valid[ Γ ] → Δ ⊢ B valid[ Γ , A ]
                        → Δ ⊢ B valid[ Γ ]
pseudocut 𝒟 ℰ = app (lam ℰ) 𝒟


pseudosub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid[ Γ ] → Δ ⊢ A valid[ Ξ ]
                        → Δ ⊢ A valid[ Γ ]
pseudosub ∙       𝒟 = ren bot⊇ 𝒟
pseudosub (ξ , 𝒞) 𝒟 = app (pseudosub ξ (lam 𝒟)) 𝒞


exch : ∀ {Δ Γ A B C} → Δ ⊢ C valid[ (Γ , A) , B ]
                     → Δ ⊢ C valid[ (Γ , B) , A ]
exch 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------


vau : ∀ {Δ Γ Ψ A B} → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ B valid[ Γ ]
                    → Δ ⊢ B valid[ Γ , [ Ψ ] A ]
vau 𝒟 = letbox vz (wk 𝒟)


unvau : ∀ {Δ Γ Ψ A B} → Δ ⊢ B valid[ Γ , [ Ψ ] A ]
                      → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ B valid[ Γ ]
unvau 𝒟 = app (lam (mwk 𝒟)) (box (mvz ids))


boxapp : ∀ {Δ Γ Ψ A B} → Δ ⊢ [ Ψ ] (A ⊃ B) valid[ Γ ] → Δ ⊢ [ Ψ ] A valid[ Γ ]
                       → Δ ⊢ [ Ψ ] B valid[ Γ ]
boxapp 𝒟 ℰ = letbox 𝒟 (letbox (mwk ℰ) (box (app (mwk (mvz ids)) (mvz ids))))


unbox : ∀ {Δ Γ Ψ A} → Δ ⊢ [ Ψ ] A valid[ Γ ] → Δ ⊢ Ψ allvalid[ Γ ]
                    → Δ ⊢ A valid[ Γ ]
unbox 𝒟 ψ = letbox 𝒟 (mvz (mwks ψ))


-- NOTE: Local completeness of [_]

rebox : ∀ {Δ Γ Ψ A} → Δ ⊢ [ Ψ ] A valid[ Γ ]
                    → Δ ⊢ [ Ψ ] A valid[ Γ ]
rebox 𝒟 = letbox 𝒟 (box (mvz ids))


dupbox : ∀ {Δ Γ Ψ Φ A} → Δ ⊢ [ Ψ ] A valid[ Γ ]
                       → Δ ⊢ [ Φ ] [ Ψ ] A valid[ Γ ]
dupbox 𝒟 = letbox 𝒟 (box (box (mvz ids)))


boxapp₀ : ∀ {Δ Γ A B} → Δ ⊢ [ ∙ ] (A ⊃ B) valid[ Γ ] → Δ ⊢ [ ∙ ] A valid[ Γ ]
                      → Δ ⊢ [ ∙ ] B valid[ Γ ]
boxapp₀ 𝒟 ℰ = boxapp 𝒟 ℰ


unbox₀ : ∀ {Δ Γ A} → Δ ⊢ [ ∙ ] A valid[ Γ ]
                   → Δ ⊢ A valid[ Γ ]
unbox₀ 𝒟 = unbox 𝒟 ∙


dupbox₀ : ∀ {Δ Γ A} → Δ ⊢ [ ∙ ] A valid[ Γ ]
                    → Δ ⊢ [ ∙ ] [ ∙ ] A valid[ Γ ]
dupbox₀ 𝒟 = dupbox 𝒟


mcut : ∀ {Δ Γ Ψ A B} → Δ ⊢ A valid[ Ψ ] → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ B valid[ Γ ]
                     → Δ ⊢ B valid[ Γ ]
mcut 𝒟 ℰ = msub (mids* , 𝒟) ℰ


-- NOTE: Local soundness of [_]

pseudomcut : ∀ {Δ Γ Ψ A B} → Δ ⊢ A valid[ Ψ ] → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ B valid[ Γ ]
                           → Δ ⊢ B valid[ Γ ]
pseudomcut 𝒟 ℰ = letbox (box 𝒟) ℰ


-- NOTE: Interesting

pseudomcut′ : ∀ {Δ Γ Ψ A B} → Δ ⊢ A valid[ Ψ ] → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ B valid[ Γ ]
                            → Δ ⊢ B valid[ Γ ]
pseudomcut′ 𝒟 ℰ = mcut 𝒟 (unbox (box ℰ) ids)


pseudomsub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid* → Ξ ⊢ A valid[ Γ ]
                         → Δ ⊢ A valid[ Γ ]
pseudomsub ∙       𝒟 = mren bot⊇ 𝒟
pseudomsub (ξ , 𝒞) 𝒟 = app (pseudomsub ξ (lam (vau 𝒟))) (box 𝒞)


mexch : ∀ {Δ Γ Ψ Φ A B C} → (Δ , ⟪ Ψ ⊫ A ⟫) , ⟪ Φ ⊫ B ⟫ ⊢ C valid[ Γ ]
                          → (Δ , ⟪ Φ ⊫ B ⟫) , ⟪ Ψ ⊫ A ⟫ ⊢ C valid[ Γ ]
mexch 𝒟 = unvau (unvau (exch (vau (vau 𝒟))))


--------------------------------------------------------------------------------
