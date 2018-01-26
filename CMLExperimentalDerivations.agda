module CMLExperimentalDerivations where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import CMLPropositions
open import CMLLemmas
import CMLDerivations as CML


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢_valid[_]
  data _⊢_valid[_] : List Assert → Prop → List Prop → Set
    where
      vz : ∀ {A Δ Γ} → Δ ⊢ A valid[ Γ , A ]

      wk : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ]
                       → Δ ⊢ A valid[ Γ , B ]

      cut : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ] → Δ ⊢ B valid[ Γ , A ]
                        → Δ ⊢ B valid[ Γ ]

      lam : ∀ {A B Δ Γ} → Δ ⊢ B valid[ Γ , A ]
                        → Δ ⊢ A ⊃ B valid[ Γ ]

      unlam : ∀ {A B Δ Γ} → Δ ⊢ A ⊃ B valid[ Γ ]
                          → Δ ⊢ B valid[ Γ , A ]

      box : ∀ {A Ψ Δ Γ} → Δ ⊢ A valid[ Ψ ]
                        → Δ ⊢ [ Ψ ] A valid[ Γ ]

      unbox : ∀ {Δ Γ Ψ A} → Δ ⊢ [ Ψ ] A valid[ Γ ] → Δ ⊢ Ψ allvalid[ Γ ]
                          → Δ ⊢ A valid[ Γ ]

      vau : ∀ {A B Ψ Δ Γ} → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ B valid[ Γ ]
                          → Δ ⊢ B valid[ Γ , [ Ψ ] A ]

      unvau : ∀ {A B Ψ Δ Γ} → Δ ⊢ B valid[ Γ , [ Ψ ] A ]
                            → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ B valid[ Γ ]

  infix 3 _⊢_allvalid[_]
  _⊢_allvalid[_] : List Assert → List Prop → List Prop → Set
  Δ ⊢ Ξ allvalid[ Γ ] = All (\ A → Δ ⊢ A valid[ Γ ]) Ξ


infix 3 _⊢_allvalid*
_⊢_allvalid* : List Assert → List Assert → Set
Δ ⊢ Ξ allvalid* = All (\ { ⟪ Γ ⊫ A ⟫ → Δ ⊢ A valid[ Γ ] }) Ξ


--------------------------------------------------------------------------------


wks : ∀ {A Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                  → Δ ⊢ Ξ allvalid[ Γ , A ]
wks ξ = maps wk ξ


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


mwk : ∀ {B Ψ A Δ Γ} → Δ ⊢ A valid[ Γ ]
                    → Δ , ⟪ Ψ ⊫ B ⟫ ⊢ A valid[ Γ ]
mwk 𝒟 = unvau (wk 𝒟)


mvz : ∀ {A Ψ Δ Γ} → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ Ψ allvalid[ Γ ]
                  → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ A valid[ Γ ]
mvz ψ = unbox (unvau vz) ψ


mwks : ∀ {A Ψ Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                     → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ Ξ allvalid[ Γ ]
mwks ξ = maps mwk ξ


mwks* : ∀ {A Ψ Δ Ξ} → Δ ⊢ Ξ allvalid*
                    → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ Ξ allvalid*
mwks* ξ = maps mwk ξ


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


vaus : ∀ {Δ Γ Ξ Ψ A} → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ Ξ allvalid[ Γ ]
                     → Δ ⊢ Ξ allvalid[ Γ , [ Ψ ] A ]
vaus 𝒟 = maps vau 𝒟


-- NOTE: Interesting; similar shape to lift or cut

unnamed : ∀ {Δ Γ Ξ Ψ A} → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ Ξ allvalid[ Γ ]
                        → Δ ⊢ Ξ , [ Ψ ] A allvalid[ Γ , [ Ψ ] A ]
unnamed 𝒟 = vaus 𝒟 , vz


mutual
  sub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid[ Γ ] → Δ ⊢ A valid[ Ξ ]
                    → Δ ⊢ A valid[ Γ ]
  sub (ξ , 𝒞) vz          = 𝒞
  sub (ξ , 𝒞) (wk 𝒟)      = sub ξ 𝒟
  sub ξ       (cut 𝒟 ℰ)   = cut (sub ξ 𝒟) (sub (lifts ξ) ℰ)
  sub ξ       (lam 𝒟)     = lam (sub (lifts ξ) 𝒟)
  sub (ξ , 𝒞) (unlam 𝒟)   = cut 𝒞 (unlam (sub ξ 𝒟))
  sub ξ       (box 𝒟)     = box 𝒟
  sub ξ       (unbox 𝒟 ψ) = unbox (sub ξ 𝒟) (subs ξ ψ)
  sub (ξ , 𝒞) (vau 𝒟)     = cut 𝒞 (vau (sub (mwks ξ) 𝒟))
  sub ξ       (unvau 𝒟)   = unvau (sub (unnamed ξ) 𝒟)  -- NOTE: Interesting

  subs : ∀ {Δ Γ Ξ Ψ} → Δ ⊢ Ξ allvalid[ Γ ] → Δ ⊢ Ψ allvalid[ Ξ ]
                     → Δ ⊢ Ψ allvalid[ Γ ]
  subs ξ ∙       = ∙
  subs ξ (ψ , 𝒟) = subs ξ ψ , sub ξ 𝒟


--------------------------------------------------------------------------------


mutual
  msub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid* → Ξ ⊢ A valid[ Γ ]
                     → Δ ⊢ A valid[ Γ ]
  msub ξ       vz          = vz
  msub ξ       (wk 𝒟)      = wk (msub ξ 𝒟)
  msub ξ       (cut 𝒟 ℰ)   = cut (msub ξ 𝒟) (msub ξ ℰ)
  msub ξ       (lam 𝒟)     = lam (msub ξ 𝒟)
  msub ξ       (unlam 𝒟)   = unlam (msub ξ 𝒟)
  msub ξ       (box 𝒟)     = box (msub ξ 𝒟)
  msub ξ       (unbox 𝒟 ψ) = unbox (msub ξ 𝒟) (msubs ξ ψ)
  msub ξ       (vau 𝒟)     = vau (msub (mlifts* ξ) 𝒟)
  msub (ξ , 𝒞) (unvau 𝒟)   = cut (box 𝒞) (msub ξ 𝒟)  -- NOTE: Interesting

  msubs : ∀ {Δ Γ Ξ Ψ} → Δ ⊢ Ξ allvalid* → Ξ ⊢ Ψ allvalid[ Γ ]
                      → Δ ⊢ Ψ allvalid[ Γ ]
  msubs ξ ∙       = ∙
  msubs ξ (ψ , 𝒟) = msubs ξ ψ , msub ξ 𝒟


msubs* : ∀ {Δ Ξ Ψ} → Δ ⊢ Ξ allvalid* → Ξ ⊢ Ψ allvalid*
                   → Δ ⊢ Ψ allvalid*
msubs* ξ ∙       = ∙
msubs* ξ (ψ , 𝒟) = msubs* ξ ψ , msub ξ 𝒟


--------------------------------------------------------------------------------


var : ∀ {Δ Γ A} → Γ ∋ A
                → Δ ⊢ A valid[ Γ ]
var zero    = vz
var (suc i) = wk (var i)


app : ∀ {Δ Γ A B} → Δ ⊢ A ⊃ B valid[ Γ ] → Δ ⊢ A valid[ Γ ]
                  → Δ ⊢ B valid[ Γ ]
app 𝒟 ℰ = cut ℰ (unlam 𝒟)


mvar : ∀ {Δ Γ Ψ A} → Δ ∋ ⟪ Ψ ⊫ A ⟫ → Δ ⊢ Ψ allvalid[ Γ ]
                   → Δ ⊢ A valid[ Γ ]
mvar zero    ψ = mvz ψ
mvar (suc i) ψ = unvau (mvar i (vaus ψ))


letbox : ∀ {Δ Γ Ψ A B} → Δ ⊢ [ Ψ ] A valid[ Γ ] → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ B valid[ Γ ]
                       → Δ ⊢ B valid[ Γ ]
letbox 𝒟 ℰ = cut 𝒟 (vau ℰ)


-- NOTE: Local completeness of [_]

rebox : ∀ {Δ Γ Ψ A} → Δ ⊢ [ Ψ ] A valid[ Γ ]
                    → Δ ⊢ [ Ψ ] A valid[ Γ ]
rebox 𝒟 = letbox 𝒟 (box (mvz ids))


-- NOTE: Local soundness of [_]

pseudomcut : ∀ {Δ Γ Ψ A B} → Δ ⊢ A valid[ Ψ ] → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ B valid[ Γ ]
                           → Δ ⊢ B valid[ Γ ]
pseudomcut 𝒟 ℰ = letbox (box 𝒟) ℰ


--------------------------------------------------------------------------------



mutual
  ↓ : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
                → Δ CML.⊢ A valid[ Γ ]
  ↓ vz          = CML.vz
  ↓ (wk 𝒟)      = CML.wk (↓ 𝒟)
  ↓ (cut 𝒟 ℰ)   = CML.cut (↓ 𝒟) (↓ ℰ)
  ↓ (lam 𝒟)     = CML.lam (↓ 𝒟)
  ↓ (unlam 𝒟)   = CML.unlam (↓ 𝒟)
  ↓ (box 𝒟)     = CML.box (↓ 𝒟)
  ↓ (unbox 𝒟 ψ) = CML.unbox (↓ 𝒟) (↓ⁿ ψ)
  ↓ (vau 𝒟)     = CML.vau (↓ 𝒟)
  ↓ (unvau 𝒟)   = CML.unvau (↓ 𝒟)

  ↓ⁿ : ∀ {Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                 → Δ CML.⊢ Ξ allvalid[ Γ ]
  ↓ⁿ ∙       = ∙
  ↓ⁿ (ξ , 𝒟) = ↓ⁿ ξ , ↓ 𝒟


mutual
  ↑ : ∀ {Δ Γ A} → Δ CML.⊢ A valid[ Γ ]
                → Δ ⊢ A valid[ Γ ]
  ↑ (CML.var i)      = var i
  ↑ (CML.lam 𝒟)      = lam (↑ 𝒟)
  ↑ (CML.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
  ↑ (CML.mvar i ψ)   = mvar i (↑ⁿ ψ)
  ↑ (CML.box 𝒟)      = box (↑ 𝒟)
  ↑ (CML.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)

  ↑ⁿ : ∀ {Δ Γ Ξ} → Δ CML.⊢ Ξ allvalid[ Γ ]
                 → Δ ⊢ Ξ allvalid[ Γ ]
  ↑ⁿ ∙       = ∙
  ↑ⁿ (ξ , 𝒟) = ↑ⁿ ξ , ↑ 𝒟


lem-var : ∀ {Δ Γ A} → (i : Γ ∋ A)
                    → ↓ {Δ} (var i) ≡ CML.var i
lem-var zero    = refl
lem-var (suc i) = CML.wk & lem-var i
                ⋮ CML.var ∘ suc & id-ren∋ i


-- NOTE: Problematic

-- lem-mvar : ∀ {Δ Γ Ψ A} → (i : Δ ∋ ⟪ Ψ ⊫ A ⟫) (ψ : Δ CML.⊢ Ψ allvalid[ Γ ])
--                        → ↓ {Γ = Γ} (mvar i (↑ⁿ ψ)) ≡ CML.mvar i ψ
-- lem-mvar zero    ψ = {!!} -- CML.unbox (CML.unvau CML.vz) (↓ⁿ (↑ⁿ ψ)) ≡ CML.mvar zero ψ
-- lem-mvar (suc i) ψ = {!!} -- CML.unvau (↓ (mvar i (vaus (↑ⁿ ψ)))) ≡ CML.mvar (suc i) ψ


-- id↓↑ : ∀ {Δ Γ A} → (𝒟 : Δ CML.⊢ A valid[ Γ ])
--                  → (↓ ∘ ↑) 𝒟 ≡ 𝒟
-- id↓↑ (CML.var i)      = lem-var i
-- id↓↑ (CML.lam 𝒟)      = CML.lam & id↓↑ 𝒟
-- id↓↑ (CML.app 𝒟 ℰ)    = CML.app & ( id-cons-wk-sub CML.ids (↓ (↑ ℰ)) (↓ (↑ 𝒟))
--                                 ⋮ id-sub (↓ (↑ 𝒟))
--                                 ⋮ id↓↑ 𝒟
--                                 )
--                               ⊗ id↓↑ ℰ
-- id↓↑ (CML.mvar i ψ)   = lem-mvar i ψ
-- id↓↑ (CML.box 𝒟)      = CML.box & id↓↑ 𝒟
-- id↓↑ (CML.letbox 𝒟 ℰ) = CML.letbox & id↓↑ 𝒟 ⊗ ( id-cons-wk-sub (CML.mwks CML.ids) (CML.mwk (↓ (↑ 𝒟))) (↓ (↑ ℰ))
--                                             ⋮ (\ ξ′ → CML.sub ξ′ (↓ (↑ ℰ))) & id-mrens-ids (drop id)
--                                             ⋮ id-sub (↓ (↑ ℰ))
--                                             ⋮ id↓↑ ℰ
--                                             )


-- NOTE: Problematic

-- id↑↓ : ∀ {Δ Γ A} → (𝒟 : Δ ⊢ A valid[ Γ ])
--                  → (↑ ∘ ↓) 𝒟 ≡ 𝒟
-- id↑↓ vz          = refl
-- id↑↓ (wk 𝒟)      = {!!} -- ↑ (CML.wk (↓ 𝒟)) ≡ wk 𝒟
-- id↑↓ (cut 𝒟 ℰ)   = {!!} -- ↑ (CML.cut (↓ 𝒟) (↓ ℰ)) ≡ cut 𝒟 ℰ
-- id↑↓ (lam 𝒟)     = lam & id↑↓ 𝒟
-- id↑↓ (unlam 𝒟)   = {!!} -- app (↑ (CML.wk (↓ 𝒟))) vz ≡ unlam 𝒟
-- id↑↓ (box 𝒟)     = box & id↑↓ 𝒟
-- id↑↓ (unbox 𝒟 ψ) = {!!} -- letbox (↑ (↓ 𝒟)) (mvz (↑ⁿ (CML.mwks (↓ⁿ ψ)))) ≡ unbox 𝒟 ψ
-- id↑↓ (vau 𝒟)     = {!!} -- letbox vz (↑ (CML.wk (↓ 𝒟))) ≡ vau 𝒟
-- id↑↓ (unvau 𝒟)   = {!!} -- app (lam (↑ (CML.mwk (↓ 𝒟)))) (box (mvz (↑ⁿ CML.ids))) ≡ unvau 𝒟


-- TODO: Semantic equivalence


--------------------------------------------------------------------------------
