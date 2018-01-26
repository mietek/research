module S4ExperimentalDerivations4 where

open import Prelude
open import Category
open import List
open import ListLemmas
open import AllList
open import S4Propositions
open import S4Lemmas
import S4Derivations as S4


--------------------------------------------------------------------------------


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

    box : ∀ {A Δ Γ} → Δ ⊢ A valid[ ∙ ]
                    → Δ ⊢ □ A valid[ Γ ]

    unbox : ∀ {A Δ Γ} → Δ ⊢ □ A valid[ Γ ]
                      → Δ ⊢ A valid[ Γ ]

    vau : ∀ {A B Δ Γ} → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]
                      → Δ ⊢ B valid[ Γ , □ A ]

    unvau : ∀ {A B Δ Γ} → Δ ⊢ B valid[ Γ , □ A ]
                        → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]


infix 3 _⊢_allvalid[_]
_⊢_allvalid[_] : List Assert → List Prop → List Prop → Set
Δ ⊢ Ξ allvalid[ Γ ] = All (\ A → Δ ⊢ A valid[ Γ ]) Ξ


infix 3 _⊢_allvalid*
_⊢_allvalid* : List Assert → List Assert → Set
Δ ⊢ Ξ allvalid* = All (\ { ⟪⊫ A ⟫ → Δ ⊢ A valid[ ∙ ] }) Ξ


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


mwk : ∀ {A B Δ Γ} → Δ ⊢ A valid[ Γ ]
                  → Δ , B ⊢ A valid[ Γ ]
mwk 𝒟 = unvau (wk 𝒟)


mwks : ∀ {A Δ Γ Ξ} → Δ ⊢ Ξ allvalid[ Γ ]
                   → Δ , ⟪⊫ A ⟫ ⊢ Ξ allvalid[ Γ ]
mwks ξ = maps mwk ξ


mwks* : ∀ {A Δ Ξ} → Δ ⊢ Ξ allvalid*
                  → Δ , ⟪⊫ A ⟫ ⊢ Ξ allvalid*
mwks* ξ = maps mwk ξ


mvz : ∀ {A Δ Γ} → Δ , ⟪⊫ A ⟫ ⊢ A valid[ Γ ]
mvz = unbox (unvau vz)


mlifts* : ∀ {A Δ Ξ} → Δ ⊢ Ξ allvalid*
                    → Δ , ⟪⊫ A ⟫ ⊢ Ξ , ⟪⊫ A ⟫ allvalid*
mlifts* ξ = mwks* ξ , mvz


mvars* : ∀ {Δ Δ′} → Δ′ ⊇ Δ
                  → Δ′ ⊢ Δ allvalid*
mvars* done     = ∙
mvars* (drop η) = mwks* (mvars* η)
mvars* (keep η) = mlifts* (mvars* η)


mids* : ∀ {Δ} → Δ ⊢ Δ allvalid*
mids* = mvars* id


--------------------------------------------------------------------------------


vaus : ∀ {Δ Γ Ξ A} → Δ , ⟪⊫ A ⟫ ⊢ Ξ allvalid[ Γ ]
                   → Δ ⊢ Ξ allvalid[ Γ , □ A ]
vaus 𝒟 = maps vau 𝒟


-- NOTE: Interesting; similar shape to lift or cut

unnamed : ∀ {Δ Γ Ξ A} → Δ , ⟪⊫ A ⟫ ⊢ Ξ allvalid[ Γ ]
                      → Δ ⊢ Ξ , □ A allvalid[ Γ , □ A ]
unnamed 𝒟 = vaus 𝒟 , vz


sub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid[ Γ ] → Δ ⊢ A valid[ Ξ ]
                  → Δ ⊢ A valid[ Γ ]
sub (ξ , 𝒞) vz        = 𝒞
sub (ξ , 𝒞) (wk 𝒟)    = sub ξ 𝒟
sub ξ       (cut 𝒟 ℰ) = cut (sub ξ 𝒟) (sub (lifts ξ) ℰ)
sub ξ       (lam 𝒟)   = lam (sub (lifts ξ) 𝒟)
sub (ξ , 𝒞) (unlam 𝒟) = cut 𝒞 (unlam (sub ξ 𝒟))
sub ξ       (box 𝒟)   = box 𝒟
sub ξ       (unbox 𝒟) = unbox (sub ξ 𝒟)
sub (ξ , 𝒞) (vau 𝒟)   = cut 𝒞 (vau (sub (mwks ξ) 𝒟))
sub ξ       (unvau 𝒟) = unvau (sub (unnamed ξ) 𝒟)  -- NOTE: Interesting


--------------------------------------------------------------------------------


msub : ∀ {Δ Γ Ξ A} → Δ ⊢ Ξ allvalid* → Ξ ⊢ A valid[ Γ ]
                   → Δ ⊢ A valid[ Γ ]
msub ξ       vz         = vz
msub ξ       (wk 𝒟)     = wk (msub ξ 𝒟)
msub ξ       (cut 𝒟 ℰ)  = cut (msub ξ 𝒟) (msub ξ ℰ)
msub ξ       (lam 𝒟)    = lam (msub ξ 𝒟)
msub ξ       (unlam 𝒟)  = unlam (msub ξ 𝒟)
msub ξ       (box 𝒟)    = box (msub ξ 𝒟)
msub ξ       (unbox 𝒟)  = unbox (msub ξ 𝒟)
msub ξ       (vau 𝒟)    = vau (msub (mlifts* ξ) 𝒟)
msub (ξ , 𝒞) (unvau 𝒟)  = cut (box 𝒞) (msub ξ 𝒟)  -- NOTE: Interesting


--------------------------------------------------------------------------------


var : ∀ {Δ Γ A} → Γ ∋ A
                → Δ ⊢ A valid[ Γ ]
var zero    = vz
var (suc i) = wk (var i)


app : ∀ {Δ Γ A B} → Δ ⊢ A ⊃ B valid[ Γ ] → Δ ⊢ A valid[ Γ ]
                  → Δ ⊢ B valid[ Γ ]
app 𝒟 ℰ = cut ℰ (unlam 𝒟)


mvar : ∀ {Δ Γ A} → Δ ∋ ⟪⊫ A ⟫
                 → Δ ⊢ A valid[ Γ ]
mvar zero    = mvz
mvar (suc i) = mwk (mvar i)


letbox : ∀ {Δ Γ A B} → Δ ⊢ □ A valid[ Γ ] → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]
                     → Δ ⊢ B valid[ Γ ]
letbox 𝒟 ℰ = cut 𝒟 (vau ℰ)


-- NOTE: Local completeness of □

rebox : ∀ {Δ Γ A} → Δ ⊢ □ A valid[ Γ ]
                  → Δ ⊢ □ A valid[ Γ ]
rebox 𝒟 = letbox 𝒟 (box mvz)


-- NOTE: Local soundness of □

pseudomcut : ∀ {Δ Γ A B} → Δ ⊢ A valid[ ∙ ] → Δ , ⟪⊫ A ⟫ ⊢ B valid[ Γ ]
                         → Δ ⊢ B valid[ Γ ]
pseudomcut 𝒟 ℰ = letbox (box 𝒟) ℰ


--------------------------------------------------------------------------------


↓ : ∀ {Δ Γ A} → Δ ⊢ A valid[ Γ ]
              → Δ S4.⊢ A valid[ Γ ]
↓ vz        = S4.vz
↓ (wk 𝒟)    = S4.wk (↓ 𝒟)
↓ (cut 𝒟 ℰ) = S4.cut (↓ 𝒟) (↓ ℰ)
↓ (lam 𝒟)   = S4.lam (↓ 𝒟)
↓ (unlam 𝒟) = S4.unlam (↓ 𝒟)
↓ (box 𝒟)   = S4.box (↓ 𝒟)
↓ (unbox 𝒟) = S4.unbox (↓ 𝒟)
↓ (vau 𝒟)   = S4.vau (↓ 𝒟)
↓ (unvau 𝒟) = S4.unvau (↓ 𝒟)


↑ : ∀ {Δ Γ A} → Δ S4.⊢ A valid[ Γ ]
              → Δ ⊢ A valid[ Γ ]
↑ (S4.var i)      = var i
↑ (S4.lam 𝒟)      = lam (↑ 𝒟)
↑ (S4.app 𝒟 ℰ)    = app (↑ 𝒟) (↑ ℰ)
↑ (S4.mvar i)     = mvar i
↑ (S4.box 𝒟)      = box (↑ 𝒟)
↑ (S4.letbox 𝒟 ℰ) = letbox (↑ 𝒟) (↑ ℰ)


lem-var : ∀ {Δ Γ A} → (i : Γ ∋ A)
                    → ↓ {Δ} (var i) ≡ S4.var i
lem-var zero    = refl
lem-var (suc i) = S4.wk & lem-var i
                ⋮ S4.var ∘ suc & id-ren∋ i


-- NOTE: Problematic

-- lem-mvar : ∀ {Δ Γ A} → (i : Δ ∋ ⟪⊫ A ⟫)
--                      → ↓ {Γ = Γ} (mvar i) ≡ S4.mvar i
-- lem-mvar zero    = {!!} -- S4.unbox (S4.unvau S4.vz) ≡ S4.mvar zero
-- lem-mvar (suc i) = {!!} -- S4.unvau (S4.wk (↓ (mvar i))) ≡ S4.mvar (suc i)


-- id↓↑ : ∀ {Δ Γ A} → (𝒟 : Δ S4.⊢ A valid[ Γ ])
--                  → (↓ ∘ ↑) 𝒟 ≡ 𝒟
-- id↓↑ (S4.var i)      = lem-var i
-- id↓↑ (S4.lam 𝒟)      = S4.lam & id↓↑ 𝒟
-- id↓↑ (S4.app 𝒟 ℰ)    = S4.app & ( id-cons-wk-sub S4.ids (↓ (↑ ℰ)) (↓ (↑ 𝒟))
--                                 ⋮ id-sub (↓ (↑ 𝒟))
--                                 ⋮ id↓↑ 𝒟
--                                 )
--                               ⊗ id↓↑ ℰ
-- id↓↑ (S4.mvar i)     = lem-mvar i
-- id↓↑ (S4.box 𝒟)      = S4.box & id↓↑ 𝒟
-- id↓↑ (S4.letbox 𝒟 ℰ) = S4.letbox & id↓↑ 𝒟 ⊗ ( id-cons-wk-sub (S4.mwks S4.ids) (S4.mwk (↓ (↑ 𝒟))) (↓ (↑ ℰ))
--                                             ⋮ (\ ξ′ → S4.sub ξ′ (↓ (↑ ℰ))) & id-mrens-ids (drop id)
--                                             ⋮ id-sub (↓ (↑ ℰ))
--                                             ⋮ id↓↑ ℰ
--                                             )


-- NOTE: Problematic

-- id↑↓ : ∀ {Δ Γ A} → (𝒟 : Δ ⊢ A valid[ Γ ])
--                  → (↑ ∘ ↓) 𝒟 ≡ 𝒟
-- id↑↓ vz        = refl
-- id↑↓ (wk 𝒟)    = {!!} -- ↑ (S4.wk (↓ 𝒟)) ≡ wk 𝒟
-- id↑↓ (cut 𝒟 ℰ) = {!!} -- ↑ (S4.cut (↓ 𝒟) (↓ ℰ)) ≡ cut 𝒟 ℰ
-- id↑↓ (lam 𝒟)   = lam & id↑↓ 𝒟
-- id↑↓ (unlam 𝒟) = {!!} -- app (↑ (S4.wk (↓ 𝒟))) vz ≡ unlam 𝒟
-- id↑↓ (box 𝒟)   = box & id↑↓ 𝒟
-- id↑↓ (unbox 𝒟) = {!!} -- letbox (↑ (↓ 𝒟)) mvz ≡ unbox 𝒟
-- id↑↓ (vau 𝒟)   = {!!} -- letbox vz (↑ (S4.wk (↓ 𝒟))) ≡ vau 𝒟
-- id↑↓ (unvau 𝒟) = {!!} -- app (lam (↑ (S4.mwk (↓ 𝒟)))) (box mvz) ≡ unvau 𝒟


-- TODO: Semantic equivalence


--------------------------------------------------------------------------------
