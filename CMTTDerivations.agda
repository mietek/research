module CMTTDerivations where

open import Prelude
open import Category
open import Fin
open import Vec
open import VecLemmas
open import AllVec
open import AllVecLemmas
open import CMTTScopes
open import CMTTTypes
open import CMTTTerms


--------------------------------------------------------------------------------


mutual
  infix 3 _⊢_⦂_valid[_]
  data _⊢_⦂_valid[_] : ∀ {d g} → {σ : Scopes d}
                                → Asserts σ → Term σ g → Type → Types g → Set
    where
      var : ∀ {A d g I} → {σ : Scopes d}
                           {Δ : Asserts σ} {Γ : Types g}
                        → Γ ∋⟨ I ⟩ A
                        → Δ ⊢ VAR I ⦂ A valid[ Γ ]

      lam : ∀ {A B d g} → {σ : Scopes d}
                           {Δ : Asserts σ} {Γ : Types g}
                           {M : Term σ (suc g)}
                        → Δ ⊢ M ⦂ B valid[ Γ , A ]
                        → Δ ⊢ LAM M ⦂ A ⊃ B valid[ Γ ]

      app : ∀ {A B d g} → {σ : Scopes d}
                           {Δ : Asserts σ} {Γ : Types g}
                           {M N : Term σ g}
                        → Δ ⊢ M ⦂ A ⊃ B valid[ Γ ] → Δ ⊢ N ⦂ A valid[ Γ ]
                        → Δ ⊢ APP M N ⦂ B valid[ Γ ]

      mvar : ∀ {A m d g I} → {σ : Scopes d}
                              {Ψ : Types m} {Δ : Asserts σ} {Γ : Types g}
                              {i : σ ∋⟨ I ⟩ m} {τ : Terms σ g m}
                           → Δ ∋◇⟨ i ⟩ ⟪ Ψ ⊫ A ⟫ → Δ ⊢ τ ⦂ Ψ allvalid[ Γ ]
                           → Δ ⊢ MVAR i τ ⦂ A valid[ Γ ]

      box : ∀ {A m d g} → {σ : Scopes d}
                           {Ψ : Types m} {Δ : Asserts σ} {Γ : Types g}
                           {M : Term σ m}
                        → Δ ⊢ M ⦂ A valid[ Ψ ]
                        → Δ ⊢ BOX M ⦂ [ Ψ ] A valid[ Γ ]

      letbox : ∀ {A B m d g} → {σ : Scopes d}
                                {Ψ : Types m} {Δ : Asserts σ} {Γ : Types g}
                                {M : Term σ g} {N : Term (σ , m) g}
                             → Δ ⊢ M ⦂ [ Ψ ] A valid[ Γ ] → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ N ⦂ B valid[ Γ ]
                             → Δ ⊢ LETBOX M N ⦂ B valid[ Γ ]


  infix 3 _⊢_⦂_allvalid[_]
  _⊢_⦂_allvalid[_] : ∀ {d g n} → {σ : Scopes d}
                                → Asserts σ → Terms σ g n → Types n → Types g → Set
  Δ ⊢ τ ⦂ Ξ allvalid[ Γ ] = All (\ { (M , A) → Δ ⊢ M ⦂ A valid[ Γ ] }) (zip τ Ξ)


infix 3 _⊢_⦂_allvalid*
_⊢_⦂_allvalid* : ∀ {d n} → {σ : Scopes d} {ρ : Scopes n}
                          → Asserts σ → Terms* σ ρ → Asserts ρ → Set
Δ ⊢ ∙     ⦂ ∙                allvalid* = ⊤
Δ ⊢ τ , M ⦂ (Ξ , ⟪ Ψ ⊫ A ⟫) allvalid* = Δ ⊢ τ ⦂ Ξ allvalid* × Δ ⊢ M ⦂ A valid[ Ψ ]


get◇ : ∀ {d n m I A} → {σ : Scopes d} {ρ : Scopes n} {i : ρ ∋⟨ I ⟩ m}
                        {Δ : Asserts σ} {Ψ : Types m}
                        {τ : Terms* σ ρ} {Ξ : Asserts ρ}
                     → Δ ⊢ τ ⦂ Ξ allvalid* → Ξ ∋◇⟨ i ⟩ ⟪ Ψ ⊫ A ⟫
                     → Δ ⊢ get τ i ⦂ A valid[ Ψ ]
get◇ {τ = τ , M} {Ξ , ⟪ Ψ ⊫ A ⟫} (ξ , 𝒟) zero    = 𝒟
get◇ {τ = τ , N} {Ξ , ⟪ Φ ⊫ B ⟫} (ξ , ℰ) (suc 𝑖) = get◇ ξ 𝑖


-- TODO: Too general?
-- Δ ⊢ τ ⦂ Ξ allvalid* = All◇ (\ { {n , m} (M , ⟪ Ψ ⊫ A ⟫) → Δ ⊢ M ⦂ A valid[ {!Ψ!} ] }) (zips τ Ξ)


--------------------------------------------------------------------------------


mutual
  ren : ∀ {d g g′ e A} → {σ : Scopes d}
                          {Δ : Asserts σ} {Γ : Types g} {Γ′ : Types g′}
                          {M : Term σ g}
                       → Γ′ ⊇⟨ e ⟩ Γ → Δ ⊢ M ⦂ A valid[ Γ ]
                       → Δ ⊢ REN e M ⦂ A valid[ Γ′ ]
  ren η (var i)      = var (ren∋ η i)
  ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
  ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
  ren η (mvar 𝑖 ψ)   = mvar 𝑖 (rens η ψ)
  ren η (box 𝒟)      = box 𝒟
  ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren η ℰ)

  rens : ∀ {d g g′ e n} → {σ : Scopes d}
                           {Δ : Asserts σ} {Γ : Types g} {Γ′ : Types g′}
                           {τ : Terms σ g n} {Ξ : Types n}
                        → Γ′ ⊇⟨ e ⟩ Γ → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ]
                        → Δ ⊢ RENS e τ ⦂ Ξ allvalid[ Γ′ ]
  rens {τ = ∙}     {∙}     η ∙       = ∙
  rens {τ = τ , M} {Ξ , A} η (ξ , 𝒟) = rens η ξ , ren η 𝒟


--------------------------------------------------------------------------------


mutual
  mren : ∀ {d d′ g e A} → {σ : Scopes d} {σ′ : Scopes d′} {η : σ′ ⊇⟨ e ⟩ σ}
                           {Δ : Asserts σ} {Δ′ : Asserts σ′} {Γ : Types g}
                           {M : Term σ g}
                        → Δ′ ⊇◇⟨ η ⟩ Δ → Δ ⊢ M ⦂ A valid[ Γ ]
                        → Δ′ ⊢ MREN η M ⦂ A valid[ Γ ]
  mren 𝜂 (var i)      = var i
  mren 𝜂 (lam 𝒟)      = lam (mren 𝜂 𝒟)
  mren 𝜂 (app 𝒟 ℰ)    = app (mren 𝜂 𝒟) (mren 𝜂 ℰ)
  mren 𝜂 (mvar 𝑖 ψ)   = mvar (ren∋◇ 𝜂 𝑖) (mrens 𝜂 ψ)
  mren 𝜂 (box 𝒟)      = box (mren 𝜂 𝒟)
  mren 𝜂 (letbox 𝒟 ℰ) = letbox (mren 𝜂 𝒟) (mren (keep 𝜂) ℰ)

  mrens : ∀ {d d′ g e n} → {σ : Scopes d} {σ′ : Scopes d′} {η : σ′ ⊇⟨ e ⟩ σ}
                            {Δ : Asserts σ} {Δ′ : Asserts σ′} {Γ : Types g}
                            {τ : Terms σ g n} {Ξ : Types n}
                         → Δ′ ⊇◇⟨ η ⟩ Δ → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ]
                         → Δ′ ⊢ MRENS η τ ⦂ Ξ allvalid[ Γ ]
  mrens {τ = ∙}     {∙}     𝜂 ∙       = ∙
  mrens {τ = τ , M} {Ξ , A} 𝜂 (ξ , 𝒟) = mrens 𝜂 ξ , mren 𝜂 𝒟


mrens* : ∀ {d d′ e n} → {σ : Scopes d} {σ′ : Scopes d′} {η : σ′ ⊇⟨ e ⟩ σ} {ρ : Scopes n}
                         {Δ : Asserts σ} {Δ′ : Asserts σ′}
                         {τ : Terms* σ ρ} {Ξ : Asserts ρ}
                      → Δ′ ⊇◇⟨ η ⟩ Δ → Δ ⊢ τ ⦂ Ξ allvalid*
                      → Δ′ ⊢ MRENS* η τ ⦂ Ξ allvalid*
mrens* {τ = ∙}     {∙}     𝜂 ∙       = ∙
mrens* {τ = τ , M} {Ξ , A} 𝜂 (ξ , 𝒟) = mrens* 𝜂 ξ , mren 𝜂 𝒟


--------------------------------------------------------------------------------


wk : ∀ {B d g A} → {σ : Scopes d}
                    {Δ : Asserts σ} {Γ : Types g}
                    {M : Term σ g}
                 → Δ ⊢ M ⦂ A valid[ Γ ]
                 → Δ ⊢ WK M ⦂ A valid[ Γ , B ]
wk 𝒟 = ren (drop id⊇) 𝒟


wks : ∀ {A d g n} → {σ : Scopes d}
                     {Δ : Asserts σ} {Γ : Types g}
                     {τ : Terms σ g n} {Ξ : Types n}
                  → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ]
                  → Δ ⊢ WKS τ ⦂ Ξ allvalid[ Γ , A ]
wks ξ = rens (drop id⊇) ξ


vz : ∀ {d g A} → {σ : Scopes d}
                  {Δ : Asserts σ} {Γ : Types g}
               → Δ ⊢ VZ ⦂ A valid[ Γ , A ]
vz = var zero


lifts : ∀ {A d g n} → {σ : Scopes d}
                       {Δ : Asserts σ} {Γ : Types g}
                       {τ : Terms σ g n} {Ξ : Types n}
                    → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ]
                    → Δ ⊢ LIFTS τ ⦂ Ξ , A allvalid[ Γ , A ]
lifts ξ = wks ξ , vz


vars : ∀ {d g g′ e} → {σ : Scopes d}
                       {Δ : Asserts σ} {Γ : Types g} {Γ′ : Types g′}
                    → Γ′ ⊇⟨ e ⟩ Γ
                    → Δ ⊢ VARS e ⦂ Γ allvalid[ Γ′ ]
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {d g} → {σ : Scopes d}
                 {Δ : Asserts σ} {Γ : Types g}
              → Δ ⊢ IDS ⦂ Γ allvalid[ Γ ]
ids = vars id⊇


--------------------------------------------------------------------------------


mwk : ∀ {B d g m A} → {σ : Scopes d}
                       {Δ : Asserts σ} {Γ : Types g} {Ψ : Types m}
                       {M : Term σ g}
                    → Δ ⊢ M ⦂ A valid[ Γ ]
                    → Δ , ⟪ Ψ ⊫ B ⟫ ⊢ MWK M ⦂ A valid[ Γ ]
mwk 𝒟 = mren (drop id⊇◇) 𝒟


mwks : ∀ {A d g n m} → {σ : Scopes d}
                        {Δ : Asserts σ} {Γ : Types g} {Ψ : Types m}
                        {τ : Terms σ g n} {Ξ : Types n}
                     → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ]
                     → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ MWKS τ ⦂ Ξ allvalid[ Γ ]
mwks ξ = mrens (drop id⊇◇) ξ


mwks* : ∀ {A d n m} → {σ : Scopes d} {ρ : Scopes n}
                       {Δ : Asserts σ} {Ψ : Types m}
                       {τ : Terms* σ ρ} {Ξ : Asserts ρ}
                    → Δ ⊢ τ ⦂ Ξ allvalid*
                    → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ MWKS* τ ⦂ Ξ allvalid*
mwks* ξ = mrens* (drop id⊇◇) ξ


mvz : ∀ {d g m A} → {σ : Scopes d}
                     {Δ : Asserts σ} {Γ : Types g}
                     {υ : Terms (σ , m) g m} {Ψ : Types m}
                  → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ υ ⦂ Ψ allvalid[ Γ ]
                  → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ MVZ υ ⦂ A valid[ Γ ]
mvz ψ = mvar zero ψ


mlifts* : ∀ {A d n m} → {σ : Scopes d} {ρ : Scopes n}
                         {Δ : Asserts σ} {Ψ : Types m}
                         {τ : Terms* σ ρ} {Ξ : Asserts ρ}
                    → Δ ⊢ τ ⦂ Ξ allvalid*
                    → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ MLIFTS* τ ⦂ Ξ , ⟪ Ψ ⊫ A ⟫ allvalid*
mlifts* ξ = mwks* ξ , mvz ids


mvars* : ∀ {d d′ e} → {σ : Scopes d} {σ′ : Scopes d′} {η : σ′ ⊇⟨ e ⟩ σ}
                       {Δ : Asserts σ} {Δ′ : Asserts σ′}
                    → Δ′ ⊇◇⟨ η ⟩ Δ
                    → Δ′ ⊢ MVARS* η ⦂ Δ allvalid*
mvars* done     = ∙
mvars* (drop 𝜂) = mwks* (mvars* 𝜂)
mvars* (keep 𝜂) = mlifts* (mvars* 𝜂)


mids* : ∀ {d} → {σ : Scopes d}
                 {Δ : Asserts σ}
              → Δ ⊢ MIDS* ⦂ Δ allvalid*
mids* = mvars* id⊇◇


--------------------------------------------------------------------------------


mutual
  sub : ∀ {d g n A} → {σ : Scopes d}
                       {Δ : Asserts σ} {Γ : Types g}
                       {τ : Terms σ g n} {Ξ : Types n} {M : Term σ n}
                    → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ] → Δ ⊢ M ⦂ A valid[ Ξ ]
                    → Δ ⊢ SUB τ M ⦂ A valid[ Γ ]
  sub ξ (var i)      = get ξ (zip∋₂ i)
  sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
  sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
  sub ξ (mvar 𝑖 ψ)   = mvar 𝑖 (subs ξ ψ)
  sub ξ (box 𝒟)      = box 𝒟
  sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)

  subs : ∀ {d g n m} → {σ : Scopes d}
                        {Δ : Asserts σ} {Γ : Types g}
                        {τ : Terms σ g n} {Ξ : Types n} {υ : Terms σ n m} {Ψ : Types m}
                     → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ] → Δ ⊢ υ ⦂ Ψ allvalid[ Ξ ]
                     → Δ ⊢ SUBS τ υ ⦂ Ψ allvalid[ Γ ]
  subs {υ = ∙}     {∙}     ξ ∙       = ∙
  subs {υ = υ , M} {Ψ , A} ξ (ψ , 𝒟) = subs ξ ψ , sub ξ 𝒟


--------------------------------------------------------------------------------


mutual
  msub : ∀ {d g n A} → {σ : Scopes d} {ρ : Scopes n}
                        {Δ : Asserts σ} {Γ : Types g}
                        {τ : Terms* σ ρ} {Ξ : Asserts ρ} {M : Term ρ g}
                     → Δ ⊢ τ ⦂ Ξ allvalid* → Ξ ⊢ M ⦂ A valid[ Γ ]
                     → Δ ⊢ MSUB τ M ⦂ A valid[ Γ ]
  msub ξ (var i)      = var i
  msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
  msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
  msub ξ (mvar 𝑖 ψ)   = sub (msubs ξ ψ) (get◇ ξ 𝑖)
  msub ξ (box 𝒟)      = box (msub ξ 𝒟)
  msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts* ξ) ℰ)

  msubs : ∀ {d g n m} → {σ : Scopes d} {ρ : Scopes n}
                         {Δ : Asserts σ} {Γ : Types g}
                         {τ : Terms* σ ρ} {Ξ : Asserts ρ} {υ : Terms ρ g m} {Ψ : Types m}
                      → Δ ⊢ τ ⦂ Ξ allvalid* → Ξ ⊢ υ ⦂ Ψ allvalid[ Γ ]
                      → Δ ⊢ MSUBS τ υ ⦂ Ψ allvalid[ Γ ]
  msubs {υ = ∙}     {∙}     ξ ∙       = ∙
  msubs {υ = υ , M} {Ψ , A} ξ (ψ , 𝒟) = msubs ξ ψ , msub ξ 𝒟


msubs* : ∀ {d n m} → {σ : Scopes d} {ρ : Scopes n} {π : Scopes m}
                      {Δ : Asserts σ}
                      {τ : Terms* σ ρ} {Ξ : Asserts ρ} {υ : Terms* ρ π} {Ψ : Asserts π}
                   → Δ ⊢ τ ⦂ Ξ allvalid* → Ξ ⊢ υ ⦂ Ψ allvalid*
                   → Δ ⊢ MSUBS* τ υ ⦂ Ψ allvalid*
msubs* {υ = ∙}     {∙}              ξ ∙       = ∙
msubs* {υ = υ , M} {Ψ , ⟪ Φ ⊫ A ⟫} ξ (ψ , 𝒟) = msubs* ξ ψ , msub ξ 𝒟


--------------------------------------------------------------------------------


unlam : ∀ {d g A B} → {σ : Scopes d}
                       {Δ : Asserts σ} {Γ : Types g}
                       {M : Term σ g}
                    → Δ ⊢ M ⦂ A ⊃ B valid[ Γ ]
                    → Δ ⊢ UNLAM M ⦂ B valid[ Γ , A ]
unlam 𝒟 = app (wk 𝒟) vz


cut : ∀ {d g A B} → {σ : Scopes d}
                     {Δ : Asserts σ} {Γ : Types g}
                     {M : Term σ g} {N : Term σ (suc g)}
                  → Δ ⊢ M ⦂ A valid[ Γ ] → Δ ⊢ N ⦂ B valid[ Γ , A ]
                  → Δ ⊢ CUT M N ⦂ B valid[ Γ ]
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


pseudocut : ∀ {d g A B} → {σ : Scopes d}
                           {Δ : Asserts σ} {Γ : Types g}
                           {M : Term σ g} {N : Term σ (suc g)}
                        → Δ ⊢ M ⦂ A valid[ Γ ] → Δ ⊢ N ⦂ B valid[ Γ , A ]
                        → Δ ⊢ PSEUDOCUT M N ⦂ B valid[ Γ ]
pseudocut 𝒟 ℰ = app (lam ℰ) 𝒟


pseudosub : ∀ {d g n A} → {σ : Scopes d}
                           {Δ : Asserts σ} {Γ : Types g}
                           {τ : Terms σ g n} {Ξ : Types n} {M : Term σ n}
                        → Δ ⊢ τ ⦂ Ξ allvalid[ Γ ] → Δ ⊢ M ⦂ A valid[ Ξ ]
                        → Δ ⊢ PSEUDOSUB τ M ⦂ A valid[ Γ ]
pseudosub {τ = ∙}     {∙}     ∙       𝒟 = ren bot⊇ 𝒟
pseudosub {τ = τ , M} {Ξ , B} (ξ , 𝒞) 𝒟 = app (pseudosub ξ (lam 𝒟)) 𝒞


exch : ∀ {d g A B C} → {σ : Scopes d}
                        {Δ : Asserts σ} {Γ : Types g}
                        {M : Term σ (suc (suc g))}
                     → Δ ⊢ M ⦂ C valid[ Γ , A , B ]
                     → Δ ⊢ EXCH M ⦂ C valid[ Γ , B , A ]
exch 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------


vau : ∀ {d g m A B} → {σ : Scopes d}
                       {Δ : Asserts σ} {Γ : Types g} {Ψ : Types m}
                       {M : Term (σ , m) g}
                    → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ M ⦂ B valid[ Γ ]
                    → Δ ⊢ VAU M ⦂ B valid[ Γ , [ Ψ ] A ]
vau 𝒟 = letbox vz (wk 𝒟)


unvau : ∀ {d g m A B} → {σ : Scopes d}
                         {Δ : Asserts σ} {Γ : Types g} {Ψ : Types m}
                         {M : Term σ (suc g)}
                      → Δ ⊢ M ⦂ B valid[ Γ , [ Ψ ] A ]
                      → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ UNVAU M ⦂ B valid[ Γ ]
unvau 𝒟 = app (lam (mwk 𝒟)) (box (mvz ids))


boxapp : ∀ {d g m A B} → {σ : Scopes d}
                          {Δ : Asserts σ} {Γ : Types g} {Ψ : Types m}
                          {M N : Term σ g}
                       → Δ ⊢ M ⦂ [ Ψ ] (A ⊃ B) valid[ Γ ] → Δ ⊢ N ⦂ [ Ψ ] A valid[ Γ ]
                       → Δ ⊢ BOXAPP M N ⦂ [ Ψ ] B valid[ Γ ]
boxapp 𝒟 ℰ = letbox 𝒟 (letbox (mwk ℰ) (box (app (mwk (mvz ids)) (mvz ids))))


unbox : ∀ {d g m A} → {σ : Scopes d}
                       {Δ : Asserts σ} {Γ : Types g} {υ : Terms σ g m} {Ψ : Types m}
                       {M : Term σ g}
                    → Δ ⊢ M ⦂ [ Ψ ] A valid[ Γ ] → Δ ⊢ υ ⦂ Ψ allvalid[ Γ ]
                    → Δ ⊢ UNBOX M υ ⦂ A valid[ Γ ]
unbox 𝒟 ψ = letbox 𝒟 (mvz (mwks ψ))


rebox : ∀ {d g m A} → {σ : Scopes d}
                       {Δ : Asserts σ} {Γ : Types g} {Ψ : Types m}
                       {M : Term σ g}
                    → Δ ⊢ M ⦂ [ Ψ ] A valid[ Γ ]
                    → Δ ⊢ REBOX M ⦂ [ Ψ ] A valid[ Γ ]
rebox 𝒟 = letbox 𝒟 (box (mvz ids))


dupbox : ∀ {d g m l A} → {σ : Scopes d}
                          {Δ : Asserts σ} {Γ : Types g} {Ψ : Types m} {Φ : Types l}
                          {M : Term σ g}
                       → Δ ⊢ M ⦂ [ Ψ ] A valid[ Γ ]
                       → Δ ⊢ DUPBOX M ⦂ [ Φ ] [ Ψ ] A valid[ Γ ]
dupbox 𝒟 = letbox 𝒟 (box (box (mvz ids)))


mcut : ∀ {d g m A B} → {σ : Scopes d}
                        {Δ : Asserts σ} {Γ : Types g} {Ψ : Types m}
                        {M : Term σ m} {N : Term (σ , m) g}
                     → Δ ⊢ M ⦂ A valid[ Ψ ] → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ N ⦂ B valid[ Γ ]
                     → Δ ⊢ MCUT M N ⦂ B valid[ Γ ]
mcut 𝒟 ℰ = msub (mids* , 𝒟) ℰ


pseudomcut : ∀ {d g m A B} → {σ : Scopes d}
                              {Δ : Asserts σ} {Γ : Types g} {Ψ : Types m}
                              {M : Term σ m} {N : Term (σ , m) g}
                           → Δ ⊢ M ⦂ A valid[ Ψ ] → Δ , ⟪ Ψ ⊫ A ⟫ ⊢ N ⦂ B valid[ Γ ]
                           → Δ ⊢ PSEUDOMCUT M N ⦂ B valid[ Γ ]
pseudomcut 𝒟 ℰ = letbox (box 𝒟) ℰ


pseudomsub : ∀ {d g n A} → {σ : Scopes d} {ρ : Scopes n}
                            {Δ : Asserts σ} {Γ : Types g}
                            {τ : Terms* σ ρ} {Ξ : Asserts ρ} {M : Term ρ g}
                         → Δ ⊢ τ ⦂ Ξ allvalid* → Ξ ⊢ M ⦂ A valid[ Γ ]
                         → Δ ⊢ PSEUDOMSUB τ M ⦂ A valid[ Γ ]
pseudomsub {τ = ∙}     {∙}              ∙       𝒟 = mren bot⊇◇ 𝒟
pseudomsub {τ = τ , M} {Ξ , ⟪ Ψ ⊫ A ⟫} (ξ , 𝒞) 𝒟 = app (pseudomsub ξ (lam (vau 𝒟))) (box 𝒞)


mexch : ∀ {d g m l A B C} → {σ : Scopes d}
                             {Δ : Asserts σ} {Γ : Types g} {Ψ : Types m} {Φ : Types l}
                             {M : Term (σ , m , l) g}
                          → Δ , ⟪ Ψ ⊫ A ⟫ , ⟪ Φ ⊫ B ⟫ ⊢ M ⦂ C valid[ Γ ]
                          → Δ , ⟪ Φ ⊫ B ⟫ , ⟪ Ψ ⊫ A ⟫ ⊢ MEXCH M ⦂ C valid[ Γ ]
mexch 𝒟 = unvau (unvau (exch (vau (vau 𝒟))))


--------------------------------------------------------------------------------
