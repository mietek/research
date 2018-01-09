module StdCMTT where

open import Prelude
open import Fin
open import Vec
open import AllVec
open import StdCMTTTerms


--------------------------------------------------------------------------------


mutual
  infixr 8 _⊃_
  data Prop : Set
    where
      BASE : Prop
      _⊃_  : Prop → Prop → Prop
      [_]_ : ∀ {g} → Truths g → Prop → Prop

  infix 7 _true
  record Truth : Set
    where
      inductive
      constructor _true
      field
        A : Prop

  Truths : Nat → Set
  Truths g = Vec Truth g


infix 7 _valid[_]
record Validity (m : Nat) : Set
  where
    constructor _valid[_]
    field
      A : Prop
      Ψ : Truths m


Validities : ∀ {d} → Scopes d → Set
Validities σ = All Validity σ


--------------------------------------------------------------------------------


record Derivation {d} (σ : Scopes d) : Set
  where
    constructor [_⊢_⦂_]
    field
      {g} : Nat
      Γ   : Truths g
      M   : Term σ g
      Aₜ  : Truth


zap : ∀ {d g n} → {σ : Scopes d}
                → Truths g → Terms σ g n → Truths n
                → Vec (Derivation σ) n
zap Γ ∙       ∙            = ∙
zap Γ (x , M) (Ξ , A true) = zap Γ x Ξ , [ Γ ⊢ M ⦂ A true ]


zap∋ : ∀ {d g n i A} → {σ : Scopes d} {Γ : Truths g}
                        {x : Terms σ g n} {Ξ : Truths n}
                     → Ξ ∋⟨ i ⟩ A true
                     → zap Γ x Ξ ∋⟨ i ⟩ [ Γ ⊢ GET x i ⦂ A true ]
zap∋ {x = x , M} {Ξ , A true} zero    = zero
zap∋ {x = x , N} {Ξ , B true} (suc 𝒾) = suc (zap∋ 𝒾)


record Derivations {d} (σ : Scopes d) : Set
  where
    constructor [_⊢⋆_⦂_]
    field
      {g} : Nat
      {n} : Nat
      Γ   : Truths g
      x   : Terms σ g n
      Ξ   : Truths n


mutual
  infix 3 _⋙_
  data _⋙_ : ∀ {d} → {σ : Scopes d} → Validities σ → Derivation σ → Set
    where
      var : ∀ {A d g i} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                        → Γ ∋⟨ i ⟩ A true
                        → Δ ⋙ [ Γ ⊢ VAR i ⦂ A true ]

      lam : ∀ {A B d g} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                           {M : Term σ (suc g)}
                        → Δ ⋙ [ Γ , A true ⊢ M ⦂ B true ]
                        → Δ ⋙ [ Γ ⊢ LAM M ⦂ A ⊃ B true ]

      app : ∀ {A B d g} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                           {M N : Term σ g}
                        → Δ ⋙ [ Γ ⊢ M ⦂ A ⊃ B true ] → Δ ⋙ [ Γ ⊢ N ⦂ A true ]
                        → Δ ⋙ [ Γ ⊢ APP M N ⦂ B true ]

      mvar : ∀ {A m d g i} → {Ψ : Truths m} {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                              {𝒾 : σ ∋⟨ i ⟩ m} {x : Terms σ g m}
                           → Δ ∋◇⟨ 𝒾 ⟩ A valid[ Ψ ] → Δ ⋙⋆ [ Γ ⊢⋆ x ⦂ Ψ ]
                           → Δ ⋙ [ Γ ⊢ MVAR 𝒾 x ⦂ A true ]

      box : ∀ {A m d g} → {Ψ : Truths m} {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                           {M : Term σ m}
                        → Δ ⋙ [ Ψ ⊢ M ⦂ A true ]
                        → Δ ⋙ [ Γ ⊢ BOX M ⦂ [ Ψ ] A true ]

      letbox : ∀ {A B m d g} → {Ψ : Truths m} {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                                {M : Term σ g} {N : Term (σ , m) g}
                             → Δ ⋙ [ Γ ⊢ M ⦂ [ Ψ ] A true ] → Δ , A valid[ Ψ ] ⋙ [ Γ ⊢ N ⦂ B true ]
                             → Δ ⋙ [ Γ ⊢ LETBOX M N ⦂ B true ]

  infix 3 _⋙⋆_
  _⋙⋆_ : ∀ {d} → {σ : Scopes d} → Validities σ → Derivations σ → Set
  Δ ⋙⋆ [ Γ ⊢⋆ x ⦂ Ξ ] = All (Δ ⋙_) (zap Γ x Ξ)


--------------------------------------------------------------------------------


mutual
  ren : ∀ {d g g′ e A} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g} {Γ′ : Truths g′}
                          {M : Term σ g}
                       → Γ′ ⊇⟨ e ⟩ Γ → Δ ⋙ [ Γ ⊢ M ⦂ A true ]
                       → Δ ⋙ [ Γ′ ⊢ REN e M ⦂ A true ]
  ren η (var 𝒾)      = var (ren∋ η 𝒾)
  ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
  ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
  ren η (mvar `𝒾 ψ)  = mvar `𝒾 (rens η ψ)
  ren η (box 𝒟)      = box 𝒟
  ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren η ℰ)

  rens : ∀ {d g g′ e n} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g} {Γ′ : Truths g′}
                           {x : Terms σ g n} {Ξ : Truths n}
                        → Γ′ ⊇⟨ e ⟩ Γ → Δ ⋙⋆ [ Γ ⊢⋆ x ⦂ Ξ ]
                        → Δ ⋙⋆ [ Γ′ ⊢⋆ RENS e x ⦂ Ξ ]
  rens {x = ∙}     {∙}          η ∙       = ∙
  rens {x = x , M} {Ξ , A true} η (ξ , 𝒟) = rens η ξ , ren η 𝒟
  -- NOTE: Equivalent to
  -- rens η ξ = maps (ren η) ξ


wk : ∀ {B d g A} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                    {M : Term σ g}
                 → Δ ⋙ [ Γ ⊢ M ⦂ A true ]
                 → Δ ⋙ [ Γ , B true ⊢ WK M ⦂ A true ]
wk 𝒟 = ren (drop id⊇) 𝒟


vz : ∀ {d g A} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
               → Δ ⋙ [ Γ , A true ⊢ VZ ⦂ A true ]
vz = var zero


wks : ∀ {d g n A} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                     {x : Terms σ g n} {Ξ : Truths n}
                  → Δ ⋙⋆ [ Γ ⊢⋆ x ⦂ Ξ ]
                  → Δ ⋙⋆ [ Γ , A true ⊢⋆ WKS x ⦂ Ξ ]
wks ξ = rens (drop id⊇) ξ


lifts : ∀ {d g n A} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                       {x : Terms σ g n} {Ξ : Truths n}
                    → Δ ⋙⋆ [ Γ ⊢⋆ x ⦂ Ξ ]
                    → Δ ⋙⋆ [ Γ , A true ⊢⋆ LIFTS x ⦂ Ξ , A true ]
lifts ξ = wks ξ , vz


ids : ∀ {d g} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
              → Δ ⋙⋆ [ Γ ⊢⋆ IDS ⦂ Γ ]
ids {Γ = ∙}          = ∙
ids {Γ = Γ , A true} = lifts ids


--------------------------------------------------------------------------------


mutual
  mren : ∀ {d d′ g e A} → {σ : Scopes d} {σ′ : Scopes d′} {η : σ′ ⊇⟨ e ⟩ σ}
                           {Δ : Validities σ} {Δ′ : Validities σ′} {Γ : Truths g}
                           {M : Term σ g}
                        → Δ′ ⊇◇⟨ η ⟩ Δ → Δ ⋙ [ Γ ⊢ M ⦂ A true ]
                        → Δ′ ⋙ [ Γ ⊢ MREN η M ⦂ A true ]
  mren `η (var 𝒾)      = var 𝒾
  mren `η (lam 𝒟)      = lam (mren `η 𝒟)
  mren `η (app 𝒟 ℰ)    = app (mren `η 𝒟) (mren `η ℰ)
  mren `η (mvar `𝒾 ψ)  = mvar (ren∋◇ `η `𝒾) (mrens `η ψ)
  mren `η (box 𝒟)      = box (mren `η 𝒟)
  mren `η (letbox 𝒟 ℰ) = letbox (mren `η 𝒟) (mren (keep `η) ℰ)

  mrens : ∀ {d d′ g e n} → {σ : Scopes d} {σ′ : Scopes d′} {η : σ′ ⊇⟨ e ⟩ σ}
                            {Δ : Validities σ} {Δ′ : Validities σ′} {Γ : Truths g}
                            {x : Terms σ g n} {Ξ : Truths n}
                         → Δ′ ⊇◇⟨ η ⟩ Δ → Δ ⋙⋆ [ Γ ⊢⋆ x ⦂ Ξ ]
                         → Δ′ ⋙⋆ [ Γ ⊢⋆ MRENS η x ⦂ Ξ ]
  mrens {x = ∙}     {∙}          `η ∙       = ∙
  mrens {x = x , M} {Ξ , A true} `η (ξ , 𝒟) = mrens `η ξ , mren `η 𝒟
  -- NOTE: Equivalent to
  -- mrens `η ξ = maps (mren `η) ξ


mwk : ∀ {B m d g A} → {Ψ : Truths m} {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                       {M : Term σ g}
                    → Δ ⋙ [ Γ ⊢ M ⦂ A true ]
                    → Δ , B valid[ Ψ ] ⋙ [ Γ ⊢ MWK M ⦂ A true ]
mwk 𝒟 = mren (drop id⊇◇) 𝒟


mwks : ∀ {m d g n A} → {Ψ : Truths m} {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                        {x : Terms σ g n} {Ξ : Truths n}
                     → Δ ⋙⋆ [ Γ ⊢⋆ x ⦂ Ξ ]
                     → Δ , A valid[ Ψ ] ⋙⋆ [ Γ ⊢⋆ MWKS x ⦂ Ξ ]
mwks ξ = mrens (drop id⊇◇) ξ


mvz : ∀ {m d g A} → {Ψ : Truths m} {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                     {y : Terms σ g m}
                  → Δ ⋙⋆ [ Γ ⊢⋆ y ⦂ Ψ ]
                  → Δ , A valid[ Ψ ] ⋙ [ Γ ⊢ MVZ y ⦂ A true ]
mvz ψ = mvar zero (mwks ψ)


--------------------------------------------------------------------------------


mutual
  sub : ∀ {d g n A} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                       {x : Terms σ g n} {Ξ : Truths n} {M : Term σ n}
                    → Δ ⋙⋆ [ Γ ⊢⋆ x ⦂ Ξ ] → Δ ⋙ [ Ξ ⊢ M ⦂ A true ]
                    → Δ ⋙ [ Γ ⊢ SUB x M ⦂ A true ]
  sub ξ (var 𝒾)      = get ξ (zap∋ 𝒾)
  sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
  sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
  sub ξ (mvar `𝒾 ψ)  = mvar `𝒾 (subs ξ ψ)
  sub ξ (box 𝒟)      = box 𝒟
  sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)

  subs : ∀ {d g n m} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                        {x : Terms σ g n} {Ξ : Truths n} {y : Terms σ n m} {Ψ : Truths m}
                     → Δ ⋙⋆ [ Γ ⊢⋆ x ⦂ Ξ ] → Δ ⋙⋆ [ Ξ ⊢⋆ y ⦂ Ψ ]
                     → Δ ⋙⋆ [ Γ ⊢⋆ SUBS x y ⦂ Ψ ]
  subs {y = ∙}     {∙}          ξ ∙       = ∙
  subs {y = y , M} {Ψ , A true} ξ (ψ , 𝒟) = subs ξ ψ , sub ξ 𝒟
  -- NOTE: Equivalent to
  -- subs ξ ψ = maps (sub ξ) ψ


cut : ∀ {d g A B} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                     {M : Term σ g} {N : Term σ (suc g)}
                  → Δ ⋙ [ Γ ⊢ M ⦂ A true ] → Δ ⋙ [ Γ , A true ⊢ N ⦂ B true ]
                  → Δ ⋙ [ Γ ⊢ CUT M N ⦂ B true ]
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


--------------------------------------------------------------------------------


record Derivation₁ {d} (σ : Scopes d) : Set
  where
    constructor [∙⊢₁_⦂_]
    field
      {m} : Nat
      M   : Term₁ σ m
      Aᵥ  : Validity m


record Derivations₁ {d} (σ : Scopes d) : Set
  where
    constructor [∙⊢⋆₁_⦂_]
    field
      {n} : Nat
      {ξ} : Scopes n
      x   : Terms₁ σ ξ
      Ξ   : Validities ξ


zap₁ : ∀ {d n} → {σ : Scopes d} {ξ : Scopes n}
               → Terms₁ σ ξ → Validities ξ
               → Vec (Derivation₁ σ) n
zap₁ ∙       ∙                  = ∙
zap₁ (x , M) (Ξ , A valid[ Ψ ]) = zap₁ x Ξ , [∙⊢₁ M ⦂ A valid[ Ψ ] ]

zap∋₁ : ∀ {m d n i A} → {Ψ : Truths m} {σ : Scopes d} {ξ : Scopes n}
                         {x : Terms₁ σ ξ} {Ξ : Validities ξ} {𝒾 : ξ ∋⟨ i ⟩ m}
                      → Ξ ∋◇⟨ 𝒾 ⟩ A valid[ Ψ ]
                      → zap₁ x Ξ ∋⟨ i ⟩ [∙⊢₁ get x 𝒾 ⦂ A valid[ Ψ ] ]
zap∋₁ {x = x , M} {Ξ , A valid[ Ψ ]} zero    = zero
zap∋₁ {x = x , N} {Ξ , B valid[ Y ]} (suc 𝒾) = suc (zap∋₁ 𝒾)


infix 3 _⋙₁_
_⋙₁_ : ∀ {d} → {σ : Scopes d} → Validities σ → Derivation₁ σ → Set
Δ ⋙₁ [∙⊢₁ M ⦂ A valid[ Ψ ] ] = Δ ⋙ [ Ψ ⊢ M ⦂ A true ]


infix 3 _⋙⋆₁_
_⋙⋆₁_ : ∀ {d} → {σ : Scopes d} → Validities σ → Derivations₁ σ → Set
Δ ⋙⋆₁ [∙⊢⋆₁ x ⦂ Ξ ] = All (Δ ⋙₁_) (zap₁ x Ξ)


--------------------------------------------------------------------------------


mrens₁ : ∀ {d d′ e n} → {σ : Scopes d} {σ′ : Scopes d′} {ξ : Scopes n} {η : σ′ ⊇⟨ e ⟩ σ}
                         {Δ : Validities σ} {Δ′ : Validities σ′}
                         {x : Terms₁ σ ξ} {Ξ : Validities ξ}
                      → Δ′ ⊇◇⟨ η ⟩ Δ → Δ ⋙⋆₁ [∙⊢⋆₁ x ⦂ Ξ ]
                      → Δ′ ⋙⋆₁ [∙⊢⋆₁ MRENS₁ η x ⦂ Ξ ]
mrens₁ {x = ∙}     {∙}                `η ∙       = ∙
mrens₁ {x = x , M} {Ξ , A valid[ Ψ ]} `η (ξ , 𝒟) = mrens₁ `η ξ , mren `η 𝒟
-- NOTE: Equivalent to
-- mrens₁ `η ξ = maps (mren `η) ξ


mwks₁ : ∀ {m d n A} → {Ψ : Truths m} {σ : Scopes d} {ξ : Scopes n}
                       {Δ : Validities σ}
                       {x : Terms₁ σ ξ} {Ξ : Validities ξ}
                    → Δ ⋙⋆₁ [∙⊢⋆₁ x ⦂ Ξ ]
                    → Δ , A valid[ Ψ ] ⋙⋆₁ [∙⊢⋆₁ MWKS₁ x ⦂ Ξ ]
mwks₁ ξ = mrens₁ (drop id⊇◇) ξ


mlifts₁ : ∀ {m d n A} → {Ψ : Truths m} {σ : Scopes d} {ξ : Scopes n}
                         {Δ : Validities σ}
                         {x : Terms₁ σ ξ} {Ξ : Validities ξ}
                      → Δ ⋙⋆₁ [∙⊢⋆₁ x ⦂ Ξ ]
                      → Δ , A valid[ Ψ ] ⋙⋆₁ [∙⊢⋆₁ MLIFTS₁ x ⦂ Ξ , A valid[ Ψ ] ]
mlifts₁ ξ = mwks₁ ξ , mvz ids


mids₁ : ∀ {d} → {σ : Scopes d}
                 {Δ : Validities σ}
              → Δ ⋙⋆₁ [∙⊢⋆₁ MIDS₁ ⦂ Δ ]
mids₁ {Δ = ∙}                = ∙
mids₁ {Δ = Δ , A valid[ Ψ ]} = mlifts₁ mids₁


--------------------------------------------------------------------------------


mutual
  msub : ∀ {d g n A} → {σ : Scopes d} {ξ : Scopes n}
                        {Δ : Validities σ} {Γ : Truths g}
                        {x : Terms₁ σ ξ} {Ξ : Validities ξ} {M : Term ξ g}
                     → Δ ⋙⋆₁ [∙⊢⋆₁ x ⦂ Ξ ] → Ξ ⋙ [ Γ ⊢ M ⦂ A true ]
                     → Δ ⋙ [ Γ ⊢ MSUB x M ⦂ A true ]
  msub ξ (var 𝒾)      = var 𝒾
  msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
  msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
  msub ξ (mvar `𝒾 ψ)  = sub (msubs ξ ψ) (get ξ (zap∋₁ `𝒾))
  msub ξ (box 𝒟)      = box (msub ξ 𝒟)
  msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts₁ ξ) ℰ)

  msubs : ∀ {d g n m} → {σ : Scopes d} {ξ : Scopes n}
                         {Δ : Validities σ} {Γ : Truths g}
                         {x : Terms₁ σ ξ} {Ξ : Validities ξ} {y : Terms ξ g m} {Ψ : Truths m}
                      → Δ ⋙⋆₁ [∙⊢⋆₁ x ⦂ Ξ ] → Ξ ⋙⋆ [ Γ ⊢⋆ y ⦂ Ψ ]
                      → Δ ⋙⋆ [ Γ ⊢⋆ MSUBS x y ⦂ Ψ ]
  msubs {y = ∙}     {∙}          ξ ∙       = ∙
  msubs {y = y , M} {Ψ , A true} ξ (ψ , 𝒟) = msubs ξ ψ , msub ξ 𝒟
  -- NOTE: Equivalent to
  -- msubs ξ ψ = maps (msub ξ) ψ


mcut : ∀ {d g m A B} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g} {Ψ : Truths m}
                        {M : Term σ m} {N : Term (σ , m) g}
                     → Δ ⋙₁ [∙⊢₁ M ⦂ A valid[ Ψ ] ] → Δ , A valid[ Ψ ] ⋙ [ Γ ⊢ N ⦂ B true ]
                     → Δ ⋙ [ Γ ⊢ MCUT M N ⦂ B true ]
mcut 𝒟 ℰ = msub (mids₁ , 𝒟) ℰ


--------------------------------------------------------------------------------


unlam : ∀ {d g A B} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                       {M : Term σ g}
                    → Δ ⋙ [ Γ ⊢ M ⦂ A ⊃ B true ]
                    → Δ ⋙ [ Γ , A true ⊢ UNLAM M ⦂ B true ]
unlam 𝒟 = app (wk 𝒟) vz


ex : ∀ {d g A B C} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                      {M : Term σ (suc (suc g))}
                   → Δ ⋙ [ Γ , A true , B true ⊢ M ⦂ C true ]
                   → Δ ⋙ [ Γ , B true , A true ⊢ EX M ⦂ C true ]
ex 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------


up : ∀ {d g m A B} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g} {Ψ : Truths m}
                       {M : Term σ (suc g)}
                   → Δ ⋙ [ Γ , [ Ψ ] A true ⊢ M ⦂ B true ]
                   → Δ , A valid[ Ψ ] ⋙ [ Γ ⊢ UP M ⦂ B true ]
up 𝒟 = app (lam (mwk 𝒟)) (box (mvz ids))


down : ∀ {d g m A B} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g} {Ψ : Truths m}
                        {M : Term (σ , m) g}
                     → Δ , A valid[ Ψ ] ⋙ [ Γ ⊢ M ⦂ B true ]
                     → Δ ⋙ [ Γ , [ Ψ ] A true ⊢ DOWN M ⦂ B true ]
down 𝒟 = letbox vz (wk 𝒟)


mex : ∀ {d g m o A B C} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g} {Ψ : Truths m} {Φ : Truths o}
                           {M : Term (σ , m , o) g}
                        → Δ , A valid[ Ψ ] , B valid[ Φ ] ⋙ [ Γ ⊢ M ⦂ C true ]
                        → Δ , B valid[ Φ ] , A valid[ Ψ ] ⋙ [ Γ ⊢ MEX M ⦂ C true ]
mex 𝒟 = up (up (ex (down (down 𝒟))))


--------------------------------------------------------------------------------
