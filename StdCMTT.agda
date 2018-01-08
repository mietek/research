module StdCMTT where

open import Prelude
open import Fin
open import Vec
open import OrnamentedVec
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
record Validity (p : Nat) : Set
  where
    constructor _valid[_]
    field
      A : Prop
      Ψ : Truths p


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


zap : ∀ {d g x} → {σ : Scopes d}
                → Truths g → Terms σ g x → Truths x
                → Vec (Derivation σ) x
zap Γ ∙       ∙            = ∙
zap Γ (ζ , M) (Ξ , A true) = zap Γ ζ Ξ , [ Γ ⊢ M ⦂ A true ]


zap∋ : ∀ {d g x i A} → {σ : Scopes d} {Γ : Truths g}
                        {ζ : Terms σ g x} {Ξ : Truths x}
                     → Ξ ∋⟨ i ⟩ A true
                     → zap Γ ζ Ξ ∋⟨ i ⟩ [ Γ ⊢ get ζ i ⦂ A true ]
zap∋ {ζ = ζ , M} {Ξ , A true} zero    = zero
zap∋ {ζ = ζ , N} {Ξ , B true} (suc 𝒾) = suc (zap∋ 𝒾)


record Derivations {d} (σ : Scopes d) : Set
  where
    constructor [_⊢⋆_⦂_]
    field
      {g} : Nat
      {x} : Nat
      Γ   : Truths g
      ζ   : Terms σ g x
      Ξ   : Truths x


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

      mvar : ∀ {A p d g i} → {Ψ : Truths p} {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                              {𝒾 : σ ∋⟨ i ⟩ p} {ζ : Terms σ g p}
                           → Δ ∋◇⟨ 𝒾 ⟩ A valid[ Ψ ] → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ψ ]
                           → Δ ⋙ [ Γ ⊢ MVAR 𝒾 ζ ⦂ A true ]

      box : ∀ {A p d g} → {Ψ : Truths p} {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                           {M : Term σ p}
                        → Δ ⋙ [ Ψ ⊢ M ⦂ A true ]
                        → Δ ⋙ [ Γ ⊢ BOX M ⦂ [ Ψ ] A true ]

      letbox : ∀ {A B p d g} → {Ψ : Truths p} {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                                {M : Term σ g} {N : Term (σ , p) g}
                             → Δ ⋙ [ Γ ⊢ M ⦂ [ Ψ ] A true ] → Δ , A valid[ Ψ ] ⋙ [ Γ ⊢ N ⦂ B true ]
                             → Δ ⋙ [ Γ ⊢ LETBOX M N ⦂ B true ]

  infix 3 _⋙⋆_
  _⋙⋆_ : ∀ {d} → {σ : Scopes d} → Validities σ → Derivations σ → Set
  Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ] = All (Δ ⋙_) (zap Γ ζ Ξ)


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

  rens : ∀ {d g g′ e x} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g} {Γ′ : Truths g′}
                           {ζ : Terms σ g x} {Ξ : Truths x}
                        → Γ′ ⊇⟨ e ⟩ Γ → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
                        → Δ ⋙⋆ [ Γ′ ⊢⋆ RENS e ζ ⦂ Ξ ]
  rens {ζ = ∙}     {∙}          η ∙       = ∙
  rens {ζ = ζ , M} {Ξ , A true} η (ξ , 𝒟) = rens η ξ , ren η 𝒟
  -- NOTE: Equivalent to
  -- rens η ξ = mapAll (ren η) ξ


wk : ∀ {B d g A} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                    {M : Term σ g}
                 → Δ ⋙ [ Γ ⊢ M ⦂ A true ]
                 → Δ ⋙ [ Γ , B true ⊢ WK M ⦂ A true ]
wk 𝒟 = ren (drop id⊇) 𝒟


vz : ∀ {d g A} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
               → Δ ⋙ [ Γ , A true ⊢ VZ ⦂ A true ]
vz = var zero


wks : ∀ {d g x A} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                     {ζ : Terms σ g x} {Ξ : Truths x}
                  → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
                  → Δ ⋙⋆ [ Γ , A true ⊢⋆ WKS ζ ⦂ Ξ ]
wks ξ = rens (drop id⊇) ξ


lifts : ∀ {d g x A} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                       {ζ : Terms σ g x} {Ξ : Truths x}
                    → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
                    → Δ ⋙⋆ [ Γ , A true ⊢⋆ LIFTS ζ ⦂ Ξ , A true ]
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

  mrens : ∀ {d d′ g e x} → {σ : Scopes d} {σ′ : Scopes d′} {η : σ′ ⊇⟨ e ⟩ σ}
                            {Δ : Validities σ} {Δ′ : Validities σ′} {Γ : Truths g}
                            {ζ : Terms σ g x} {Ξ : Truths x}
                         → Δ′ ⊇◇⟨ η ⟩ Δ → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
                         → Δ′ ⋙⋆ [ Γ ⊢⋆ MRENS η ζ ⦂ Ξ ]
  mrens {ζ = ∙}     {∙}          `η ∙       = ∙
  mrens {ζ = ζ , M} {Ξ , A true} `η (ξ , 𝒟) = mrens `η ξ , mren `η 𝒟
  -- NOTE: Equivalent to
  -- mrens `η ξ = mapAll (mren `η) ξ


mwk : ∀ {B p d g A} → {Ψ : Truths p} {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                       {M : Term σ g}
                    → Δ ⋙ [ Γ ⊢ M ⦂ A true ]
                    → Δ , B valid[ Ψ ] ⋙ [ Γ ⊢ MWK M ⦂ A true ]
mwk 𝒟 = mren (drop id⊇◇) 𝒟


mwks : ∀ {p d g x A} → {Ψ : Truths p} {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                        {ζ : Terms σ g x} {Ξ : Truths x}
                     → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ]
                     → Δ , A valid[ Ψ ] ⋙⋆ [ Γ ⊢⋆ MWKS ζ ⦂ Ξ ]
mwks ξ = mrens (drop id⊇◇) ξ


mvz : ∀ {p d g A} → {Ψ : Truths p} {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                     {φ : Terms σ g p}
                  → Δ ⋙⋆ [ Γ ⊢⋆ φ ⦂ Ψ ]
                  → Δ , A valid[ Ψ ] ⋙ [ Γ ⊢ MVZ φ ⦂ A true ]
mvz ψ = mvar zero (mwks ψ)


--------------------------------------------------------------------------------


mutual
  sub : ∀ {d g x A} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                       {ζ : Terms σ g x} {Ξ : Truths x} {M : Term σ x}
                    → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ] → Δ ⋙ [ Ξ ⊢ M ⦂ A true ]
                    → Δ ⋙ [ Γ ⊢ SUB ζ M ⦂ A true ]
  sub ξ (var 𝒾)      = lookup ξ (zap∋ 𝒾)
  sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
  sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
  sub ξ (mvar `𝒾 ψ)  = mvar `𝒾 (subs ξ ψ)
  sub ξ (box 𝒟)      = box 𝒟
  sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)

  subs : ∀ {d g x p} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g}
                        {ζ : Terms σ g x} {Ξ : Truths x} {φ : Terms σ x p} {Ψ : Truths p}
                     → Δ ⋙⋆ [ Γ ⊢⋆ ζ ⦂ Ξ ] → Δ ⋙⋆ [ Ξ ⊢⋆ φ ⦂ Ψ ]
                     → Δ ⋙⋆ [ Γ ⊢⋆ SUBS ζ φ ⦂ Ψ ]
  subs {φ = ∙}     {∙}          ξ ∙       = ∙
  subs {φ = φ , M} {Ψ , A true} ξ (ψ , 𝒟) = subs ξ ψ , sub ξ 𝒟
  -- NOTE: Equivalent to
  -- subs ξ ψ = mapAll (sub ξ) ψ


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
      {p} : Nat
      M   : Term₁ σ p
      Aᵥ  : Validity p


record Derivations₁ {d} (σ : Scopes d) : Set
  where
    constructor [∙⊢⋆₁_⦂_]
    field
      {x} : Nat
      {ξ} : Scopes x
      ζ   : Terms₁ σ ξ
      Ξ   : Validities ξ


zap₁ : ∀ {d x} → {σ : Scopes d} {ξ : Scopes x}
               → Terms₁ σ ξ → Validities ξ
               → Vec (Derivation₁ σ) x
zap₁ ∙       ∙                  = ∙
zap₁ (ζ , M) (Ξ , A valid[ Ψ ]) = zap₁ ζ Ξ , [∙⊢₁ M ⦂ A valid[ Ψ ] ]

zap∋₁ : ∀ {p d x i A} → {Ψ : Truths p} {σ : Scopes d} {ξ : Scopes x}
                         {ζ : Terms₁ σ ξ} {Ξ : Validities ξ} {𝒾 : ξ ∋⟨ i ⟩ p}
                      → Ξ ∋◇⟨ 𝒾 ⟩ A valid[ Ψ ]
                      → zap₁ ζ Ξ ∋⟨ i ⟩ [∙⊢₁ lookup ζ 𝒾 ⦂ A valid[ Ψ ] ]
zap∋₁ {ζ = ζ , M} {Ξ , A valid[ Ψ ]} zero    = zero
zap∋₁ {ζ = ζ , N} {Ξ , B valid[ Φ ]} (suc 𝒾) = suc (zap∋₁ 𝒾)


infix 3 _⋙₁_
_⋙₁_ : ∀ {d} → {σ : Scopes d} → Validities σ → Derivation₁ σ → Set
Δ ⋙₁ [∙⊢₁ M ⦂ A valid[ Ψ ] ] = Δ ⋙ [ Ψ ⊢ M ⦂ A true ]


infix 3 _⋙⋆₁_
_⋙⋆₁_ : ∀ {d} → {σ : Scopes d} → Validities σ → Derivations₁ σ → Set
Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ] = All (Δ ⋙₁_) (zap₁ ζ Ξ)


--------------------------------------------------------------------------------


mrens₁ : ∀ {d d′ e x} → {σ : Scopes d} {σ′ : Scopes d′} {ξ : Scopes x} {η : σ′ ⊇⟨ e ⟩ σ}
                         {Δ : Validities σ} {Δ′ : Validities σ′}
                         {ζ : Terms₁ σ ξ} {Ξ : Validities ξ}
                      → Δ′ ⊇◇⟨ η ⟩ Δ → Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ]
                      → Δ′ ⋙⋆₁ [∙⊢⋆₁ MRENS₁ η ζ ⦂ Ξ ]
mrens₁ {ζ = ∙}     {∙}                `η ∙       = ∙
mrens₁ {ζ = ζ , M} {Ξ , A valid[ Ψ ]} `η (ξ , 𝒟) = mrens₁ `η ξ , mren `η 𝒟
-- NOTE: Equivalent to
-- mrens₁ `η ξ = mapAll (mren `η) ξ


mwks₁ : ∀ {p d x A} → {Ψ : Truths p} {σ : Scopes d} {ξ : Scopes x}
                       {Δ : Validities σ}
                       {ζ : Terms₁ σ ξ} {Ξ : Validities ξ}
                    → Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ]
                    → Δ , A valid[ Ψ ] ⋙⋆₁ [∙⊢⋆₁ MWKS₁ ζ ⦂ Ξ ]
mwks₁ ξ = mrens₁ (drop id⊇◇) ξ


mlifts₁ : ∀ {p d x A} → {Ψ : Truths p} {σ : Scopes d} {ξ : Scopes x}
                         {Δ : Validities σ}
                         {ζ : Terms₁ σ ξ} {Ξ : Validities ξ}
                      → Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ]
                      → Δ , A valid[ Ψ ] ⋙⋆₁ [∙⊢⋆₁ MLIFTS₁ ζ ⦂ Ξ , A valid[ Ψ ] ]
mlifts₁ ξ = mwks₁ ξ , mvz ids


mids₁ : ∀ {d} → {σ : Scopes d}
                 {Δ : Validities σ}
              → Δ ⋙⋆₁ [∙⊢⋆₁ MIDS₁ ⦂ Δ ]
mids₁ {Δ = ∙}                = ∙
mids₁ {Δ = Δ , A valid[ Ψ ]} = mlifts₁ mids₁


--------------------------------------------------------------------------------


mutual
  msub : ∀ {d g x A} → {σ : Scopes d} {ξ : Scopes x}
                        {Δ : Validities σ} {Γ : Truths g}
                        {ζ : Terms₁ σ ξ} {Ξ : Validities ξ} {M : Term ξ g}
                     → Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ] → Ξ ⋙ [ Γ ⊢ M ⦂ A true ]
                     → Δ ⋙ [ Γ ⊢ MSUB ζ M ⦂ A true ]
  msub ξ (var 𝒾)      = var 𝒾
  msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
  msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
  msub ξ (mvar `𝒾 ψ)  = sub (msubs ξ ψ) (lookup ξ (zap∋₁ `𝒾))
  msub ξ (box 𝒟)      = box (msub ξ 𝒟)
  msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts₁ ξ) ℰ)

  msubs : ∀ {d g x p} → {σ : Scopes d} {ξ : Scopes x}
                         {Δ : Validities σ} {Γ : Truths g}
                         {ζ : Terms₁ σ ξ} {Ξ : Validities ξ} {φ : Terms ξ g p} {Ψ : Truths p}
                      → Δ ⋙⋆₁ [∙⊢⋆₁ ζ ⦂ Ξ ] → Ξ ⋙⋆ [ Γ ⊢⋆ φ ⦂ Ψ ]
                      → Δ ⋙⋆ [ Γ ⊢⋆ MSUBS ζ φ ⦂ Ψ ]
  msubs {φ = ∙}     {∙}          ξ ∙       = ∙
  msubs {φ = φ , M} {Ψ , A true} ξ (ψ , 𝒟) = msubs ξ ψ , msub ξ 𝒟
  -- NOTE: Equivalent to
  -- msubs ξ ψ = mapAll (msub ξ) ψ


mcut : ∀ {d g p A B} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g} {Ψ : Truths p}
                        {M : Term σ p} {N : Term (σ , p) g}
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


shl : ∀ {d g p A B} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g} {Ψ : Truths p}
                       {M : Term σ (suc g)}
                    → Δ ⋙ [ Γ , [ Ψ ] A true ⊢ M ⦂ B true ]
                    → Δ , A valid[ Ψ ] ⋙ [ Γ ⊢ SHL M ⦂ B true ]
shl 𝒟 = app (lam (mwk 𝒟)) (box (mvz ids))


shr : ∀ {d g p A B} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g} {Ψ : Truths p}
                       {M : Term (σ , p) g}
                    → Δ , A valid[ Ψ ] ⋙ [ Γ ⊢ M ⦂ B true ]
                    → Δ ⋙ [ Γ , [ Ψ ] A true ⊢ SHR M ⦂ B true ]
shr 𝒟 = letbox vz (wk 𝒟)


mex : ∀ {d g p q A B C} → {σ : Scopes d} {Δ : Validities σ} {Γ : Truths g} {Ψ : Truths p} {Φ : Truths q}
                           {M : Term (σ , p , q) g}
                        → Δ , A valid[ Ψ ] , B valid[ Φ ] ⋙ [ Γ ⊢ M ⦂ C true ]
                        → Δ , B valid[ Φ ] , A valid[ Ψ ] ⋙ [ Γ ⊢ MEX M ⦂ C true ]
mex 𝒟 = shl (shl (ex (shr (shr 𝒟))))


--------------------------------------------------------------------------------
