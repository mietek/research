module StdS4TT where

open import Prelude
open import Fin
open import Vec
open import AllVec
open import StdS4TTTerms


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


infix 7 _valid
record Validity : Set
  where
    constructor _valid
    field
      A : Prop


Truths : Nat → Set
Truths g = Vec Truth g


Validities : Nat → Set
Validities d = Vec Validity d


--------------------------------------------------------------------------------


infix 4 _⊢_⦂_
record Derivation (d : Nat) : Set
  where
    constructor _⊢_⦂_
    field
      {g} : Nat
      Γ   : Truths g
      M   : Term d g
      Aₜ  : Truth


infix 3 _⨾_
data _⨾_ : ∀ {d} → Validities d → Derivation d → Set
  where
    var : ∀ {A d g i} → {Δ : Validities d} {Γ : Truths g}
                      → Γ ∋⟨ i ⟩ A true
                      → Δ ⨾ Γ ⊢ VAR i ⦂ A true

    lam : ∀ {A B d g M} → {Δ : Validities d} {Γ : Truths g}
                        → Δ ⨾ Γ , A true ⊢ M ⦂ B true
                        → Δ ⨾ Γ ⊢ LAM M ⦂ A ⊃ B true

    app : ∀ {A B d g M N} → {Δ : Validities d} {Γ : Truths g}
                          → Δ ⨾ Γ ⊢ M ⦂ A ⊃ B true → Δ ⨾ Γ ⊢ N ⦂ A true
                          → Δ ⨾ Γ ⊢ APP M N ⦂ B true

    mvar : ∀ {A d g i} → {Δ : Validities d} {Γ : Truths g}
                       → Δ ∋⟨ i ⟩ A valid
                       → Δ ⨾ Γ ⊢ MVAR i ⦂ A true 

    box : ∀ {A d g M} → {Δ : Validities d} {Γ : Truths g}
                      → Δ ⨾ ∙ ⊢ M ⦂ A true
                      → Δ ⨾ Γ ⊢ BOX M ⦂ □ A true

    letbox : ∀ {A B d g M N} → {Δ : Validities d} {Γ : Truths g}
                             → Δ ⨾ Γ ⊢ M ⦂ □ A true → Δ , A valid ⨾ Γ ⊢ N ⦂ B true
                             → Δ ⨾ Γ ⊢ LETBOX M N ⦂ B true


--------------------------------------------------------------------------------


ren : ∀ {d g g′ e M A} → {Δ : Validities d} {Γ : Truths g} {Γ′ : Truths g′}
                       → Γ′ ⊇⟨ e ⟩ Γ → Δ ⨾ Γ ⊢ M ⦂ A true
                       → Δ ⨾ Γ′ ⊢ REN e M ⦂ A true
ren η (var 𝒾)      = var (ren∋ η 𝒾)
ren η (lam 𝒟)      = lam (ren (keep η) 𝒟)
ren η (app 𝒟 ℰ)    = app (ren η 𝒟) (ren η ℰ)
ren η (mvar 𝒾)     = mvar 𝒾
ren η (box 𝒟)      = box 𝒟
ren η (letbox 𝒟 ℰ) = letbox (ren η 𝒟) (ren η ℰ)


wk : ∀ {B d g M A} → {Δ : Validities d} {Γ : Truths g}
                   → Δ ⨾ Γ ⊢ M ⦂ A true
                   → Δ ⨾ Γ , B true ⊢ WK M ⦂ A true
wk 𝒟 = ren (drop id⊇) 𝒟


vz : ∀ {d g A} → {Δ : Validities d} {Γ : Truths g}
               → Δ ⨾ Γ , A true ⊢ VZ ⦂ A true 
vz = var zero


--------------------------------------------------------------------------------


mren : ∀ {d d′ g e M A} → {Δ : Validities d} {Δ′ : Validities d′} {Γ : Truths g}
                        → Δ′ ⊇⟨ e ⟩ Δ → Δ ⨾ Γ ⊢ M ⦂ A true
                        → Δ′ ⨾ Γ ⊢ MREN e M ⦂ A true
mren η (var 𝒾)      = var 𝒾
mren η (lam 𝒟)      = lam (mren η 𝒟)
mren η (app 𝒟 ℰ)    = app (mren η 𝒟) (mren η ℰ)
mren η (mvar 𝒾)     = mvar (ren∋ η 𝒾)
mren η (box 𝒟)      = box (mren η 𝒟)
mren η (letbox 𝒟 ℰ) = letbox (mren η 𝒟) (mren (keep η) ℰ)


mwk : ∀ {B d g M A} → {Δ : Validities d} {Γ : Truths g}
                    → Δ ⨾ Γ ⊢ M ⦂ A true
                    → Δ , B valid ⨾ Γ ⊢ MWK M ⦂ A true
mwk 𝒟 = mren (drop id⊇) 𝒟


mvz : ∀ {d g A} → {Δ : Validities d} {Γ : Truths g}
                → Δ , A valid ⨾ Γ ⊢ MVZ ⦂ A true
mvz = mvar zero


--------------------------------------------------------------------------------


record Derivations (d : Nat) : Set
  where
    constructor [_⊢⋆_⦂_]
    field
      {g} : Nat
      {n} : Nat
      Γ   : Truths g
      x   : Terms d g n
      Ξ   : Truths n


pac : ∀ {d g n} → Truths g → Terms d g n → Truths n
                → Vec (Derivation d) n
pac Γ ∙       ∙            = ∙
pac Γ (x , M) (Ξ , A true) = pac Γ x Ξ , (Γ ⊢ M ⦂ A true)


pac∋ : ∀ {d g n i A} → {Γ : Truths g} {x : Terms d g n} {Ξ : Truths n}
                     → Ξ ∋⟨ i ⟩ A true
                     → pac Γ x Ξ ∋⟨ i ⟩ (Γ ⊢ GET x i ⦂ A true)
pac∋ {x = x , M} {Ξ , A true} zero    = zero
pac∋ {x = x , N} {Ξ , B true} (suc 𝒾) = suc (pac∋ 𝒾)


infix 3 _⨾⋆_
_⨾⋆_ : ∀ {d} → Validities d → Derivations d → Set
Δ ⨾⋆ [ Γ ⊢⋆ x ⦂ Ξ ] = All (Δ ⨾_) (pac Γ x Ξ)


--------------------------------------------------------------------------------


rens : ∀ {d g g′ e n} → {Δ : Validities d} {Γ : Truths g} {Γ′ : Truths g′}
                         {x : Terms d g n} {Ξ : Truths n}
                      → Γ′ ⊇⟨ e ⟩ Γ → Δ ⨾⋆ [ Γ ⊢⋆ x ⦂ Ξ ]
                      → Δ ⨾⋆ [ Γ′ ⊢⋆ RENS e x ⦂ Ξ ]
rens {x = ∙}     {∙}          η ∙       = ∙
rens {x = x , M} {Ξ , A true} η (ξ , 𝒟) = rens η ξ , ren η 𝒟
-- NOTE: Equivalent to
-- rens η ξ = maps (ren η) ξ


wks : ∀ {d g n A} → {Δ : Validities d} {Γ : Truths g}
                     {x : Terms d g n} {Ξ : Truths n}
                  → Δ ⨾⋆ [ Γ ⊢⋆ x ⦂ Ξ ]
                  → Δ ⨾⋆ [ Γ , A true ⊢⋆ WKS x ⦂ Ξ ]
wks ξ = rens (drop id⊇) ξ


lifts : ∀ {d g n A} → {Δ : Validities d} {Γ : Truths g}
                       {x : Terms d g n} {Ξ : Truths n}
                    → Δ ⨾⋆ [ Γ ⊢⋆ x ⦂ Ξ ]
                    → Δ ⨾⋆ [ Γ , A true ⊢⋆ LIFTS x ⦂ Ξ , A true ]
lifts ξ = wks ξ , vz


vars : ∀ {d g g′ e} → {Δ : Validities d} {Γ : Truths g} {Γ′ : Truths g′}
                    → Γ′ ⊇⟨ e ⟩ Γ
                    → Δ ⨾⋆ [ Γ′ ⊢⋆ VARS e ⦂ Γ ]
vars done     = ∙
vars (drop η) = wks (vars η)
vars (keep η) = lifts (vars η)


ids : ∀ {d g} → {Δ : Validities d} {Γ : Truths g}
              → Δ ⨾⋆ [ Γ ⊢⋆ IDS ⦂ Γ ]
ids = vars id⊇


--------------------------------------------------------------------------------


mrens : ∀ {d d′ g e n} → {Δ : Validities d} {Δ′ : Validities d′} {Γ : Truths g}
                          {x : Terms d g n} {Ξ : Truths n}
                       → Δ′ ⊇⟨ e ⟩ Δ → Δ ⨾⋆ [ Γ ⊢⋆ x ⦂ Ξ ]
                       → Δ′ ⨾⋆ [ Γ ⊢⋆ MRENS e x ⦂ Ξ ]
mrens {x = ∙}     {∙}          η ∙       = ∙
mrens {x = x , M} {Ξ , A true} η (ξ , 𝒟) = mrens η ξ , mren η 𝒟
-- NOTE: Equivalent to
-- mrens η ξ = maps (mren η) ξ


mwks : ∀ {d g n A} → {Δ : Validities d} {Γ : Truths g}
                      {x : Terms d g n} {Ξ : Truths n}
                   → Δ ⨾⋆ [ Γ ⊢⋆ x ⦂ Ξ ]
                   → Δ , A valid ⨾⋆ [ Γ ⊢⋆ MWKS x ⦂ Ξ ]
mwks ξ = mrens (drop id⊇) ξ


--------------------------------------------------------------------------------


sub : ∀ {d g n M A} → {Δ : Validities d} {Γ : Truths g}
                       {x : Terms d g n} {Ξ : Truths n}
                    → Δ ⨾⋆ [ Γ ⊢⋆ x ⦂ Ξ ] → Δ ⨾ Ξ ⊢ M ⦂ A true
                    → Δ ⨾ Γ ⊢ SUB x M ⦂ A true
sub ξ (var 𝒾)      = get ξ (pac∋ 𝒾)
sub ξ (lam 𝒟)      = lam (sub (lifts ξ) 𝒟)
sub ξ (app 𝒟 ℰ)    = app (sub ξ 𝒟) (sub ξ ℰ)
sub ξ (mvar 𝒾)     = mvar 𝒾
sub ξ (box 𝒟)      = box 𝒟
sub ξ (letbox 𝒟 ℰ) = letbox (sub ξ 𝒟) (sub (mwks ξ) ℰ)


cut : ∀ {d g M N A B} → {Δ : Validities d} {Γ : Truths g}
                      → Δ ⨾ Γ ⊢ M ⦂ A true → Δ ⨾ Γ , A true ⊢ N ⦂ B true
                      → Δ ⨾ Γ ⊢ CUT M N ⦂ B true
cut 𝒟 ℰ = sub (ids , 𝒟) ℰ


--------------------------------------------------------------------------------


infix 4 ∙⊢₁_⦂_
record Derivation₁ (d : Nat) : Set
  where
    constructor ∙⊢₁_⦂_
    field
      M  : Term₁ d
      Aᵥ : Validity


infix 4 ∙⊢⋆₁_⦂_
record Derivations₁ (d : Nat) : Set
  where
    constructor ∙⊢⋆₁_⦂_
    field
      {n} : Nat
      x   : Terms₁ d n
      Ξ   : Validities n


pac₁ : ∀ {d n} → Terms₁ d n → Validities n
               → Vec (Derivation₁ d) n
pac₁ ∙       ∙             = ∙
pac₁ (x , M) (Ξ , A valid) = pac₁ x Ξ , (∙⊢₁ M ⦂ A valid)


pac∋₁ : ∀ {d n i A} → {x : Terms₁ d n} {Ξ : Validities n}
                    → Ξ ∋⟨ i ⟩ A valid
                    → pac₁ x Ξ ∋⟨ i ⟩ (∙⊢₁ GET x i ⦂ A valid)
pac∋₁ {x = x , M} {Ξ , A valid} zero    = zero
pac∋₁ {x = x , N} {Ξ , B valid} (suc 𝒾) = suc (pac∋₁ 𝒾)


infix 3 _⨾₁_
_⨾₁_ : ∀ {d} → Validities d → Derivation₁ d → Set
Δ ⨾₁ ∙⊢₁ M ⦂ A valid = Δ ⨾ ∙ ⊢ M ⦂ A true


infix 3 _⨾⋆₁_
_⨾⋆₁_ : ∀ {d} → Validities d → Derivations₁ d → Set
Δ ⨾⋆₁ ∙⊢⋆₁ x ⦂ Ξ = All (Δ ⨾₁_) (pac₁ x Ξ)


--------------------------------------------------------------------------------


mrens₁ : ∀ {d d′ e n} → {Δ : Validities d} {Δ′ : Validities d′} {x : Terms₁ d n} {Ξ : Validities n}
                      → Δ′ ⊇⟨ e ⟩ Δ → Δ ⨾⋆₁ ∙⊢⋆₁ x ⦂ Ξ
                      → Δ′ ⨾⋆₁ ∙⊢⋆₁ MRENS₁ e x ⦂ Ξ 
mrens₁ {x = ∙}     {∙}           η ∙       = ∙
mrens₁ {x = x , M} {Ξ , A valid} η (ξ , 𝒟) = mrens₁ η ξ , mren η 𝒟
-- NOTE: Equivalent to
-- mrens₁ η ξ = maps (mren η) ξ


mwks₁ : ∀ {d n A} → {Δ : Validities d} {x : Terms₁ d n} {Ξ : Validities n}
                  → Δ ⨾⋆₁ ∙⊢⋆₁ x ⦂ Ξ 
                  → Δ , A valid ⨾⋆₁ ∙⊢⋆₁ MWKS₁ x ⦂ Ξ 
mwks₁ ξ = mrens₁ (drop id⊇) ξ


mlifts₁ : ∀ {d n A} → {Δ : Validities d} {x : Terms₁ d n} {Ξ : Validities n}
                    → Δ ⨾⋆₁ ∙⊢⋆₁ x ⦂ Ξ 
                    → Δ , A valid ⨾⋆₁ ∙⊢⋆₁ MLIFTS₁ x ⦂ Ξ , A valid 
mlifts₁ ξ = mwks₁ ξ , mvz


mvars₁ : ∀ {d d′ e} → {Δ : Validities d} {Δ′ : Validities d′}
                    → Δ′ ⊇⟨ e ⟩ Δ
                    → Δ′ ⨾⋆₁ ∙⊢⋆₁ MVARS₁ e ⦂ Δ 
mvars₁ done     = ∙
mvars₁ (drop η) = mwks₁ (mvars₁ η)
mvars₁ (keep η) = mlifts₁ (mvars₁ η)


mids₁ : ∀ {d} → {Δ : Validities d}
              → Δ ⨾⋆₁ ∙⊢⋆₁ MIDS₁ ⦂ Δ 
mids₁ = mvars₁ id⊇


--------------------------------------------------------------------------------


msub : ∀ {d g n M A} → {Δ : Validities d} {Γ : Truths g}
                        {x : Terms₁ d n} {Ξ : Validities n}
                     → Δ ⨾⋆₁ ∙⊢⋆₁ x ⦂ Ξ → Ξ ⨾ Γ ⊢ M ⦂ A true
                     → Δ ⨾ Γ ⊢ MSUB x M ⦂ A true
msub ξ (var 𝒾)      = var 𝒾
msub ξ (lam 𝒟)      = lam (msub ξ 𝒟)
msub ξ (app 𝒟 ℰ)    = app (msub ξ 𝒟) (msub ξ ℰ)
msub ξ (mvar 𝒾)     = sub ∙ (get ξ (pac∋₁ 𝒾))
msub ξ (box 𝒟)      = box (msub ξ 𝒟)
msub ξ (letbox 𝒟 ℰ) = letbox (msub ξ 𝒟) (msub (mlifts₁ ξ) ℰ)


mcut : ∀ {d g M N A B} → {Δ : Validities d} {Γ : Truths g}
                       → Δ ⨾₁ ∙⊢₁ M ⦂ A valid → Δ , A valid ⨾ Γ ⊢ N ⦂ B true
                       → Δ ⨾ Γ ⊢ MCUT M N ⦂ B true
mcut 𝒟 ℰ = msub (mids₁ , 𝒟) ℰ


--------------------------------------------------------------------------------


unlam : ∀ {d g M A B} → {Δ : Validities d} {Γ : Truths g}
                      → Δ ⨾ Γ ⊢ M ⦂ A ⊃ B true
                      → Δ ⨾ Γ , A true ⊢ UNLAM M ⦂ B true
unlam 𝒟 = app (wk 𝒟) vz


ex : ∀ {d g M A B C} → {Δ : Validities d} {Γ : Truths g}
                     → Δ ⨾ Γ , A true , B true ⊢ M ⦂ C true
                     → Δ ⨾ Γ , B true , A true ⊢ EX M ⦂ C true
ex 𝒟 = app (app (wk (wk (lam (lam 𝒟)))) vz) (wk vz)


--------------------------------------------------------------------------------


up : ∀ {d g M A B} → {Δ : Validities d} {Γ : Truths g}
                   → Δ ⨾ Γ , □ A true ⊢ M ⦂ B true
                   → Δ , A valid ⨾ Γ ⊢ UP M ⦂ B true
up 𝒟 = app (lam (mwk 𝒟)) (box mvz)


down : ∀ {d g M A B} → {Δ : Validities d} {Γ : Truths g}
                     → Δ , A valid ⨾ Γ ⊢ M ⦂ B true
                     → Δ ⨾ Γ , □ A true ⊢ DOWN M ⦂ B true
down 𝒟 = letbox vz (wk 𝒟)


mex : ∀ {d g M A B C} → {Δ : Validities d} {Γ : Truths g}
                      → Δ , A valid , B valid ⨾ Γ ⊢ M ⦂ C true
                      → Δ , B valid , A valid ⨾ Γ ⊢ MEX M ⦂ C true
mex 𝒟 = up (up (ex (down (down 𝒟))))


--------------------------------------------------------------------------------
