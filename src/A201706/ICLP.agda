module A201706.ICLP where

open import A201706.PreludeVec public


-- Terms.

mutual
  data Tm (d g : Nat) : Set where
    VAR   : Fin g → Tm d g
    MVAR  : ∀ {`g} → Tm⋆ d g `g → Fin d → Tm d g
    LAM   : Tm d (suc g) → Tm d g
    APP   : Tm d g → Tm d g → Tm d g
    BOX   : ∀ {`g} → Tm d `g → Tm d g
    UNBOX : Tm d g → Tm (suc d) g → Tm d g

  Tm⋆ : Nat → Nat → Nat → Set
  Tm⋆ d g n = Vec (Tm d g) n

mutual
  monoTm : ∀ {d g d′ g′} → d′ ≥ d → g′ ≥ g → Tm d g → Tm d′ g′
  monoTm z e (VAR i)     = VAR (monoFin e i)
  monoTm z e (MVAR p i)  = MVAR (monoTm⋆ z e p) (monoFin z i)
  monoTm z e (LAM M)     = LAM (monoTm z (lift e) M)
  monoTm z e (APP M N)   = APP (monoTm z e M) (monoTm z e N)
  monoTm z e (BOX M)     = BOX (monoTm z refl≥ M)
  monoTm z e (UNBOX M N) = UNBOX (monoTm z e M) (monoTm (lift z) e N)

  monoTm⋆ : ∀ {d g d′ g′ n} → d′ ≥ d → g′ ≥ g → Tm⋆ d g n → Tm⋆ d′ g′ n
  monoTm⋆ z e ∅       = ∅
  monoTm⋆ z e (x , M) = monoTm⋆ z e x , monoTm z e M
  -- NOTE: Equivalent, but does not pass termination check.
  -- monoTm⋆ z e x = map (monoTm z e) x

mutual
  idmonoTm : ∀ {d g} → (M : Tm d g) → monoTm refl≥ refl≥ M ≡ M
  idmonoTm (VAR i)     = cong VAR (idmonoFin i)
  idmonoTm (MVAR p i)  = cong² MVAR (idmonoTm⋆ p) (idmonoFin i)
  idmonoTm (LAM M)     = cong LAM (idmonoTm M)
  idmonoTm (APP M N)   = cong² APP (idmonoTm M) (idmonoTm N)
  idmonoTm (BOX M)     = cong BOX (idmonoTm M)
  idmonoTm (UNBOX M N) = cong² UNBOX (idmonoTm M) (idmonoTm N)

  idmonoTm⋆ : ∀ {d g n} → (x : Tm⋆ d g n) → monoTm⋆ refl≥ refl≥ x ≡ x
  idmonoTm⋆ ∅       = refl
  idmonoTm⋆ (x , M) = cong² _,_ (idmonoTm⋆ x) (idmonoTm M)

reflTm⋆ : ∀ {d g} → Tm⋆ d g g
reflTm⋆ {g = zero}  = ∅
reflTm⋆ {g = suc g} = monoTm⋆ refl≥ (weak refl≥) reflTm⋆ , VAR zero

mreflTm⋆ : ∀ {d g} → Tm⋆ d g d
mreflTm⋆ {zero}  = ∅
mreflTm⋆ {suc d} = monoTm⋆ (weak refl≥) refl≥ mreflTm⋆ , MVAR reflTm⋆ zero

lookupTm : ∀ {d g n} → Tm⋆ d g n → Fin n → Tm d g
lookupTm x i = lookup x i

mutual
  graftTm : ∀ {d g `g} → Tm⋆ d g `g → Tm d `g → Tm d g
  graftTm p (VAR i)     = lookupTm p i
  graftTm p (MVAR p′ i) = MVAR (graftTm⋆ p p′) i
  graftTm p (LAM M)     = LAM (graftTm (monoTm⋆ refl≥ (weak refl≥) p , VAR zero) M)
  graftTm p (APP M N)   = APP (graftTm p M) (graftTm p N)
  graftTm p (BOX M)     = BOX M
  graftTm p (UNBOX M N) = UNBOX (graftTm p M) (graftTm (monoTm⋆ (weak refl≥) refl≥ p) N)

  graftTm⋆ : ∀ {d g `g n} → Tm⋆ d g `g → Tm⋆ d `g n → Tm⋆ d g n
  graftTm⋆ p ∅       = ∅
  graftTm⋆ p (x , M) = graftTm⋆ p x , graftTm p M
  -- NOTE: Equivalent, but does not pass termination check.
  -- graftTm⋆ p x = map (graftTm p) x

transTm : ∀ {d g g′ g″} → Tm⋆ d g″ g′ → Tm⋆ d g′ g → Tm⋆ d g″ g
transTm = graftTm⋆

mutual
  mgraftTm : ∀ {d g `d} → Tm⋆ d zero `d → Tm `d g → Tm d g
  mgraftTm q (VAR i)     = VAR i
  mgraftTm q (MVAR p i)  = UNBOX (monoTm refl≥ inf≥ (lookupTm q i))
                                 (MVAR (mgraftTm⋆ (monoTm⋆ (weak refl≥) refl≥ q) p) zero)
  mgraftTm q (LAM M)     = LAM (mgraftTm q M)
  mgraftTm q (APP M N)   = APP (mgraftTm q M) (mgraftTm q N)
  mgraftTm q (BOX M)     = BOX (mgraftTm q M)
  mgraftTm {g = g} q (UNBOX M N) =
    UNBOX (mgraftTm q M)
      (mgraftTm (monoTm⋆ (weak refl≥) refl≥ q ,
       BOX {`g = g} (MVAR reflTm⋆ zero)) N)

  mgraftTm⋆ : ∀ {d g `d n} → Tm⋆ d zero `d → Tm⋆ `d g n → Tm⋆ d g n
  mgraftTm⋆ q ∅       = ∅
  mgraftTm⋆ q (x , M) = mgraftTm⋆ q x , mgraftTm q M


-- Types and vectors of types.

mutual
  infixr 7 _⇒_
  data Ty : Set where
    •      : Ty
    _⇒_   : Ty → Ty → Ty
    [_⊦_]_ : ∀ {d g} → Ty⋆ g → Tm d g → Ty → Ty

  record BoxTy : Set where
    inductive
    constructor [_⊦_]_
    field
      {d} : Nat
      {g} : Nat
      Γ   : Ty⋆ g
      M   : Tm d g
      A   : Ty

  Ty⋆ : Nat → Set
  Ty⋆ g = Vec Ty g

  BoxTy⋆ : Nat → Set
  BoxTy⋆ d = Vec BoxTy d
