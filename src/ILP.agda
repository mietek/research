module A201706.ILP where

open import A201706.PreludeVec public


-- Terms.

data Tm (d g : Nat) : Set where
  VAR   : Fin g → Tm d g
  MVAR  : Fin d → Tm d g
  LAM   : Tm d (suc g) → Tm d g
  APP   : Tm d g → Tm d g → Tm d g
  BOX   : Tm d zero → Tm d g
  UNBOX : Tm d g → Tm (suc d) g → Tm d g

Tm⋆ : Nat → Nat → Nat → Set
Tm⋆ d g n = Vec (Tm d g) n

monoTm : ∀ {d g d′ g′} → d′ ≥ d → g′ ≥ g → Tm d g → Tm d′ g′
monoTm z e (VAR i)     = VAR (monoFin e i)
monoTm z e (MVAR i)    = MVAR (monoFin z i)
monoTm z e (LAM M)     = LAM (monoTm z (lift e) M)
monoTm z e (APP M N)   = APP (monoTm z e M) (monoTm z e N)
monoTm z e (BOX M)     = BOX (monoTm z done M)
monoTm z e (UNBOX M N) = UNBOX (monoTm z e M) (monoTm (lift z) e N)

monoTm⋆ : ∀ {d g d′ g′ n} → d′ ≥ d → g′ ≥ g → Tm⋆ d g n → Tm⋆ d′ g′ n
monoTm⋆ z e x = map (monoTm z e) x

idmonoTm : ∀ {d g} → (M : Tm d g) → monoTm refl≥ refl≥ M ≡ M
idmonoTm (VAR i)     = cong VAR (idmonoFin i)
idmonoTm (MVAR i)    = cong MVAR (idmonoFin i)
idmonoTm (LAM M)     = cong LAM (idmonoTm M)
idmonoTm (APP M N)   = cong² APP (idmonoTm M) (idmonoTm N)
idmonoTm (BOX M)     = cong BOX (idmonoTm M)
idmonoTm (UNBOX M N) = cong² UNBOX (idmonoTm M) (idmonoTm N)

reflTm⋆ : ∀ {d g} → Tm⋆ d g g
reflTm⋆ {g = zero}  = ∅
reflTm⋆ {g = suc g} = monoTm⋆ refl≥ (weak refl≥) reflTm⋆ , VAR zero

mreflTm⋆ : ∀ {d g} → Tm⋆ d g d
mreflTm⋆ {zero}  = ∅
mreflTm⋆ {suc d} = monoTm⋆ (weak refl≥) refl≥ mreflTm⋆ , MVAR zero

lookupTm : ∀ {d g n} → Tm⋆ d g n → Fin n → Tm d g
lookupTm x i = lookup x i

graftTm : ∀ {d g `g} → Tm⋆ d g `g → Tm d `g → Tm d g
graftTm p (VAR i)     = lookupTm p i
graftTm p (MVAR i)    = MVAR i
graftTm p (LAM M)     = LAM (graftTm (monoTm⋆ refl≥ (weak refl≥) p , VAR zero) M)
graftTm p (APP M N)   = APP (graftTm p M) (graftTm p N)
graftTm p (BOX M)     = BOX (graftTm ∅ M)
graftTm p (UNBOX M N) = UNBOX (graftTm p M) (graftTm (monoTm⋆ (weak refl≥) refl≥ p) N)

graftTm⋆ : ∀ {d g `g n} → Tm⋆ d g `g → Tm⋆ d `g n → Tm⋆ d g n
graftTm⋆ p x = map (graftTm p) x

transTm : ∀ {d g g′ g″} → Tm⋆ d g″ g′ → Tm⋆ d g′ g → Tm⋆ d g″ g
transTm = graftTm⋆

mgraftTm : ∀ {d g `d} → Tm⋆ d zero `d → Tm `d g → Tm d g
mgraftTm q (VAR i)     = VAR i
mgraftTm q (MVAR i)    = UNBOX (monoTm refl≥ inf≥ (lookupTm q i)) (MVAR zero)
mgraftTm q (LAM M)     = LAM (mgraftTm q M)
mgraftTm q (APP M N)   = APP (mgraftTm q M) (mgraftTm q N)
mgraftTm q (BOX M)     = BOX (mgraftTm q M)
mgraftTm q (UNBOX M N) = UNBOX (mgraftTm q M) (mgraftTm (monoTm⋆ (weak refl≥) refl≥ q , BOX (MVAR zero)) N)


-- Types and vectors of types.

mutual
  infixr 7 _⇒_
  data Ty : Set where
    •    : Ty
    _⇒_ : Ty → Ty → Ty
    [_]_ : ∀ {d} → Tm d zero → Ty → Ty

  record BoxTy : Set where
    inductive
    constructor [_]_
    field
      {d} : Nat
      M   : Tm d zero
      A   : Ty

  Ty⋆ : Nat → Set
  Ty⋆ g = Vec Ty g

  BoxTy⋆ : Nat → Set
  BoxTy⋆ d = Vec BoxTy d
