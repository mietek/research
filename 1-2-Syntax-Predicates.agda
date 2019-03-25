---------------------------------------------------------------------------------------------------------------

module 1-2-Syntax-Predicates where

open import 1-1-Syntax-Terms public
open Unary


---------------------------------------------------------------------------------------------------------------
--
-- Non-abstraction predicates

data NA {n} : Pred₀ (Tm n) where
  var : ∀ {s x} → NA (var s x)
  app : ∀ {e₁ e₂} → NA (app e₁ e₂)

na? : Decidable NA
na? (var s x)   = yes var
na? (lam s e)   = no λ ()
na? (app e₁ e₂) = yes app

uniq-na : Unique NA
uniq-na {e = var _ _} var var = refl
uniq-na {e = lam _ _} ()  ()
uniq-na {e = app _ _} app app = refl


---------------------------------------------------------------------------------------------------------------
--
-- Normal form predicates

mutual
  data NF {n} : Pred₀ (Tm n) where
    lam : ∀ {s e} → NF e → NF (lam s e)
    nf  : ∀ {e} → NANF e → NF e

  -- Non-abstraction normal form predicates
  data NANF {n} : Pred₀ (Tm n) where
    var : ∀ {s x} → NANF (var s x)
    app : ∀ {e₁ e₂} → NANF e₁ → NF e₂ → NANF (app e₁ e₂)

mutual
  uniq-nf : Unique NF
  uniq-nf {e = var _ _} (nf p)  (nf p′)  = nf & uniq-nanf p p′
  uniq-nf {e = lam _ _} (lam p) (lam p′) = lam & uniq-nf p p′
  uniq-nf {e = lam _ _} (lam p) (nf ())
  uniq-nf {e = lam _ _} (nf ()) p′
  uniq-nf {e = app _ _} (nf p)  (nf p′)  = nf & uniq-nanf p p′

  uniq-nanf : Unique NANF
  uniq-nanf {e = var _ _} var         var           = refl
  uniq-nanf {e = lam _ _} ()          ()
  uniq-nanf {e = app _ _} (app p₁ p₂) (app p₁′ p₂′) = app & uniq-nanf p₁ p₁′ ⊗ uniq-nf p₂ p₂′

nanf←nf : ∀ {n} {e : Tm n} → NF e → NA e → NANF e
nanf←nf (lam p) ()
nanf←nf (nf p)  p′ = p

na←nanf : ∀ {n} {e : Tm n} → NANF e → NA e
na←nanf var         = var
na←nanf (app p₁ p₂) = app

mutual
  nf? : Decidable NF
  nf? (var s x)         = yes (nf var)
  nf? (lam s e)         with nf? e
  ... | no ¬p           = no λ { (lam p) → p ↯ ¬p
                               ; (nf ()) }
  ... | yes p           = yes (lam p)
  nf? (app e₁ e₂)       with nanf? e₁ | nf? e₂
  ... | no ¬p₁ | _      = no λ { (nf (app p₁ p₂)) → p₁ ↯ ¬p₁ }
  ... | yes p₁ | no ¬p₂ = no λ { (nf (app p₁ p₂)) → p₂ ↯ ¬p₂ }
  ... | yes p₁ | yes p₂ = yes (nf (app p₁ p₂))

  nanf? : Decidable NANF
  nanf? (var s x)       = yes var
  nanf? (lam s e)       = no λ ()
  nanf? (app e₁ e₂)     with nanf? e₁ | nf? e₂
  ... | no ¬p₁ | _      = no λ { (app p₁ p₂) → p₁ ↯ ¬p₁ }
  ... | yes p₁ | no ¬p₂ = no λ { (app p₁ p₂) → p₂ ↯ ¬p₂ }
  ... | yes p₁ | yes p₂ = yes (app p₁ p₂)


---------------------------------------------------------------------------------------------------------------
--
-- Weak normal form predicates

mutual
  data WNF {n} : Pred₀ (Tm n) where
    lam : ∀ {s e} → WNF (lam s e)
    wnf : ∀ {e} → NAWNF e → WNF e

  -- Non-abstraction weak normal form predicates
  data NAWNF {n} : Pred₀ (Tm n) where
    var : ∀ {s x} → NAWNF (var s x)
    app : ∀ {e₁ e₂} → NAWNF e₁ → WNF e₂ → NAWNF (app e₁ e₂)

mutual
  uniq-wnf : Unique WNF
  uniq-wnf {e = var _ _} (wnf p)  (wnf p′) = wnf & uniq-nawnf p p′
  uniq-wnf {e = lam _ _} lam      lam      = refl
  uniq-wnf {e = lam _ _} lam      (wnf ())
  uniq-wnf {e = lam _ _} (wnf ()) p′
  uniq-wnf {e = app _ _} (wnf p)  (wnf p′) = wnf & uniq-nawnf p p′

  uniq-nawnf : Unique NAWNF
  uniq-nawnf {e = var _ _} var         var           = refl
  uniq-nawnf {e = lam _ _} ()          ()
  uniq-nawnf {e = app _ _} (app p₁ p₂) (app p₁′ p₂′) = app & uniq-nawnf p₁ p₁′ ⊗ uniq-wnf p₂ p₂′

nawnf←wnf : ∀ {n} {e : Tm n} → WNF e → NA e → NAWNF e
nawnf←wnf lam     ()
nawnf←wnf (wnf p) p′ = p

na←nawnf : ∀ {n} {e : Tm n} → NAWNF e → NA e
na←nawnf var         = var
na←nawnf (app p₁ p₂) = app

mutual
  wnf←nf : ∀ {n} {e : Tm n} → NF e → WNF e
  wnf←nf (lam p) = lam
  wnf←nf (nf p)  = wnf (nawnf←nanf p)

  nawnf←nanf : ∀ {n} {e : Tm n} → NANF e → NAWNF e
  nawnf←nanf var         = var
  nawnf←nanf (app p₁ p₂) = app (nawnf←nanf p₁) (wnf←nf p₂)

mutual
  wnf? : Decidable WNF
  wnf? (var s x)        = yes (wnf var)
  wnf? (lam s e)        = yes lam
  wnf? (app e₁ e₂)      with nawnf? e₁ | wnf? e₂
  ... | no ¬p₁ | _      = no λ { (wnf (app p₁ p₂)) → p₁ ↯ ¬p₁ }
  ... | yes p₁ | no ¬p₂ = no λ { (wnf (app p₁ p₂)) → p₂ ↯ ¬p₂ }
  ... | yes p₁ | yes p₂ = yes (wnf (app p₁ p₂))

  nawnf? : Decidable NAWNF
  nawnf? (var s x)      = yes var
  nawnf? (lam s e)      = no λ ()
  nawnf? (app e₁ e₂)    with nawnf? e₁ | wnf? e₂
  ... | no ¬p₁ | _      = no λ { (app p₁ p₂) → p₁ ↯ ¬p₁ }
  ... | yes p₁ | no ¬p₂ = no λ { (app p₁ p₂) → p₂ ↯ ¬p₂ }
  ... | yes p₁ | yes p₂ = yes (app p₁ p₂)


---------------------------------------------------------------------------------------------------------------
--
-- Non-abstraction (head or weak head) normal form predicates

data NAXNF {n} : Pred₀ (Tm n) where
  var : ∀ {s x} → NAXNF (var s x)
  app : ∀ {e₁ e₂} → NAXNF e₁ → NAXNF (app e₁ e₂)

uniq-naxnf : Unique NAXNF
uniq-naxnf {e = var _ _} var      var       = refl
uniq-naxnf {e = lam _ _} ()       ()
uniq-naxnf {e = app _ _} (app p₁) (app p₁′) = app & uniq-naxnf p₁ p₁′

na←naxnf : ∀ {n} {e : Tm n} → NAXNF e → NA e
na←naxnf var      = var
na←naxnf (app p₁) = app

naxnf←nanf : ∀ {n} {e : Tm n} → NANF e → NAXNF e
naxnf←nanf var         = var
naxnf←nanf (app p₁ p₂) = app (naxnf←nanf p₁)

naxnf←nf : ∀ {n} {e : Tm n} → NF e → NA e → NAXNF e
naxnf←nf (lam p) ()
naxnf←nf (nf p)  p′  = naxnf←nanf p

naxnf←nawnf : ∀ {n} {e : Tm n} → NAWNF e → NAXNF e
naxnf←nawnf var         = var
naxnf←nawnf (app p₁ p₂) = app (naxnf←nawnf p₁)

naxnf←wnf : ∀ {n} {e : Tm n} → WNF e → NA e → NAXNF e
naxnf←wnf lam     ()
naxnf←wnf (wnf p) p′ = naxnf←nawnf p

naxnf? : Decidable NAXNF
naxnf? (var s x)   = yes var
naxnf? (lam s e)   = no λ ()
naxnf? (app e₁ e₂) with naxnf? e₁
... | no ¬p₁       = no λ { (app p₁) → p₁ ↯ ¬p₁ }
... | yes p₁       = yes (app p₁)


---------------------------------------------------------------------------------------------------------------
--
-- Head normal form predicates

data HNF {n} : Pred₀ (Tm n) where
  lam : ∀ {s e} → HNF e → HNF (lam s e)
  hnf : ∀ {e} → NAXNF e → HNF e

uniq-hnf : Unique HNF
uniq-hnf {e = var _ _} (hnf p)  (hnf p′) = hnf & uniq-naxnf p p′
uniq-hnf {e = lam _ _} (lam p)  (lam p′) = lam & uniq-hnf p p′
uniq-hnf {e = lam _ _} (lam p)  (hnf ())
uniq-hnf {e = lam _ _} (hnf ()) p′
uniq-hnf {e = app _ _} (hnf p)  (hnf p′) = hnf & uniq-naxnf p p′

naxnf←hnf : ∀ {n} {e : Tm n} → HNF e → NA e → NAXNF e
naxnf←hnf (lam p) ()
naxnf←hnf (hnf p) p′ = p

hnf←nf : ∀ {n} {e : Tm n} → NF e → HNF e
hnf←nf (lam p) = lam (hnf←nf p)
hnf←nf (nf p)  = hnf (naxnf←nanf p)

hnf? : Decidable HNF
hnf? (var s x)   = yes (hnf var)
hnf? (lam s e)   with hnf? e
... | no ¬p      = no λ { (lam p) → p ↯ ¬p
                        ; (hnf ()) }
... | yes p      = yes (lam p)
hnf? (app e₁ e₂) with naxnf? e₁
... | no ¬p₁     = no λ { (hnf (app p₁)) → p₁ ↯ ¬p₁ }
... | yes p₁     = yes (hnf (app p₁))


---------------------------------------------------------------------------------------------------------------
--
-- Weak head normal form predicates

data WHNF {n} : Pred₀ (Tm n) where
  lam  : ∀ {s e} → WHNF (lam s e)
  whnf : ∀ {e} → NAXNF e → WHNF e

uniq-whnf : Unique WHNF
uniq-whnf {e = var _ _} (whnf p)  (whnf p′) = whnf & uniq-naxnf p p′
uniq-whnf {e = lam _ _} lam       lam       = refl
uniq-whnf {e = lam _ _} lam       (whnf ())
uniq-whnf {e = lam _ _} (whnf ()) p′
uniq-whnf {e = app _ _} (whnf p)  (whnf p′) = whnf & uniq-naxnf p p′

naxnf←whnf : ∀ {n} {e : Tm n} → WHNF e → NA e → NAXNF e
naxnf←whnf lam      ()
naxnf←whnf (whnf p) p′ = p

whnf←nf : ∀ {n} {e : Tm n} → NF e → WHNF e
whnf←nf (lam p) = lam
whnf←nf (nf p)  = whnf (naxnf←nanf p)

whnf←hnf : ∀ {n} {e : Tm n} → HNF e → WHNF e
whnf←hnf (lam p) = lam
whnf←hnf (hnf p) = whnf p

whnf? : Decidable WHNF
whnf? (var s x)   = yes (whnf var)
whnf? (lam s e)   = yes lam
whnf? (app e₁ e₂) with naxnf? e₁
... | no ¬p₁      = no λ { (whnf (app p₁)) → p₁ ↯ ¬p₁ }
... | yes p₁      = yes (whnf (app p₁))


---------------------------------------------------------------------------------------------------------------
--
-- TODO: Replace all negative constraints in small-step rules with first-order representations?

module _ where
  private
    postulate
      funext : ∀ {a b} → Extensionality a b

  uniq-¬hnf : ∀ {n} {e : Tm n} (¬p ¬p′ : ¬ HNF e) → ¬p ≡ ¬p′
  uniq-¬hnf ¬p ¬p′ = funext λ p → p ↯ ¬p

  uniq-¬whnf : ∀ {n} {e : Tm n} (¬p ¬p′ : ¬ WHNF e) → ¬p ≡ ¬p′
  uniq-¬whnf ¬p ¬p′ = funext λ p → p ↯ ¬p


---------------------------------------------------------------------------------------------------------------
