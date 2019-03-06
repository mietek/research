---------------------------------------------------------------------------------------------------------------

module 1-2-Syntax-Predicates where

open import 1-1-Syntax-Terms public


---------------------------------------------------------------------------------------------------------------
--
-- Non-abstraction predicates

data NA {n} : Pred₀ (Tm n) where
  var : ∀ {x} → NA (var x)
  app : ∀ {e₁ e₂} → NA (app e₁ e₂)

na? : ∀ {n} (e : Tm n) → Dec (NA e)
na? (var x)     = yes var
na? (lam e)     = no λ ()
na? (app e₁ e₂) = yes app

uniq-na : Unique NA
uniq-na {e = var _}   var var = refl
uniq-na {e = lam _}   ()  ()
uniq-na {e = app _ _} app app = refl


---------------------------------------------------------------------------------------------------------------
--
-- Normal form predicates

mutual
  data NF {n} : Pred₀ (Tm n) where
    lam : ∀ {e} → NF e → NF (lam e)
    nf  : ∀ {e} → NANF e → NF e

  -- Non-abstraction normal form predicates
  data NANF {n} : Pred₀ (Tm n) where
    var : ∀ {x} → NANF (var x)
    app : ∀ {e₁ e₂} → NANF e₁ → NF e₂ → NANF (app e₁ e₂)

mutual
  uniq-nf : Unique NF
  uniq-nf {e = var _}   (nf p)  (nf p′)  = nf & uniq-nanf p p′
  uniq-nf {e = lam _}   (lam p) (lam p′) = lam & uniq-nf p p′
  uniq-nf {e = lam _}   (lam p) (nf ())
  uniq-nf {e = lam _}   (nf ()) p′
  uniq-nf {e = app _ _} (nf p)  (nf p′)  = nf & uniq-nanf p p′

  uniq-nanf : Unique NANF
  uniq-nanf {e = var _}   var         var           = refl
  uniq-nanf {e = lam _}   ()          ()
  uniq-nanf {e = app _ _} (app p₁ p₂) (app p₁′ p₂′) = app & uniq-nanf p₁ p₁′ ⊗ uniq-nf p₂ p₂′

nanf←nf : ∀ {n} {e : Tm n} → NF e → NA e → NANF e
nanf←nf (lam p) ()
nanf←nf (nf p)  q  = p

na←nanf : ∀ {n} {e : Tm n} → NANF e → NA e
na←nanf var         = var
na←nanf (app p₁ p₂) = app

mutual
  nf? : ∀ {n} (e : Tm n) → Dec (NF e)
  nf? (var x)     = yes (nf var)
  nf? (lam e)     with nf? e
  ... | no ¬p     = no λ { (lam p) → p ↯ ¬p
                         ; (nf ())
                         }
  ... | yes p     = yes (lam p)
  nf? (app e₁ e₂) with nanf? e₁ | nf? e₂
  ... | no ¬p₁ | _      = no λ { (nf (app p₁ p₂)) → p₁ ↯ ¬p₁ }
  ... | yes p₁ | no ¬p₂ = no λ { (nf (app p₁ p₂)) → p₂ ↯ ¬p₂ }
  ... | yes p₁ | yes p₂ = yes (nf (app p₁ p₂))

  nanf? : ∀ {n} (e : Tm n) → Dec (NANF e)
  nanf? (var x)     = yes var
  nanf? (lam e)     = no λ ()
  nanf? (app e₁ e₂) with nanf? e₁ | nf? e₂
  ... | no ¬p₁ | _      = no λ { (app p₁ p₂) → p₁ ↯ ¬p₁ }
  ... | yes p₁ | no ¬p₂ = no λ { (app p₁ p₂) → p₂ ↯ ¬p₂ }
  ... | yes p₁ | yes p₂ = yes (app p₁ p₂)


---------------------------------------------------------------------------------------------------------------
--
-- Weak normal form predicates

mutual
  data WNF {n} : Pred₀ (Tm n) where
    lam : ∀ {e} → WNF (lam e)
    wnf : ∀ {e} → NAWNF e → WNF e

  -- Non-abstraction weak normal form predicates
  data NAWNF {n} : Pred₀ (Tm n) where
    var : ∀ {x} → NAWNF (var x)
    app : ∀ {e₁ e₂} → NAWNF e₁ → WNF e₂ → NAWNF (app e₁ e₂)

mutual
  uniq-wnf : Unique WNF
  uniq-wnf {e = var _}   (wnf p)  (wnf p′) = wnf & uniq-nawnf p p′
  uniq-wnf {e = lam _}   lam      lam      = refl
  uniq-wnf {e = lam _}   lam      (wnf ())
  uniq-wnf {e = lam _}   (wnf ()) p′
  uniq-wnf {e = app _ _} (wnf p)  (wnf p′) = wnf & uniq-nawnf p p′

  uniq-nawnf : Unique NAWNF
  uniq-nawnf {e = var _}   var         var           = refl
  uniq-nawnf {e = lam _}   ()          ()
  uniq-nawnf {e = app _ _} (app p₁ p₂) (app p₁′ p₂′) = app & uniq-nawnf p₁ p₁′ ⊗ uniq-wnf p₂ p₂′

nawnf←wnf : ∀ {n} {e : Tm n} → WNF e → NA e → NAWNF e
nawnf←wnf lam     ()
nawnf←wnf (wnf p) q  = p

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
  wnf? : ∀ {n} (e : Tm n) → Dec (WNF e)
  wnf? (var x)     = yes (wnf var)
  wnf? (lam e)     = yes lam
  wnf? (app e₁ e₂) with nawnf? e₁ | wnf? e₂
  ... | no ¬p₁ | _      = no λ { (wnf (app p₁ p₂)) → p₁ ↯ ¬p₁ }
  ... | yes p₁ | no ¬p₂ = no λ { (wnf (app p₁ p₂)) → p₂ ↯ ¬p₂ }
  ... | yes p₁ | yes p₂ = yes (wnf (app p₁ p₂))

  nawnf? : ∀ {n} (e : Tm n) → Dec (NAWNF e)
  nawnf? (var x)     = yes var
  nawnf? (lam e)     = no λ ()
  nawnf? (app e₁ e₂) with nawnf? e₁ | wnf? e₂
  ... | no ¬p₁ | _      = no λ { (app p₁ p₂) → p₁ ↯ ¬p₁ }
  ... | yes p₁ | no ¬p₂ = no λ { (app p₁ p₂) → p₂ ↯ ¬p₂ }
  ... | yes p₁ | yes p₂ = yes (app p₁ p₂)


---------------------------------------------------------------------------------------------------------------
--
-- Non-abstraction (head or weak head) normal form predicates

data NAXNF {n} : Pred₀ (Tm n) where
  var : ∀ {x} → NAXNF (var x)
  app : ∀ {e₁ e₂} → NAXNF e₁ → NAXNF (app e₁ e₂)

uniq-naxnf : Unique NAXNF
uniq-naxnf {e = var _}   var      var       = refl
uniq-naxnf {e = lam _}   ()       ()
uniq-naxnf {e = app _ _} (app p₁) (app p₁′) = app & uniq-naxnf p₁ p₁′

na←naxnf : ∀ {n} {e : Tm n} → NAXNF e → NA e
na←naxnf var      = var
na←naxnf (app p₁) = app

naxnf←nanf : ∀ {n} {e : Tm n} → NANF e → NAXNF e
naxnf←nanf var         = var
naxnf←nanf (app p₁ p₂) = app (naxnf←nanf p₁)

naxnf←nf : ∀ {n} {e : Tm n} → NF e → NA e → NAXNF e
naxnf←nf (lam p) ()
naxnf←nf (nf p)  q  = naxnf←nanf p

naxnf←nawnf : ∀ {n} {e : Tm n} → NAWNF e → NAXNF e
naxnf←nawnf var         = var
naxnf←nawnf (app p₁ p₂) = app (naxnf←nawnf p₁)

naxnf←wnf : ∀ {n} {e : Tm n} → WNF e → NA e → NAXNF e
naxnf←wnf lam     ()
naxnf←wnf (wnf p) q  = naxnf←nawnf p

naxnf? : ∀ {n} (e : Tm n) → Dec (NAXNF e)
naxnf? (var x)     = yes var
naxnf? (lam e)     = no λ ()
naxnf? (app e₁ e₂) with naxnf? e₁
... | no ¬p₁       = no λ { (app p₁) → p₁ ↯ ¬p₁ }
... | yes p₁       = yes (app p₁)


---------------------------------------------------------------------------------------------------------------
--
-- Head normal form predicates

data HNF {n} : Pred₀ (Tm n) where
  lam : ∀ {e} → HNF e → HNF (lam e)
  hnf : ∀ {e} → NAXNF e → HNF e

uniq-hnf : Unique HNF
uniq-hnf {e = var _}   (hnf p)  (hnf p′) = hnf & uniq-naxnf p p′
uniq-hnf {e = lam _}   (lam p)  (lam p′) = lam & uniq-hnf p p′
uniq-hnf {e = lam _}   (lam p)  (hnf ())
uniq-hnf {e = lam _}   (hnf ()) p′
uniq-hnf {e = app _ _} (hnf p)  (hnf p′) = hnf & uniq-naxnf p p′

naxnf←hnf : ∀ {n} {e : Tm n} → HNF e → NA e → NAXNF e
naxnf←hnf (lam p) ()
naxnf←hnf (hnf p) q  = p

hnf←nf : ∀ {n} {e : Tm n} → NF e → HNF e
hnf←nf (lam p) = lam (hnf←nf p)
hnf←nf (nf p)  = hnf (naxnf←nanf p)

hnf? : ∀ {n} (e : Tm n) → Dec (HNF e)
hnf? (var x)     = yes (hnf var)
hnf? (lam e)     with hnf? e
... | no ¬p      = no λ { (lam p) → p ↯ ¬p
                        ; (hnf ())
                        }
... | yes p      = yes (lam p)
hnf? (app e₁ e₂) with naxnf? e₁
... | no ¬p₁     = no λ { (hnf (app p₁)) → p₁ ↯ ¬p₁ }
... | yes p₁     = yes (hnf (app p₁))


---------------------------------------------------------------------------------------------------------------
--
-- Weak head normal form predicates

data WHNF {n} : Pred₀ (Tm n) where
  lam  : ∀ {e} → WHNF (lam e)
  whnf : ∀ {e} → NAXNF e → WHNF e

uniq-whnf : Unique WHNF
uniq-whnf {e = var _}   (whnf p)  (whnf p′) = whnf & uniq-naxnf p p′
uniq-whnf {e = lam _}   lam       lam       = refl
uniq-whnf {e = lam _}   lam       (whnf ())
uniq-whnf {e = lam _}   (whnf ()) p′
uniq-whnf {e = app _ _} (whnf p)  (whnf p′) = whnf & uniq-naxnf p p′

-- TODO: Replace all uses of ¬ WHNF with first-order representations?
module _ where
  private
    postulate
      funext : ∀ {a b} → Extensionality a b

  uniq-¬whnf : ∀ {n} {e : Tm n} (¬p ¬p′ : ¬ WHNF e) → ¬p ≡ ¬p′
  uniq-¬whnf ¬p ¬p′ = funext λ p → abort (p ↯ ¬p)

naxnf←whnf : ∀ {n} {e : Tm n} → WHNF e → NA e → NAXNF e
naxnf←whnf lam      ()
naxnf←whnf (whnf p) q  = p

whnf←nf : ∀ {n} {e : Tm n} → NF e → WHNF e
whnf←nf (lam p) = lam
whnf←nf (nf p)  = whnf (naxnf←nanf p)

whnf? : ∀ {n} (e : Tm n) → Dec (WHNF e)
whnf? (var x)     = yes (whnf var)
whnf? (lam e)     = yes lam
whnf? (app e₁ e₂) with naxnf? e₁
... | no ¬p₁      = no λ { (whnf (app p₁)) → p₁ ↯ ¬p₁ }
... | yes p₁      = yes (whnf (app p₁))


---------------------------------------------------------------------------------------------------------------
