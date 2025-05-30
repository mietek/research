{-# OPTIONS --sized-types #-}

module A201607.OlderBasicILP.Direct.Hilbert.Nested where

open import A201607.Common.Context public


-- Propositions of intuitionistic logic of proofs, without ∨, ⊥, or +.

mutual
  infixr 10 _⦂_
  infixl 9 _∧_
  infixr 7 _▻_
  data Ty : Set where
    α_  : Atom → Ty
    _▻_ : Ty → Ty → Ty
    _⦂_ : Box → Ty → Ty
    _∧_ : Ty → Ty → Ty
    ⊤  : Ty

  record Box : Set where
    inductive
    constructor [_]
    field
      {/A} : Ty
      t    : ∅ ⊢ /A


  -- Derivations, as Hilbert-style combinator trees.

  infix 3 _⊢_
  data _⊢_ (Γ : Cx Ty) : Ty → Set where
    var   : ∀ {A}              → A ∈ Γ → Γ ⊢ A
    app   : ∀ {A B}            → Γ ⊢ A ▻ B → Γ ⊢ A → Γ ⊢ B
    ci    : ∀ {A}              → Γ ⊢ A ▻ A
    ck    : ∀ {A B}            → Γ ⊢ A ▻ B ▻ A
    cs    : ∀ {A B C}          → Γ ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
    box   : ∀ {A}              → (t : ∅ ⊢ A) → Γ ⊢ [ t ] ⦂ A
    cdist : ∀ {A B} {t : ∅ ⊢ A ▻ B} {u : ∅ ⊢ A}
                               → Γ ⊢ [ t ] ⦂ (A ▻ B) ▻ [ u ] ⦂ A ▻ [ app t u ] ⦂ B
    cup   : ∀ {A} {t : ∅ ⊢ A} → Γ ⊢ [ t ] ⦂ A ▻ [ box t ] ⦂ [ t ] ⦂ A
    cdown : ∀ {A} {t : ∅ ⊢ A} → Γ ⊢ [ t ] ⦂ A ▻ A
    cpair : ∀ {A B}            → Γ ⊢ A ▻ B ▻ A ∧ B
    cfst  : ∀ {A B}            → Γ ⊢ A ∧ B ▻ A
    csnd  : ∀ {A B}            → Γ ⊢ A ∧ B ▻ B
    unit  : Γ ⊢ ⊤

infix 3 _⊢⋆_
_⊢⋆_ : Cx Ty → Cx Ty → Set
Γ ⊢⋆ ∅     = 𝟙
Γ ⊢⋆ Ξ , A = Γ ⊢⋆ Ξ × Γ ⊢ A

infix 7 _▻◅_
_▻◅_ : Ty → Ty → Ty
A ▻◅ B = (A ▻ B) ∧ (B ▻ A)


-- Additional useful propositions.

_⦂⋆_ : ∀ {n} → VCx Box n → VCx Ty n → Cx Ty
∅        ⦂⋆ ∅       = ∅
(ts , t) ⦂⋆ (Ξ , A) = (ts ⦂⋆ Ξ) , (t ⦂ A)


-- Monotonicity with respect to context inclusion.

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (var i)   = var (mono∈ η i)
mono⊢ η (app t u) = app (mono⊢ η t) (mono⊢ η u)
mono⊢ η ci        = ci
mono⊢ η ck        = ck
mono⊢ η cs        = cs
mono⊢ η (box t)   = box t
mono⊢ η cdist     = cdist
mono⊢ η cup       = cup
mono⊢ η cdown     = cdown
mono⊢ η cpair     = cpair
mono⊢ η cfst      = cfst
mono⊢ η csnd      = csnd
mono⊢ η unit      = unit

mono⊢⋆ : ∀ {Ξ Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⋆ Ξ → Γ′ ⊢⋆ Ξ
mono⊢⋆ {∅}     η ∙        = ∙
mono⊢⋆ {Ξ , A} η (ts , t) = mono⊢⋆ η ts , mono⊢ η t


-- Shorthand for variables.

v₀ : ∀ {A Γ} → Γ , A ⊢ A
v₀ = var i₀

v₁ : ∀ {A B Γ} → (Γ , A) , B ⊢ A
v₁ = var i₁

v₂ : ∀ {A B C Γ} → ((Γ , A) , B) , C ⊢ A
v₂ = var i₂


-- Reflexivity.

refl⊢⋆ : ∀ {Γ} → Γ ⊢⋆ Γ
refl⊢⋆ {∅}     = ∙
refl⊢⋆ {Γ , A} = mono⊢⋆ weak⊆ refl⊢⋆ , v₀


-- Deduction theorem.

lam : ∀ {A B Γ} → Γ , A ⊢ B → Γ ⊢ A ▻ B
lam (var top)     = ci
lam (var (pop i)) = app ck (var i)
lam (app t u)     = app (app cs (lam t)) (lam u)
lam ci            = app ck ci
lam ck            = app ck ck
lam cs            = app ck cs
lam (box t)       = app ck (box t)
lam cdist         = app ck cdist
lam cup           = app ck cup
lam cdown         = app ck cdown
lam cpair         = app ck cpair
lam cfst          = app ck cfst
lam csnd          = app ck csnd
lam unit          = app ck unit


-- Detachment theorem.

det : ∀ {A B Γ} → Γ ⊢ A ▻ B → Γ , A ⊢ B
det t = app (mono⊢ weak⊆ t) v₀


-- Cut and multicut.

cut : ∀ {A B Γ} → Γ ⊢ A → Γ , A ⊢ B → Γ ⊢ B
cut t u = app (lam u) t

multicut : ∀ {Ξ A Γ} → Γ ⊢⋆ Ξ → Ξ ⊢ A → Γ ⊢ A
multicut {∅}     ∙        u = mono⊢ bot⊆ u
multicut {Ξ , B} (ts , t) u = app (multicut ts (lam u)) t


-- Transitivity.

trans⊢⋆ : ∀ {Γ″ Γ′ Γ} → Γ ⊢⋆ Γ′ → Γ′ ⊢⋆ Γ″ → Γ ⊢⋆ Γ″
trans⊢⋆ {∅}      ts ∙        = ∙
trans⊢⋆ {Γ″ , A} ts (us , u) = trans⊢⋆ ts us , multicut ts u


-- Contraction.

ccont : ∀ {A B Γ} → Γ ⊢ (A ▻ A ▻ B) ▻ A ▻ B
ccont = lam (lam (app (app v₁ v₀) v₀))

cont : ∀ {A B Γ} → Γ , A , A ⊢ B → Γ , A ⊢ B
cont t = det (app ccont (lam (lam t)))


-- Exchange, or Schönfinkel’s C combinator.

cexch : ∀ {A B C Γ} → Γ ⊢ (A ▻ B ▻ C) ▻ B ▻ A ▻ C
cexch = lam (lam (lam (app (app v₂ v₀) v₁)))

exch : ∀ {A B C Γ} → Γ , A , B ⊢ C → Γ , B , A ⊢ C
exch t = det (det (app cexch (lam (lam t))))


-- Composition, or Schönfinkel’s B combinator.

ccomp : ∀ {A B C Γ} → Γ ⊢ (B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
ccomp = lam (lam (lam (app v₂ (app v₁ v₀))))

comp : ∀ {A B C Γ} → Γ , B ⊢ C → Γ , A ⊢ B → Γ , A ⊢ C
comp t u = det (app (app ccomp (lam t)) (lam u))


-- Useful theorems in functional form.

dist : ∀ {A B Γ} {t : ∅ ⊢ A ▻ B} {u : ∅ ⊢ A}
       → Γ ⊢ [ t ] ⦂ (A ▻ B) → Γ ⊢ [ u ] ⦂ A
       → Γ ⊢ [ app t u ] ⦂ B
dist t u = app (app cdist t) u

up : ∀ {A Γ} {t : ∅ ⊢ A}
     → Γ ⊢ [ t ] ⦂ A
     → Γ ⊢ [ box t ] ⦂ [ t ] ⦂ A
up t = app cup t

down : ∀ {A Γ} {t : ∅ ⊢ A}
       → Γ ⊢ [ t ] ⦂ A
       → Γ ⊢ A
down t = app cdown t

distup : ∀ {A B Γ} {u : ∅ ⊢ A} {t : ∅ ⊢ [ u ] ⦂ A ▻ B}
         → Γ ⊢ [ t ] ⦂ ([ u ] ⦂ A ▻ B) → Γ ⊢ [ u ] ⦂ A
         → Γ ⊢ [ app t (box u) ] ⦂ B
distup t u = dist t (up u)

unbox : ∀ {A C Γ} {t : ∅ ⊢ A} {u : ∅ ⊢ C}
        → Γ ⊢ [ t ] ⦂ A → Γ , [ t ] ⦂ A ⊢ [ u ] ⦂ C
        → Γ ⊢ [ u ] ⦂ C
unbox t u = app (lam u) t


-- FIXME ↓ FIXME ↓ FIXME -----------------------------------------------------
--
-- ???

distup′ : ∀ {A B Γ} {u : ∅ ⊢ A} {t : ∅ , [ u ] ⦂ A ⊢ B}
          → Γ ⊢ [ lam t ] ⦂ ([ u ] ⦂ A ▻ B) → Γ ⊢ [ u ] ⦂ A
          → Γ ⊢ [ app (lam t) (box u) ] ⦂ B
distup′ t u = dist t (up u)

-- multibox : ∀ {n A Γ} {[ss] : VCx Box n} {Ξ : VCx Ty n}
--            → Γ ⊢⋆ [ss] ⦂⋆ Ξ → (u : [ss] ⦂⋆ Ξ ⊢ A)
--            → Γ ⊢ {!!} ⦂ A
-- multibox {[ss] = ∅}            {∅}     ∙        u = box u
-- multibox {[ss] = [ss] , [ s ]} {Ξ , B} (ts , t) u = {!!}

-- FIXME ↑ FIXME ↑ FIXME -----------------------------------------------------


pair : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
pair t u = app (app cpair t) u

fst : ∀ {A B Γ} → Γ ⊢ A ∧ B → Γ ⊢ A
fst t = app cfst t

snd : ∀ {A B Γ} → Γ ⊢ A ∧ B → Γ ⊢ B
snd t = app csnd t


-- Closure under context concatenation.

concat : ∀ {A B Γ} Γ′ → Γ , A ⊢ B → Γ′ ⊢ A → Γ ⧺ Γ′ ⊢ B
concat Γ′ t u = app (mono⊢ (weak⊆⧺₁ Γ′) (lam t)) (mono⊢ weak⊆⧺₂ u)
