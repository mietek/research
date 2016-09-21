-- Basic intuitionistic logic of proofs, without ∨, ⊥, or +.
-- Gentzen-style formalisation of syntax with context pairs.
-- Simple terms.

module BasicILP.Syntax.DyadicGentzen where

open import BasicILP.Syntax.Common public


-- Types, or propositions.
-- [ Ψ ⁏ Ω ⊢ t ] A means t is a proof of the fact that the type A is inhabited given assumptions in the context Ψ and the modal context Ω.

mutual
  syntax □ Π A t = [ Π ⊢ t ] A


  infixr 10 □
  infixl 9 _∧_
  infixr 7 _▻_
  data Ty : Set where
    α_  : Atom → Ty
    _▻_ : Ty → Ty → Ty
    □   : (Π : Cx² Ty Box) → (A : Ty) → Π ⊢ A → Ty
    _∧_ : Ty → Ty → Ty
    ⊤  : Ty


  -- Context/modal context/type/term quadruples.

  record Box : Set where
    inductive
    constructor □
    field
      Π : Cx² Ty Box
      A : Ty
      x : Π ⊢ A


  -- Derivations.

  -- NOTE: Only var is an instance constructor, which allows the instance argument for mvar to be automatically inferred, in many cases.

  infix 3 _⊢_
  data _⊢_ : Cx² Ty Box → Ty → Set where
    instance
      var : ∀ {A Γ Δ}         → A ∈ Γ → Γ ⁏ Δ ⊢ A
    lam   : ∀ {A B Γ Δ}       → Γ , A ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ A ▻ B
    app   : ∀ {A B Γ Δ}       → Γ ⁏ Δ ⊢ A ▻ B → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B

    mvar  : ∀ {Ψ Ω A x Γ Δ}   → [ Ψ ⁏ Ω ⊢ x ] A ∈ Δ
                              → {{_ : Γ ⁏ Δ ⊢⋆ Ψ}}
                              → {{_ : Γ ⁏ Δ ⊢⍟ Ω}}
                              → Γ ⁏ Δ ⊢ A

    box   : ∀ {Ψ Ω A Γ Δ}     → (x : Ψ ⁏ Ω ⊢ A)
                              → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] A

    unbox : ∀ {Ψ Ω A C x Γ Δ} → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] A
                              → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A ⊢ C
                              → Γ ⁏ Δ ⊢ C

    pair  : ∀ {A B Γ Δ}       → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ A ∧ B
    fst   : ∀ {A B Γ Δ}       → Γ ⁏ Δ ⊢ A ∧ B → Γ ⁏ Δ ⊢ A
    snd   : ∀ {A B Γ Δ}       → Γ ⁏ Δ ⊢ A ∧ B → Γ ⁏ Δ ⊢ B
    unit  : ∀ {Γ Δ}           → Γ ⁏ Δ ⊢ ⊤

  infix 3 _⊢⋆_
  data _⊢⋆_ : Cx² Ty Box → Cx Ty → Set where
    instance
      ∙   : ∀ {Γ Δ}     → Γ ⁏ Δ ⊢⋆ ∅
      _,_ : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢⋆ Ξ , A

  infix 3 _⊢⍟_
  data _⊢⍟_ : Cx² Ty Box → Cx Box → Set where
    instance
      ∙   : ∀ {Γ Δ}           → Γ ⁏ Δ ⊢⍟ ∅
      _,_ : ∀ {Ξ Ψ Ω A x Γ Δ} → Γ ⁏ Δ ⊢⍟ Ξ
                              → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] A
                              → Γ ⁏ Δ ⊢⍟ Ξ , [ Ψ ⁏ Ω ⊢ x ] A


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢ A → Γ′ ⁏ Δ ⊢ A
  mono⊢ η (var i)                = var (mono∈ η i)
  mono⊢ η (lam t)                = lam (mono⊢ (keep η) t)
  mono⊢ η (app t u)              = app (mono⊢ η t) (mono⊢ η u)
  mono⊢ η (mvar i {{ts}} {{us}}) = mvar i {{mono⊢⋆ η ts}} {{mono⊢⍟ η us}}
  mono⊢ η (box t)                = box t
  mono⊢ η (unbox t u)            = unbox (mono⊢ η t) (mono⊢ η u)
  mono⊢ η (pair t u)             = pair (mono⊢ η t) (mono⊢ η u)
  mono⊢ η (fst t)                = fst (mono⊢ η t)
  mono⊢ η (snd t)                = snd (mono⊢ η t)
  mono⊢ η unit                   = unit

  mono⊢⋆ : ∀ {Ξ Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢⋆ Ξ → Γ′ ⁏ Δ ⊢⋆ Ξ
  mono⊢⋆ η ∙        = ∙
  mono⊢⋆ η (ts , t) = mono⊢⋆ η ts , mono⊢ η t

  mono⊢⍟ : ∀ {Ξ Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢⍟ Ξ → Γ′ ⁏ Δ ⊢⍟ Ξ
  mono⊢⍟ η ∙        = ∙
  mono⊢⍟ η (ts , t) = mono⊢⍟ η ts , mono⊢ η t


-- Monotonicity with respect to modal context inclusion.

mutual
  mmono⊢ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ′ ⊢ A
  mmono⊢ θ (var i)                = var i
  mmono⊢ θ (lam t)                = lam (mmono⊢ θ t)
  mmono⊢ θ (app t u)              = app (mmono⊢ θ t) (mmono⊢ θ u)
  mmono⊢ θ (mvar i {{ts}} {{us}}) = mvar (mono∈ θ i) {{mmono⊢⋆ θ ts}} {{mmono⊢⍟ θ us}}
  mmono⊢ θ (box t)                = box t
  mmono⊢ θ (unbox t u)            = unbox (mmono⊢ θ t) (mmono⊢ (keep θ) u)
  mmono⊢ θ (pair t u)             = pair (mmono⊢ θ t) (mmono⊢ θ u)
  mmono⊢ θ (fst t)                = fst (mmono⊢ θ t)
  mmono⊢ θ (snd t)                = snd (mmono⊢ θ t)
  mmono⊢ θ unit                   = unit

  mmono⊢⋆ : ∀ {Ξ Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ′ ⊢⋆ Ξ
  mmono⊢⋆ θ ∙        = ∙
  mmono⊢⋆ θ (ts , t) = mmono⊢⋆ θ ts , mmono⊢ θ t

  mmono⊢⍟ : ∀ {Ξ Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢⍟ Ξ → Γ ⁏ Δ′ ⊢⍟ Ξ
  mmono⊢⍟ θ ∙        = ∙
  mmono⊢⍟ θ (ts , t) = mmono⊢⍟ θ ts , mmono⊢ θ t


-- Monotonicity using context pairs.

mono²⊢ : ∀ {A Π Π′} → Π ⊆² Π′ → Π ⊢ A → Π′ ⊢ A
mono²⊢ (η , θ) = mono⊢ η ∘ mmono⊢ θ


-- Shorthand for variables.

v₀ : ∀ {A Γ Δ} → Γ , A ⁏ Δ ⊢ A
v₀ = var i₀

v₁ : ∀ {A B Γ Δ} → Γ , A , B ⁏ Δ ⊢ A
v₁ = var i₁

v₂ : ∀ {A B C Γ Δ} → Γ , A , B , C ⁏ Δ ⊢ A
v₂ = var i₂

mv₀ : ∀ {Ψ Ω A x Γ Δ}
      → {{_ : Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A ⊢⋆ Ψ}}
      → {{_ : Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A ⊢⍟ Ω}}
      → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A ⊢ A
mv₀ = mvar i₀

mv₁ : ∀ {Ψ Ψ′ Ω Ω′ A B x y Γ Δ}
      → {{_ : Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A , [ Ψ′ ⁏ Ω′ ⊢ y ] B ⊢⋆ Ψ}}
      → {{_ : Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A , [ Ψ′ ⁏ Ω′ ⊢ y ] B ⊢⍟ Ω}}
      → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A , [ Ψ′ ⁏ Ω′ ⊢ y ] B ⊢ A
mv₁ = mvar i₁

mv₂ : ∀ {Ψ Ψ′ Ψ″ Ω Ω′ Ω″ A B C x y z Γ Δ}
      → {{_ : Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A , [ Ψ′ ⁏ Ω′ ⊢ y ] B , [ Ψ″ ⁏ Ω″ ⊢ z ] C ⊢⋆ Ψ}}
      → {{_ : Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A , [ Ψ′ ⁏ Ω′ ⊢ y ] B , [ Ψ″ ⁏ Ω″ ⊢ z ] C ⊢⍟ Ω}}
      → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A , [ Ψ′ ⁏ Ω′ ⊢ y ] B , [ Ψ″ ⁏ Ω″ ⊢ z ] C ⊢ A
mv₂ = mvar i₂


-- Generalised reflexivity.

instance
  refl⊢⋆ : ∀ {Γ Ψ Δ} → {{_ : Ψ ⊆ Γ}} → Γ ⁏ Δ ⊢⋆ Ψ
  refl⊢⋆ {∅}     {{done}}   = ∙
  refl⊢⋆ {Γ , A} {{skip η}} = mono⊢⋆ weak⊆ (refl⊢⋆ {{η}})
  refl⊢⋆ {Γ , A} {{keep η}} = mono⊢⋆ weak⊆ (refl⊢⋆ {{η}}) , v₀

  mrefl⊢⍟ : ∀ {Δ Ω Γ} → {{_ : Ω ⊆ Δ}} → Γ ⁏ Δ ⊢⍟ Ω
  mrefl⊢⍟ {∅}                     {{done}}   = ∙
  mrefl⊢⍟ {Δ , [ Ψ ⁏ Ω ⊢ x ] A } {{skip θ}} = mmono⊢⍟ weak⊆ (mrefl⊢⍟ {{θ}})
  mrefl⊢⍟ {Δ , [ Ψ ⁏ Ω ⊢ x ] A } {{keep θ}} = mmono⊢⍟ weak⊆ (mrefl⊢⍟ {{θ}}) , box x


-- Deduction theorem is built-in.

-- Modal deduction theorem.

mlam : ∀ {Ψ Ω A B x Γ Δ}
      → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A ⊢ B
      → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] A ▻ B
mlam t = lam (unbox v₀ (mono⊢ weak⊆ t))


-- Detachment theorems.

det : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▻ B → Γ , A ⁏ Δ ⊢ B
det t = app (mono⊢ weak⊆ t) v₀

-- FIXME: Is this correct?
mdet : ∀ {Ψ Ω A B x Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] A ▻ B
      → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A ⊢ B
mdet {x = x} t = app (mmono⊢ weak⊆ t) (box x)


-- Cut and multicut.

cut : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A → Γ , A ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ B
cut t u = app (lam u) t

mcut : ∀ {Ψ Ω A B x Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] A
      → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A ⊢ B
      → Γ ⁏ Δ ⊢ B
mcut t u = app (mlam u) t

multicut : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Ξ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A
multicut ∙        u = mono⊢ bot⊆ u
multicut (ts , t) u = app (multicut ts (lam u)) t


-- Contraction.

ccont : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ (A ▻ A ▻ B) ▻ A ▻ B
ccont = lam (lam (app (app v₁ v₀) v₀))

cont : ∀ {A B Γ Δ} → Γ , A , A ⁏ Δ ⊢ B → Γ , A ⁏ Δ ⊢ B
cont t = det (app ccont (lam (lam t)))

mcont : ∀ {Ψ Ω A B x Γ Δ}
      → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A , [ Ψ ⁏ Ω ⊢ x ] A ⊢ B
      → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A ⊢ B
mcont t = mdet (app ccont (mlam (mlam t)))


-- Exchange, or Schönfinkel’s C combinator.

cexch : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ (A ▻ B ▻ C) ▻ B ▻ A ▻ C
cexch = lam (lam (lam (app (app v₂ v₀) v₁)))

exch : ∀ {A B C Γ Δ} → Γ , A , B ⁏ Δ ⊢ C → Γ , B , A ⁏ Δ ⊢ C
exch t = det (det (app cexch (lam (lam t))))

mexch : ∀ {Ψ Ψ′ Ω Ω′ A B C x y Γ Δ}
      → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A , [ Ψ′ ⁏ Ω′ ⊢ y ] B ⊢ C
      → Γ ⁏ Δ , [ Ψ′ ⁏ Ω′ ⊢ y ] B , [ Ψ ⁏ Ω ⊢ x ] A ⊢ C
mexch t = mdet (mdet (app cexch (mlam (mlam t))))


-- Composition, or Schönfinkel’s B combinator.

ccomp : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ (B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
ccomp = lam (lam (lam (app v₂ (app v₁ v₀))))

comp : ∀ {A B C Γ Δ} → Γ , B ⁏ Δ ⊢ C → Γ , A ⁏ Δ ⊢ B → Γ , A ⁏ Δ ⊢ C
comp t u = det (app (app ccomp (lam t)) (lam u))

mcomp : ∀ {Ψ Ψ′ Ψ″ Ω Ω′ Ω″ A B C x y z Γ Δ}
      → Γ ⁏ Δ , [ Ψ′ ⁏ Ω′ ⊢ y ] B ⊢ [ Ψ″ ⁏ Ω″ ⊢ z ] C
      → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A ⊢ [ Ψ′ ⁏ Ω′ ⊢ y ] B
      → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A ⊢ [ Ψ″ ⁏ Ω″ ⊢ z ] C
mcomp t u = mdet (app (app ccomp (mlam t)) (mlam u))


-- Useful theorems in functional form.

dist : ∀ {Ψ Ω A B x y Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] (A ▻ B)
      → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ y ] A
      → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] (A ▻ B) , [ Ψ ⁏ Ω ⊢ y ] A ⊢ app mv₁ mv₀ ] B
dist t u = unbox t (unbox (mmono⊢ weak⊆ u) (box
             (app mv₁ mv₀)))

up : ∀ {Ψ Ω A x Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] A
      → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ box mv₀ ] [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ x ] A ⊢ mv₀ ] A
up t = unbox t (box (box mv₀))

down : ∀ {Ψ Ω A x Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ x ] A
      → {{_ : Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A ⊢⋆ Ψ}}
      → {{_ : Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ x ] A ⊢⍟ Ω}}
      → Γ ⁏ Δ ⊢ A
down t = unbox t mv₀


-- Useful theorems in combinatory form.

ci : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A ▻ A
ci = lam v₀

ck : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▻ B ▻ A
ck = lam (lam v₁)

cs : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
cs = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))

cdist : ∀ {Ψ Ω A B t u Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ t ] (A ▻ B) ▻
                  [ Ψ ⁏ Ω ⊢ u ] A ▻
                  [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ t ] (A ▻ B) , [ Ψ ⁏ Ω ⊢ u ] A ⊢ app mv₁ mv₀ ] B
cdist = lam (lam (dist v₁ v₀))

cup : ∀ {Ψ Ω A t Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ t ] A ▻
                  [ Ψ ⁏ Ω ⊢ box mv₀ ] [ Ψ ⁏ Ω , [ Ψ ⁏ Ω ⊢ t ] A ⊢ mv₀ ] A
cup = lam (up v₀)

cunbox : ∀ {Ψ Ω A C t Γ Δ} → Γ ⁏ Δ ⊢ [ Ψ ⁏ Ω ⊢ t ] A ▻ ([ Ψ ⁏ Ω ⊢ t ] A ▻ C) ▻ C
cunbox = lam (lam (app v₀ v₁))

cpair : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▻ B ▻ A ∧ B
cpair = lam (lam (pair v₁ v₀))

cfst : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ∧ B ▻ A
cfst = lam (fst v₀)

csnd : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ∧ B ▻ B
csnd = lam (snd v₀)


-- Closure under context concatenation.

concat : ∀ {A B Γ} Γ′ {Δ} → Γ , A ⁏ Δ ⊢ B → Γ′ ⁏ Δ ⊢ A → Γ ⧺ Γ′ ⁏ Δ ⊢ B
concat Γ′ t u = app (mono⊢ (weak⊆⧺₁ Γ′) (lam t)) (mono⊢ weak⊆⧺₂ u)

mconcat : ∀ {Ψ Ω A B t Γ Δ} Δ′ → Γ ⁏ Δ , [ Ψ ⁏ Ω ⊢ t ] A ⊢ B → Γ ⁏ Δ′ ⊢ [ Ψ ⁏ Ω ⊢ t ] A → Γ ⁏ Δ ⧺ Δ′ ⊢ B
mconcat Δ′ t u = app (mmono⊢ (weak⊆⧺₁ Δ′) (mlam t)) (mmono⊢ weak⊆⧺₂ u)


-- Substitution.

mutual
  [_≔_]_ : ∀ {A C Γ Δ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ C → Γ ∖ i ⁏ Δ ⊢ C
  [ i ≔ s ] var j                with i ≟∈ j
  [ i ≔ s ] var .i               | same   = s
  [ i ≔ s ] var ._               | diff j = var j
  [ i ≔ s ] lam t                = lam ([ pop i ≔ mono⊢ weak⊆ s ] t)
  [ i ≔ s ] app t u              = app ([ i ≔ s ] t) ([ i ≔ s ] u)
  [ i ≔ s ] mvar j {{ts}} {{us}} = mvar j {{[ i ≔ s ]⋆ ts}} {{[ i ≔ s ]⍟ us}}
  [ i ≔ s ] box t                = box t
  [ i ≔ s ] unbox t u            = unbox ([ i ≔ s ] t) ([ i ≔ mmono⊢ weak⊆ s ] u)
  [ i ≔ s ] pair t u             = pair ([ i ≔ s ] t) ([ i ≔ s ] u)
  [ i ≔ s ] fst t                = fst ([ i ≔ s ] t)
  [ i ≔ s ] snd t                = snd ([ i ≔ s ] t)
  [ i ≔ s ] unit                 = unit

  [_≔_]⋆_ : ∀ {Ξ A Γ Δ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢⋆ Ξ → Γ ∖ i ⁏ Δ ⊢⋆ Ξ
  [_≔_]⋆_ i s ∙        = ∙
  [_≔_]⋆_ i s (ts , t) = [ i ≔ s ]⋆ ts , [ i ≔ s ] t

  [_≔_]⍟_ : ∀ {Ξ A Γ Δ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢⍟ Ξ → Γ ∖ i ⁏ Δ ⊢⍟ Ξ
  [_≔_]⍟_ i s ∙        = ∙
  [_≔_]⍟_ i s (ts , t) = [ i ≔ s ]⍟ ts , [ i ≔ s ] t


-- Modal substitution.

mutual
  m[_≔_]_ : ∀ {Ψ Ω A C t Γ Δ} → (i : [ Ψ ⁏ Ω ⊢ t ] A ∈ Δ) → Ψ ⁏ Δ ∖ i ⊢ A → Γ ⁏ Δ ⊢ C → Γ ⁏ Δ ∖ i ⊢ C
  m[ i ≔ s ] var j                 = var j
  m[ i ≔ s ] lam t                 = lam (m[ i ≔ s ] t)
  m[ i ≔ s ] app t u               = app (m[ i ≔ s ] t) (m[ i ≔ s ] u)
  m[ i ≔ s ] mvar j  {{ts}} {{us}} with i ≟∈ j
  m[ i ≔ s ] mvar .i {{ts}} {{us}} | same   = multicut (m[ i ≔ s ]⋆ ts) s
  m[ i ≔ s ] mvar ._ {{ts}} {{us}} | diff j = mvar j {{m[ i ≔ s ]⋆ ts}} {{m[ i ≔ s ]⍟ us}}
  m[ i ≔ s ] box t                 = box t
  m[ i ≔ s ] unbox t u             = unbox (m[ i ≔ s ] t) (m[ pop i ≔ mmono⊢ weak⊆ s ] u)
  m[ i ≔ s ] pair t u              = pair (m[ i ≔ s ] t) (m[ i ≔ s ] u)
  m[ i ≔ s ] fst t                 = fst (m[ i ≔ s ] t)
  m[ i ≔ s ] snd t                 = snd (m[ i ≔ s ] t)
  m[ i ≔ s ] unit                  = unit

  m[_≔_]⋆_ : ∀ {Ξ Ψ Ω A t Γ Δ} → (i : [ Ψ ⁏ Ω ⊢ t ] A ∈ Δ) → Ψ ⁏ Δ ∖ i ⊢ A → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ∖ i ⊢⋆ Ξ
  m[_≔_]⋆_ i s ∙        = ∙
  m[_≔_]⋆_ i s (ts , t) = m[ i ≔ s ]⋆ ts , m[ i ≔ s ] t

  m[_≔_]⍟_ : ∀ {Ξ Ψ Ω A t Γ Δ} → (i : [ Ψ ⁏ Ω ⊢ t ] A ∈ Δ) → Ψ ⁏ Δ ∖ i ⊢ A → Γ ⁏ Δ ⊢⍟ Ξ → Γ ⁏ Δ ∖ i ⊢⍟ Ξ
  m[_≔_]⍟_ i s ∙        = ∙
  m[_≔_]⍟_ i s (ts , t) = m[ i ≔ s ]⍟ ts , m[ i ≔ s ] t


-- TODO: Convertibility.


-- Examples from the Nanevski-Pfenning-Pientka paper.

-- NOTE: In many cases, the instance argument for mvar can be automatically inferred, but not always.

module Examples₁ where
  e₁ : ∀ {A C D Γ Δ t}
        → Γ ⁏ Δ ⊢ [ ∅ , C ⁏ Δ ⊢ t ] A ▻
                    [ ∅ , C , D ⁏ Δ , [ ∅ , C ⁏ Δ ⊢ t ] A ⊢ mv₀ ] A
  e₁ = lam (unbox v₀ (box mv₀))

  e₂ : ∀ {A C Γ Δ t}
        → Γ ⁏ Δ ⊢ [ ∅ , C , C ⁏ Δ ⊢ t ] A ▻
                    [ ∅ , C ⁏ Δ , [ ∅ , C , C ⁏ Δ ⊢ t ] A ⊢ mv₀ ] A
  e₂ = lam (unbox v₀ (box mv₀))

  e₃ : ∀ {A Γ Δ}
        → Γ ⁏ Δ ⊢ [ ∅ , A ⁏ Δ ⊢ v₀ ] A
  e₃ = box v₀

  e₄ : ∀ {A B C Γ Δ t u v}
        → Γ ⁏ Δ ⊢ [ ∅ , A ⁏ Δ ⊢ t ] B ▻
                    [ ∅ , A ⁏ Δ ⊢ v ] [ ∅ , B ⁏ Δ ⊢ u ] C ▻
                    [ ∅ , A ⁏ Δ , [ ∅ , A ⁏ Δ ⊢ t ] B
                                , [ ∅ , A ⁏ Δ ⊢ v ] [ ∅ , B ⁏ Δ ⊢ u ] C
                                ⊢ unbox mv₀ (mv₀ {{∙ , mv₂}}) ] C
  e₄ = lam (lam (unbox v₁ (unbox v₀ (box
         (unbox mv₀ (mv₀ {{∙ , mv₂}}))))))

  e₅ : ∀ {A Γ Δ t}
        → Γ ⁏ Δ ⊢ [ ∅ ⁏ Δ ⊢ t ] A ▻ A
  e₅ = lam (unbox v₀ mv₀)

  e₆ : ∀ {A C D Γ Δ t}
        → Γ ⁏ Δ ⊢ [ ∅ , C ⁏ Δ ⊢ t ] A ▻
                    [ ∅ , D ⁏ Δ ⊢ box mv₀ ]
                      [ ∅ , C ⁏ Δ , [ ∅ , C ⁏ Δ ⊢ t ]
                        A ⊢ mv₀ ] A
  e₆ = lam (unbox v₀ (box (box mv₀)))

  e₇ : ∀ {A B C D Γ Δ t u}
        → Γ ⁏ Δ ⊢ [ ∅ , C ⁏ Δ ⊢ t ] (A ▻ B) ▻
                    [ ∅ , D ⁏ Δ ⊢ u ] A ▻
                    [ ∅ , C , D ⁏ Δ , [ ∅ , C ⁏ Δ ⊢ t ] (A ▻ B)
                                    , [ ∅ , D ⁏ Δ ⊢ u ] A
                                    ⊢ app mv₁ mv₀ ] B
  e₇ = lam (lam (unbox v₁ (unbox v₀ (box
         (app mv₁ mv₀)))))

  e₈ : ∀ {A B C Γ Δ t u}
        → Γ ⁏ Δ ⊢ [ ∅ , A ⁏ Δ ⊢ t ] (A ▻ B) ▻
                    [ ∅ , B ⁏ Δ ⊢ u ] C ▻
                    [ ∅ , A ⁏ Δ , [ ∅ , A ⁏ Δ ⊢ t ] (A ▻ B)
                                , [ ∅ , B ⁏ Δ ⊢ u ] C
                                ⊢ mv₀ {{∙ , app mv₁ v₀}} ] C
  e₈ = lam (lam (unbox v₁ (unbox v₀ (box
         (mv₀ {{∙ , app mv₁ v₀}})))))


-- Examples from the Alt-Artemov paper.

module Examples₂ where
  e₁ : ∀ {A Γ Δ t}
        → Γ ⁏ Δ ⊢ [ ∅ ⁏ Δ ⊢ lam (down v₀) ]
                      ([ ∅ ⁏ Δ ⊢ t ] A ▻ A)
  e₁ = box (lam (down v₀))

  e₂ : ∀ {A Γ Δ t}
        → Γ ⁏ Δ ⊢ [ ∅ ⁏ Δ ⊢ lam (up v₀) ]
                      ([ ∅ ⁏ Δ ⊢ t ] A ▻
                       [ ∅ ⁏ Δ ⊢ box mv₀ ]
                         [ ∅ ⁏ Δ , [ ∅ ⁏ Δ ⊢ t ]
                           A ⊢ mv₀ ] A)
  e₂ = box (lam (up v₀))

  e₃ : ∀ {A B Γ Δ}
        → Γ ⁏ Δ ⊢ [ ∅ ⁏ Δ ⊢ box (lam (lam (pair v₁ v₀))) ]
                      [ ∅ ⁏ Δ ⊢ lam (lam (pair v₁ v₀)) ]
                        (A ▻ B ▻ A ∧ B)
  e₃ = box (box (lam (lam (pair v₁ v₀))))

  e₄ : ∀ {A B Γ Δ t u}
        → Γ ⁏ Δ ⊢ [ ∅ ⁏ Δ ⊢ lam (lam (unbox v₁ (unbox v₀ (box
                                 (box (pair mv₁ mv₀)))))) ]
                      ([ ∅ ⁏ Δ ⊢ t ] A ▻
                       [ ∅ ⁏ Δ ⊢ u ] B ▻
                       [ ∅ ⁏ Δ ⊢ box (pair mv₁ mv₀) ]
                         [ ∅ ⁏ Δ , [ ∅ ⁏ Δ ⊢ t ] A
                                 , [ ∅ ⁏ Δ ⊢ u ] B
                                 ⊢ pair mv₁ mv₀ ]
                           (A ∧ B))
  e₄ = box (lam (lam (unbox v₁ (unbox v₀ (box
         (box (pair mv₁ mv₀)))))))
