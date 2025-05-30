{-# OPTIONS --sized-types #-}

-- Basic intuitionistic modal logic S4, without ∨, ⊥, or ◇.
-- Gentzen-style formalisation of labelled syntax, after Basin-Matthews-Viganò.

module A201607.BasicIS4.Syntax.LabelledGentzen where

open import A201607.BasicIS4.Syntax.Common public


-- Labels, as in Gabbay’s labelled deductive systems.

postulate
  Label : Set


-- Label pairs, or relational access tokens.
-- x ↝ y means the world labelled y is accessible from the world labelled x.

infix 6 _↝_
record Token : Set where
  constructor _↝_
  field
    x : Label
    y : Label


-- Labelled types.
-- A ◎ x means the type A is inhabited at the world labelled x.

infix 6 _◎_
record LabelledTy : Set where
  constructor _◎_
  field
    A : Ty
    x : Label

infix 6 _◎⋆_
_◎⋆_ : Cx Ty → Label → Cx LabelledTy
∅       ◎⋆ x = ∅
(Ξ , A) ◎⋆ x = Ξ ◎⋆ x , A ◎ x


-- Derivations.

infix 3 _⊢ᴿ_
data _⊢ᴿ_ (Λ : Cx Token) : Token → Set where
  rvar   : ∀ {x y}   → x ↝ y ∈ Λ → Λ ⊢ᴿ x ↝ y
  rrefl  : ∀ {x}     → Λ ⊢ᴿ x ↝ x
  rtrans : ∀ {x y z} → Λ ⊢ᴿ x ↝ y → Λ ⊢ᴿ y ↝ z → Λ ⊢ᴿ x ↝ z

infix 3 _⊢_
data _⊢_ : Cx² Ty Token → LabelledTy → Set where
  var  : ∀ {x A Γ Λ}   → A ∈ Γ → Γ ⁏ Λ ⊢ A ◎ x
  lam  : ∀ {x A B Γ Λ} → Γ , A ⁏ Λ ⊢ B ◎ x → Γ ⁏ Λ ⊢ A ▻ B ◎ x
  app  : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ A ▻ B ◎ x → Γ ⁏ Λ ⊢ A ◎ x → Γ ⁏ Λ ⊢ B ◎ x
  scan : ∀ {x A Γ Λ}   → (∀ {y} → Γ ⁏ Λ , x ↝ y ⊢ A ◎ y) → Γ ⁏ Λ ⊢ □ A ◎ x
  move : ∀ {x y A Γ Λ} → Γ ⁏ Λ ⊢ □ A ◎ x → Λ ⊢ᴿ x ↝ y → Γ ⁏ Λ ⊢ A ◎ y
  pair : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ A ◎ x → Γ ⁏ Λ ⊢ B ◎ x → Γ ⁏ Λ ⊢ A ∧ B ◎ x
  fst  : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ A ∧ B ◎ x → Γ ⁏ Λ ⊢ A ◎ x
  snd  : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ A ∧ B ◎ x → Γ ⁏ Λ ⊢ B ◎ x
  unit : ∀ {x Γ Λ}     → Γ ⁏ Λ ⊢ ⊤ ◎ x

infix 3 _⊢⋆_
_⊢⋆_ : Cx² Ty Token → Cx LabelledTy → Set
Γ ⁏ Λ ⊢⋆ ∅     = 𝟙
Γ ⁏ Λ ⊢⋆ Ξ , A = Γ ⁏ Λ ⊢⋆ Ξ × Γ ⁏ Λ ⊢ A


-- Monotonicity with respect to context inclusion.

mono⊢ : ∀ {x A Γ Γ′ Λ} → Γ ⊆ Γ′ → Γ ⁏ Λ ⊢ A ◎ x → Γ′ ⁏ Λ ⊢ A ◎ x
mono⊢ η (var i)    = var (mono∈ η i)
mono⊢ η (lam t)    = lam (mono⊢ (keep η) t)
mono⊢ η (app t u)  = app (mono⊢ η t) (mono⊢ η u)
mono⊢ η (scan t)   = scan (mono⊢ η t)
mono⊢ η (move t u) = move (mono⊢ η t) u
mono⊢ η (pair t u) = pair (mono⊢ η t) (mono⊢ η u)
mono⊢ η (fst t)    = fst (mono⊢ η t)
mono⊢ η (snd t)    = snd (mono⊢ η t)
mono⊢ η unit       = unit

mono⊢⋆ : ∀ {Ξ x Γ Γ′ Λ} → Γ ⊆ Γ′ → Γ ⁏ Λ ⊢⋆ Ξ ◎⋆ x → Γ′ ⁏ Λ ⊢⋆ Ξ ◎⋆ x
mono⊢⋆ {∅}     η ∙        = ∙
mono⊢⋆ {Ξ , A} η (ts , t) = mono⊢⋆ η ts , mono⊢ η t


-- Monotonicity with respect to relational context inclusion.

rmono⊢ᴿ : ∀ {x y Λ Λ′} → Λ ⊆ Λ′ → Λ ⊢ᴿ x ↝ y → Λ′ ⊢ᴿ x ↝ y
rmono⊢ᴿ ρ (rvar i)     = rvar (mono∈ ρ i)
rmono⊢ᴿ ρ rrefl        = rrefl
rmono⊢ᴿ ρ (rtrans t u) = rtrans (rmono⊢ᴿ ρ t) (rmono⊢ᴿ ρ u)

rmono⊢ : ∀ {x A Γ Λ Λ′} → Λ ⊆ Λ′ → Γ ⁏ Λ ⊢ A ◎ x → Γ ⁏ Λ′ ⊢ A ◎ x
rmono⊢ ρ (var i)    = var i
rmono⊢ ρ (lam t)    = lam (rmono⊢ ρ t)
rmono⊢ ρ (app t u)  = app (rmono⊢ ρ t) (rmono⊢ ρ u)
rmono⊢ ρ (scan t)   = scan (rmono⊢ (keep ρ) t)
rmono⊢ ρ (move t u) = move (rmono⊢ ρ t) (rmono⊢ᴿ ρ u)
rmono⊢ ρ (pair t u) = pair (rmono⊢ ρ t) (rmono⊢ ρ u)
rmono⊢ ρ (fst t)    = fst (rmono⊢ ρ t)
rmono⊢ ρ (snd t)    = snd (rmono⊢ ρ t)
rmono⊢ ρ unit       = unit

rmono⊢⋆ : ∀ {Ξ x Γ Λ Λ′} → Λ ⊆ Λ′ → Γ ⁏ Λ ⊢⋆ Ξ ◎⋆ x → Γ ⁏ Λ′ ⊢⋆ Ξ ◎⋆ x
rmono⊢⋆ {∅}     ρ ∙        = ∙
rmono⊢⋆ {Ξ , A} ρ (ts , t) = rmono⊢⋆ ρ ts , rmono⊢ ρ t


-- Monotonicity using context pairs.

mono²⊢ : ∀ {x A Π Π′} → Π ⊆² Π′ → Π ⊢ A ◎ x → Π′ ⊢ A ◎ x
mono²⊢ (η , ρ) = mono⊢ η ∘ rmono⊢ ρ


-- Shorthand for variables.

v₀ : ∀ {x A Γ Λ} → Γ , A ⁏ Λ ⊢ A ◎ x
v₀ = var i₀

v₁ : ∀ {x A B Γ Λ} → Γ , A , B ⁏ Λ ⊢ A ◎ x
v₁ = var i₁

v₂ : ∀ {x A B C Γ Λ} → Γ , A , B , C ⁏ Λ ⊢ A ◎ x
v₂ = var i₂

rv₀ : ∀ {x y Λ} → Λ , x ↝ y ⊢ᴿ x ↝ y
rv₀ = rvar i₀

rv₁ : ∀ {x y x′ y′ Λ} → Λ , x ↝ y , x′ ↝ y′ ⊢ᴿ x ↝ y
rv₁ = rvar i₁

rv₂ : ∀ {x y x′ y′ x″ y″ Λ} → Λ , x ↝ y , x′ ↝ y′ , x″ ↝ y″ ⊢ᴿ x ↝ y
rv₂ = rvar i₂


-- Reflexivity.

refl⊢⋆ : ∀ {Γ x Λ} → Γ ⁏ Λ ⊢⋆ Γ ◎⋆ x
refl⊢⋆ {∅}     = ∙
refl⊢⋆ {Γ , A} = mono⊢⋆ weak⊆ refl⊢⋆ , v₀


-- Deduction theorem is built-in.

lam⋆ : ∀ {Ξ x A Γ Λ} → Γ ⧺ Ξ ⁏ Λ ⊢ A ◎ x → Γ ⁏ Λ ⊢ Ξ ▻⋯▻ A ◎ x
lam⋆ {∅}     = I
lam⋆ {Ξ , B} = lam⋆ {Ξ} ∘ lam

lam⋆₀ : ∀ {Γ x A Λ} → Γ ⁏ Λ ⊢ A ◎ x → ∅ ⁏ Λ ⊢ Γ ▻⋯▻ A ◎ x
lam⋆₀ {∅}     = I
lam⋆₀ {Γ , B} = lam⋆₀ ∘ lam


-- Detachment theorem.

det : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ A ▻ B ◎ x → Γ , A ⁏ Λ ⊢ B ◎ x
det t = app (mono⊢ weak⊆ t) v₀

det⋆ : ∀ {Ξ x A Γ Λ} → Γ ⁏ Λ ⊢ Ξ ▻⋯▻ A ◎ x → Γ ⧺ Ξ ⁏ Λ ⊢ A ◎ x
det⋆ {∅}     = I
det⋆ {Ξ , B} = det ∘ det⋆ {Ξ}

det⋆₀ : ∀ {Γ x A Λ} → ∅ ⁏ Λ ⊢ Γ ▻⋯▻ A ◎ x → Γ ⁏ Λ ⊢ A ◎ x
det⋆₀ {∅}     = I
det⋆₀ {Γ , B} = det ∘ det⋆₀


-- Cut and multicut.

cut : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ A ◎ x → Γ , A ⁏ Λ ⊢ B ◎ x → Γ ⁏ Λ ⊢ B ◎ x
cut t u = app (lam u) t

multicut : ∀ {Ξ x A Γ Λ} → Γ ⁏ Λ ⊢⋆ Ξ ◎⋆ x → Ξ ⁏ Λ ⊢ A ◎ x → Γ ⁏ Λ ⊢ A ◎ x
multicut {∅}     ∙        u = mono⊢ bot⊆ u
multicut {Ξ , B} (ts , t) u = app (multicut ts (lam u)) t


-- Transitivity.

trans⊢⋆ : ∀ {Γ″ x Γ′ Γ Λ} → Γ ⁏ Λ ⊢⋆ Γ′ ◎⋆ x → Γ′ ⁏ Λ ⊢⋆ Γ″ ◎⋆ x → Γ ⁏ Λ ⊢⋆ Γ″ ◎⋆ x
trans⊢⋆ {∅}      ts ∙        = ∙
trans⊢⋆ {Γ″ , A} ts (us , u) = trans⊢⋆ ts us , multicut ts u


-- Contraction.

ccont : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ (A ▻ A ▻ B) ▻ A ▻ B ◎ x
ccont = lam (lam (app (app v₁ v₀) v₀))

cont : ∀ {x A B Γ Λ} → Γ , A , A ⁏ Λ ⊢ B ◎ x → Γ , A ⁏ Λ ⊢ B ◎ x
cont t = det (app ccont (lam (lam t)))


-- Exchange, or Schönfinkel’s C combinator.

cexch : ∀ {x A B C Γ Λ} → Γ ⁏ Λ ⊢ (A ▻ B ▻ C) ▻ B ▻ A ▻ C ◎ x
cexch = lam (lam (lam (app (app v₂ v₀) v₁)))

exch : ∀ {x A B C Γ Λ} → Γ , A , B ⁏ Λ ⊢ C ◎ x → Γ , B , A  ⁏ Λ ⊢ C ◎ x
exch t = det (det (app cexch (lam (lam t))))


-- Composition, or Schönfinkel’s B combinator.

ccomp : ∀ {x A B C Γ Λ} → Γ ⁏ Λ ⊢ (B ▻ C) ▻ (A ▻ B) ▻ A ▻ C ◎ x
ccomp = lam (lam (lam (app v₂ (app v₁ v₀))))

comp : ∀ {x A B C Γ Λ} → Γ , B ⁏ Λ ⊢ C ◎ x → Γ , A ⁏ Λ ⊢ B ◎ x → Γ , A ⁏ Λ ⊢ C ◎ x
comp t u = det (app (app ccomp (lam t)) (lam u))


-- Useful theorems in functional form.

dist : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ □ (A ▻ B) ◎ x → Γ ⁏ Λ ⊢ □ A ◎ x → Γ ⁏ Λ ⊢ □ B ◎ x
dist t u = scan (app (move (rmono⊢ weak⊆ t) rv₀) (move (rmono⊢ weak⊆ u) rv₀))

up : ∀ {x A Γ Λ} → Γ ⁏ Λ ⊢ □ A ◎ x → Γ ⁏ Λ ⊢ □ □ A ◎ x
up t = scan (scan (move (rmono⊢ (trans⊆ weak⊆ weak⊆) t) (rtrans rv₁ rv₀)))

down : ∀ {x A Γ Λ} → Γ ⁏ Λ ⊢ □ A ◎ x → Γ ⁏ Λ ⊢ A ◎ x
down t = move t rrefl

distup : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ □ (□ A ▻ B) ◎ x → Γ ⁏ Λ ⊢ □ A ◎ x → Γ ⁏ Λ ⊢ □ B ◎ x
distup t u = dist t (up u)

box : ∀ {x A Γ Λ} → (∀ {y} → ∅ ⁏ Λ , x ↝ y ⊢ A ◎ y) → Γ ⁏ Λ ⊢ □ A ◎ x
box t = scan (mono⊢ bot⊆ t)

unbox : ∀ {x A C Γ Λ} → Γ ⁏ Λ ⊢ □ A ◎ x → Γ , □ A ⁏ Λ ⊢ C ◎ x → Γ ⁏ Λ ⊢ C ◎ x
unbox t u = app (lam u) t


-- Useful theorems in combinatory form.

ci : ∀ {x A Γ Λ} → Γ ⁏ Λ ⊢ A ▻ A ◎ x
ci = lam v₀

ck : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ A ▻ B ▻ A ◎ x
ck = lam (lam v₁)

cs : ∀ {x A B C Γ Λ} → Γ ⁏ Λ ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C ◎ x
cs = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))

cdist : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ □ (A ▻ B) ▻ □ A ▻ □ B ◎ x
cdist = lam (lam (scan (app (move v₁ rv₀) (move v₀ rv₀))))

cup : ∀ {x A Γ Λ} → Γ ⁏ Λ ⊢ □ A ▻ □ □ A ◎ x
cup = lam (scan (scan (move v₀ (rtrans rv₁ rv₀))))

cdown : ∀ {x A Γ Λ} → Γ ⁏ Λ ⊢ □ A ▻ A ◎ x
cdown = lam (move v₀ rrefl)

cdistup : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ □ (□ A ▻ B) ▻ □ A ▻ □ B ◎ x
cdistup = lam (lam (app (app cdist v₁) (app cup v₀)))

cunbox : ∀ {x A C Γ Λ} → Γ ⁏ Λ ⊢ □ A ▻ (□ A ▻ C) ▻ C ◎ x
cunbox = lam (lam (app v₀ v₁))

cpair : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ A ▻ B ▻ A ∧ B ◎ x
cpair = lam (lam (pair v₁ v₀))

cfst : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ A ∧ B ▻ A ◎ x
cfst = lam (fst v₀)

csnd : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ A ∧ B ▻ B ◎ x
csnd = lam (snd v₀)


-- Internalisation, or lifting, and additional theorems.

lift : ∀ {Γ x A Λ} → (∀ {y} → Γ ⁏ Λ , x ↝ y ⊢ A ◎ y) → □⋆ Γ ⁏ Λ ⊢ □ A ◎ x
lift {∅}     t = box t
lift {Γ , B} t = det (app cdist (lift (lam t)))

hypup : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ A ▻ B ◎ x → Γ ⁏ Λ ⊢ □ A ▻ B ◎ x
hypup t = lam (app (mono⊢ weak⊆ t) (down v₀))

hypdown : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ □ □ A ▻ B ◎ x → Γ ⁏ Λ ⊢ □ A ▻ B ◎ x
hypdown t = lam (app (mono⊢ weak⊆ t) (up v₀))

cxup : ∀ {Γ x A Λ} → Γ ⁏ Λ ⊢ A ◎ x → □⋆ Γ ⁏ Λ ⊢ A ◎ x
cxup {∅}     t = t
cxup {Γ , B} t = det (hypup (cxup (lam t)))

cxdown : ∀ {Γ x A Λ} → □⋆ □⋆ Γ ⁏ Λ ⊢ A ◎ x → □⋆ Γ ⁏ Λ ⊢ A ◎ x
cxdown {∅}     t = t
cxdown {Γ , B} t = det (hypdown (cxdown (lam t)))

box⋆ : ∀ {Ξ x Γ Λ} → (∀ {y} → ∅ ⁏ Λ , x ↝ y ⊢⋆ Ξ ◎⋆ y) → Γ ⁏ Λ ⊢⋆ □⋆ Ξ ◎⋆ x
box⋆ {∅}     f = ∙
box⋆ {Ξ , A} f = box⋆ (π₁ f) , box (π₂ f)

lift⋆ : ∀ {Ξ x Γ Λ} → (∀ {y} → Γ ⁏ Λ , x ↝ y ⊢⋆ Ξ ◎⋆ y) → □⋆ Γ ⁏ Λ ⊢⋆ □⋆ Ξ ◎⋆ x
lift⋆ {∅}     f = ∙
lift⋆ {Ξ , A} f = lift⋆ (π₁ f) , lift (π₂ f)

up⋆ : ∀ {Ξ x Γ Λ} → Γ ⁏ Λ ⊢⋆ □⋆ Ξ ◎⋆ x → Γ ⁏ Λ ⊢⋆ □⋆ □⋆ Ξ ◎⋆ x
up⋆ {∅}     f = ∙
up⋆ {Ξ , A} f = up⋆ (π₁ f) , up (π₂ f)

down⋆ : ∀ {Ξ x Γ Λ} → Γ ⁏ Λ ⊢⋆ □⋆ Ξ ◎⋆ x → Γ ⁏ Λ ⊢⋆ Ξ ◎⋆ x
down⋆ {∅}     f = ∙
down⋆ {Ξ , A} f = down⋆ (π₁ f) , down (π₂ f)

multibox : ∀ {Ξ x A Γ Λ} → Γ ⁏ Λ ⊢⋆ □⋆ Ξ ◎⋆ x → (∀ {y} → □⋆ Ξ ⁏ ∅ , x ↝ y ⊢ A ◎ y) → Γ ⁏ Λ ⊢ □ A ◎ x
multibox ts u = multicut (up⋆ ts) (rmono⊢ bot⊆ (lift u))

dist′ : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ □ (A ▻ B) ◎ x → Γ ⁏ Λ ⊢ □ A ▻ □ B ◎ x
dist′ t = lam (dist (mono⊢ weak⊆ t) v₀)

mpair : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ □ A ◎ x → Γ ⁏ Λ ⊢ □ B ◎ x → Γ ⁏ Λ ⊢ □ (A ∧ B) ◎ x
mpair t u = scan (pair (move (rmono⊢ weak⊆ t) rv₀) (move (rmono⊢ weak⊆ u) rv₀))

mfst : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ □ (A ∧ B) ◎ x → Γ ⁏ Λ ⊢ □ A ◎ x
mfst t = scan (fst (move (rmono⊢ weak⊆ t) rv₀))

msnd : ∀ {x A B Γ Λ} → Γ ⁏ Λ ⊢ □ (A ∧ B) ◎ x → Γ ⁏ Λ ⊢ □ B ◎ x
msnd t = scan (snd (move (rmono⊢ weak⊆ t) rv₀))


-- Closure under context concatenation.

concat : ∀ {x A B Γ} Γ′ {Λ} → Γ , A ⁏ Λ ⊢ B ◎ x → Γ′ ⁏ Λ ⊢ A ◎ x → Γ ⧺ Γ′ ⁏ Λ ⊢ B ◎ x
concat Γ′ t u = app (mono⊢ (weak⊆⧺₁ Γ′) (lam t)) (mono⊢ weak⊆⧺₂ u)


-- TODO: Substitution.

-- [_≔_]_ : ∀ {x A B Γ Λ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Λ ⊢ A ◎ x → Γ ⁏ Λ ⊢ B ◎ x → Γ ∖ i ⁏ Λ ⊢ B ◎ x
-- [ i ≔ s ] var j    with i ≟∈ j
-- [ i ≔ s ] var .i   | same   = s
-- [ i ≔ s ] var ._   | diff j = var j
-- [ i ≔ s ] lam t    = lam ([ pop i ≔ mono⊢ weak⊆ s ] t)
-- [ i ≔ s ] app t u  = app ([ i ≔ s ] t) ([ i ≔ s ] u)
-- [ i ≔ s ] scan t   = scan {![ i ≔ rmono⊢ weak⊆ s ] t!}
-- [ i ≔ s ] move t u = move {![ i ≔ s ] t!} u
-- [ i ≔ s ] pair t u = pair ([ i ≔ s ] t) ([ i ≔ s ] u)
-- [ i ≔ s ] fst t    = fst ([ i ≔ s ] t)
-- [ i ≔ s ] snd t    = snd ([ i ≔ s ] t)
-- [ i ≔ s ] unit     = unit


-- TODO: Convertibility.
