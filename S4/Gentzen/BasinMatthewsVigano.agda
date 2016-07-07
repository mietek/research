module S4.Gentzen.BasinMatthewsVigano where

open import S4.Core public


-- Labels, as in Gabbay’s labelled deductive systems (LDS).

postulate
  La : Set

infix 3 _≤_
record LaLa : Set where
  constructor _≤_
  field
    x : La
    y : La

infix 3 _⦂_
record LaTy : Set where
  constructor _⦂_
  field
    x : La
    A : Ty


-- Proofs of S4, as labelled Gentzen-style natural deduction trees, following Basin, Matthews, and Viganò.

infix 1 _⊢_≤_
data _⊢_≤_ (Ξ : Cx LaLa) : La → La → Set where
  rvar   : ∀ {x y} → x ≤ y ∈ Ξ → Ξ ⊢ x ≤ y
  rrefl  : ∀ {x} → Ξ ⊢ x ≤ x
  rtrans : ∀ {x y z} → Ξ ⊢ x ≤ y → Ξ ⊢ y ≤ z → Ξ ⊢ x ≤ z

infix 1 _⨾_⊢_⦂_
data _⨾_⊢_⦂_ (Γ : Cx LaTy) (Ξ : Cx LaLa) : La → Ty → Set where
  var  : ∀ {x A}   → x ⦂ A ∈ Γ → Γ ⨾ Ξ ⊢ x ⦂ A
  lam  : ∀ {x A B} → Γ , x ⦂ A ⨾ Ξ ⊢ x ⦂ B → Γ ⨾ Ξ ⊢ x ⦂ A ⊃ B
  app  : ∀ {x A B} → Γ ⨾ Ξ ⊢ x ⦂ A ⊃ B → Γ ⨾ Ξ ⊢ x ⦂ A → Γ ⨾ Ξ ⊢ x ⦂ B
  scan : ∀ {x A}   → (∀ {y} → Γ ⨾ Ξ , x ≤ y ⊢ y ⦂ A) → Γ ⨾ Ξ ⊢ x ⦂ □ A
  move : ∀ {x y A} → Γ ⨾ Ξ ⊢ x ⦂ □ A → Ξ ⊢ x ≤ y → Γ ⨾ Ξ ⊢ y ⦂ A
  unit : ∀ {x}     → Γ ⨾ Ξ ⊢ x ⦂ ι
  pair : ∀ {x A B} → Γ ⨾ Ξ ⊢ x ⦂ A → Γ ⨾ Ξ ⊢ x ⦂ B → Γ ⨾ Ξ ⊢ x ⦂ A ∧ B
  fst  : ∀ {x A B} → Γ ⨾ Ξ ⊢ x ⦂ A ∧ B → Γ ⨾ Ξ ⊢ x ⦂ A
  snd  : ∀ {x A B} → Γ ⨾ Ξ ⊢ x ⦂ A ∧ B → Γ ⨾ Ξ ⊢ x ⦂ B


-- Monotonicity of syntactic consequence with respect to intuitionistic context extension.

mono⊢ : ∀ {x A Γ Γ′ Ξ} → Γ ⊆ Γ′ → Γ ⨾ Ξ ⊢ x ⦂ A → Γ′ ⨾ Ξ ⊢ x ⦂ A
mono⊢ η (var i)    = var (mono∈ η i)
mono⊢ η (lam t)    = lam (mono⊢ (keep η) t)
mono⊢ η (app t u)  = app (mono⊢ η t) (mono⊢ η u)
mono⊢ η (scan t)   = scan (mono⊢ η t)
mono⊢ η (move t u) = move (mono⊢ η t) u
mono⊢ η unit       = unit
mono⊢ η (pair t u) = pair (mono⊢ η t) (mono⊢ η u)
mono⊢ η (fst t)    = fst (mono⊢ η t)
mono⊢ η (snd t)    = snd (mono⊢ η t)


-- Monotonicity of syntactic consequence with respect to relational context extension.

rmono⊢≤ : ∀ {x y Ξ Ξ′} → Ξ ⊆ Ξ′ → Ξ ⊢ x ≤ y → Ξ′ ⊢ x ≤ y
rmono⊢≤ η (rvar i)     = rvar (mono∈ η i)
rmono⊢≤ η rrefl        = rrefl
rmono⊢≤ η (rtrans t u) = rtrans (rmono⊢≤ η t) (rmono⊢≤ η u)

rmono⊢ : ∀ {x A Γ Ξ Ξ′} → Ξ ⊆ Ξ′ → Γ ⨾ Ξ ⊢ x ⦂ A → Γ ⨾ Ξ′ ⊢ x ⦂ A
rmono⊢ η (var i)    = var i
rmono⊢ η (lam t)    = lam (rmono⊢ η t)
rmono⊢ η (app t u)  = app (rmono⊢ η t) (rmono⊢ η u)
rmono⊢ η (scan t)   = scan (rmono⊢ (keep η) t)
rmono⊢ η (move t u) = move (rmono⊢ η t) (rmono⊢≤ η u)
rmono⊢ η unit       = unit
rmono⊢ η (pair t u) = pair (rmono⊢ η t) (rmono⊢ η u)
rmono⊢ η (fst t)    = fst (rmono⊢ η t)
rmono⊢ η (snd t)    = snd (rmono⊢ η t)


-- Shorthand for variables.

rv₀ : ∀ {x y Ξ} → Ξ , x ≤ y ⊢ x ≤ y
rv₀ = rvar top

rv₁ : ∀ {x y x′ y′ Ξ} → Ξ , x ≤ y , x′ ≤ y′ ⊢ x ≤ y
rv₁ = rvar (pop top)

rv₂ : ∀ {x y x′ y′ x″ y″ Ξ} → Ξ , x ≤ y , x′ ≤ y′ , x″ ≤ y″ ⊢ x ≤ y
rv₂ = rvar (pop (pop top))

v₀ : ∀ {x A Γ Ξ} → Γ , x ⦂ A ⨾ Ξ ⊢ x ⦂ A
v₀ = var top

v₁ : ∀ {x y A B Γ Ξ} → Γ , x ⦂ A , y ⦂ B ⨾ Ξ ⊢ x ⦂ A
v₁ = var (pop top)

v₂ : ∀ {x y z A B C Γ Ξ} → Γ , x ⦂ A , y ⦂ B , z ⦂ C ⨾ Ξ ⊢ x ⦂ A
v₂ = var (pop (pop top))


-- Deduction theorem is built-in.

-- TODO: mlam


-- Detachment theorem.

det : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ A ⊃ B → Γ , x ⦂ A ⨾ Ξ ⊢ x ⦂ B
det t = app (mono⊢ weak⊆ t) v₀

-- TODO: mdet


-- Contraction.

ccont : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ (A ⊃ A ⊃ B) ⊃ A ⊃ B
ccont = lam (lam (app (app v₁ v₀) v₀))

cont : ∀ {x A B Γ Ξ} → Γ , x ⦂ A , x ⦂ A ⨾ Ξ ⊢ x ⦂ B → Γ , x ⦂ A ⨾ Ξ ⊢ x ⦂ B
cont t = det (app ccont (lam (lam t)))

-- TODO: mcont


-- Exchange.

cexch : ∀ {x A B C Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ (A ⊃ B ⊃ C) ⊃ B ⊃ A ⊃ C
cexch = lam (lam (lam (app (app v₂ v₀) v₁)))

exch : ∀ {x A B C Γ Ξ} → Γ , x ⦂ A , x ⦂ B ⨾ Ξ ⊢ x ⦂ C → Γ , x ⦂ B , x ⦂ A ⨾ Ξ ⊢ x ⦂ C
exch t = det (det (app cexch (lam (lam t))))

-- TODO: mexch


-- Composition.

ccomp : ∀ {x A B C Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ (B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
ccomp = lam (lam (lam (app v₂ (app v₁ v₀))))

comp : ∀ {x A B C Γ Ξ} → Γ , x ⦂ B ⨾ Ξ ⊢ x ⦂ C → Γ , x ⦂ A ⨾ Ξ ⊢ x ⦂ B → Γ , x ⦂ A ⨾ Ξ ⊢ x ⦂ C
comp t u = det (app (app ccomp (lam t)) (lam u))

-- TODO: mcomp


-- Useful theorems in combinatory form.

ci : ∀ {x A Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ A ⊃ A
ci = lam v₀

ck : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ A ⊃ B ⊃ A
ck = lam (lam v₁)

cs : ∀ {x A B C Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
cs = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))

cdist : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ □ (A ⊃ B) ⊃ □ A ⊃ □ B
cdist = lam (lam (scan (app (move v₁ rv₀) (move v₀ rv₀))))

cup : ∀ {x A Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ □ A ⊃ □ □ A
cup = lam (scan (scan (move v₀ (rtrans rv₁ rv₀))))

cdown : ∀ {x A Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ □ A ⊃ A
cdown = lam (move v₀ rrefl)

cdistup : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ □ (□ A ⊃ B) ⊃ □ A ⊃ □ B
cdistup = lam (lam (app (app cdist v₁) (app cup v₀)))

cunbox : ∀ {x A C Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ □ A ⊃ (□ A ⊃ C) ⊃ C
cunbox = lam (lam (app v₀ v₁))

cpair : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ A ⊃ B ⊃ A ∧ B
cpair = lam (lam (pair v₁ v₀))

cfst : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ A ∧ B ⊃ A
cfst = lam (fst v₀)

csnd : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ A ∧ B ⊃ B
csnd = lam (snd v₀)


-- Useful theorems in functional form.

dist : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ □ (A ⊃ B) → Γ ⨾ Ξ ⊢ x ⦂ □ A → Γ ⨾ Ξ ⊢ x ⦂ □ B
dist t u = scan (app (move (rmono⊢ weak⊆ t) rv₀) (move (rmono⊢ weak⊆ u) rv₀))

up : ∀ {x A Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ □ A → Γ ⨾ Ξ ⊢ x ⦂ □ □ A
up t = scan (scan (move (rmono⊢ (trans⊆ weak⊆ weak⊆) t) (rtrans rv₁ rv₀)))

down : ∀ {x A Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ □ A → Γ ⨾ Ξ ⊢ x ⦂ A
down t = move t rrefl

distup : ∀ {x A B Γ Ξ} → Γ ⨾ Ξ ⊢ x ⦂ □ (□ A ⊃ B) → Γ ⨾ Ξ ⊢ x ⦂ □ A → Γ ⨾ Ξ ⊢ x ⦂ □ B
distup t u = dist t (up u)

-- TODO: box, unbox


-- Closure under context concatenation.

concat : ∀ {x A B Γ} Γ′ {Ξ} → Γ , x ⦂ A ⨾ Ξ ⊢ x ⦂ B → Γ′ ⨾ Ξ ⊢ x ⦂ A → Γ ⧺ Γ′ ⨾ Ξ ⊢ x ⦂ B
concat Γ′ t u = app (mono⊢ (weak⊆⧺ Γ′) (lam t)) (mono⊢ weak⊆⧺′ u)

-- TODO: mconcat


-- Substitution.

[_≔_]_ : ∀ {x y A C Γ Ξ} → (i : x ⦂ A ∈ Γ) → Γ - i ⨾ Ξ ⊢ x ⦂ A → Γ ⨾ Ξ ⊢ y ⦂ C → Γ - i ⨾ Ξ ⊢ y ⦂ C
[ i ≔ s ] var k    with i ≟∈ k
[ i ≔ s ] var .i   | same   = s
[ i ≔ s ] var ._   | diff k = var k
[ i ≔ s ] lam t    = lam ([ pop i ≔ mono⊢ weak⊆ s ] t)
[ i ≔ s ] app t u  = app ([ i ≔ s ] t) ([ i ≔ s ] u)
[ i ≔ s ] scan t   = scan ([ i ≔ rmono⊢ weak⊆ s ] t)
[ i ≔ s ] move t u = move ([ i ≔ s ] t) u
[ i ≔ s ] unit     = unit
[ i ≔ s ] pair t u = pair ([ i ≔ s ] t) ([ i ≔ s ] u)
[ i ≔ s ] fst t    = fst ([ i ≔ s ] t)
[ i ≔ s ] snd t    = snd ([ i ≔ s ] t)

-- TODO: msubst
