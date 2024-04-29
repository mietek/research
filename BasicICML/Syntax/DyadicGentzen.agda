-- Basic intuitionistic contextual modal logic, without ∨ or ⊥.
-- Gentzen-style formalisation of syntax with context pairs, after Nanevski-Pfenning-Pientka.
-- Simple terms.

module BasicICML.Syntax.DyadicGentzen where

open import BasicICML.Syntax.Common public


-- Derivations.

mutual
  infix 3 _⊢_
  data _⊢_ : Cx² Ty Box → Ty → Set where
    var : ∀ {A Γ Δ}       → A ∈ Γ → Γ ⁏ Δ ⊢ A
    lam   : ∀ {A B Γ Δ}   → Γ , A ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ A ▻ B
    app   : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ A ▻ B → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B
    mvar  : ∀ {Ψ A Γ Δ}   → [ Ψ ] A ∈ Δ → Γ ⁏ Δ ⊢⋆ Ψ → Γ ⁏ Δ ⊢ A
    box   : ∀ {Ψ A Γ Δ}   → Ψ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ [ Ψ ] A
    unbox : ∀ {Ψ A C Γ Δ} → Γ ⁏ Δ ⊢ [ Ψ ] A → Γ ⁏ Δ , [ Ψ ] A ⊢ C → Γ ⁏ Δ ⊢ C
    pair  : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ A ∧ B
    fst   : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ A ∧ B → Γ ⁏ Δ ⊢ A
    snd   : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ A ∧ B → Γ ⁏ Δ ⊢ B
    unit  : ∀ {Γ Δ}       → Γ ⁏ Δ ⊢ ⊤

  infix 3 _⊢⋆_
  data _⊢⋆_ : Cx² Ty Box → Cx Ty → Set where
    ∙   : ∀ {Γ Δ}     → Γ ⁏ Δ ⊢⋆ ∅
    _,_ : ∀ {Ξ A Γ Δ} → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢⋆ Ξ , A


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ : ∀ {A Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢ A → Γ′ ⁏ Δ ⊢ A
  mono⊢ η (var i)         = var (mono∈ η i)
  mono⊢ η (lam t)         = lam (mono⊢ (keep η) t)
  mono⊢ η (app t u)       = app (mono⊢ η t) (mono⊢ η u)
  mono⊢ η (mvar i ts)     = mvar i (mono⊢⋆ η ts)
  mono⊢ η (box t)         = box t
  mono⊢ η (unbox t u)     = unbox (mono⊢ η t) (mono⊢ η u)
  mono⊢ η (pair t u)      = pair (mono⊢ η t) (mono⊢ η u)
  mono⊢ η (fst t)         = fst (mono⊢ η t)
  mono⊢ η (snd t)         = snd (mono⊢ η t)
  mono⊢ η unit            = unit

  mono⊢⋆ : ∀ {Ξ Γ Γ′ Δ} → Γ ⊆ Γ′ → Γ ⁏ Δ ⊢⋆ Ξ → Γ′ ⁏ Δ ⊢⋆ Ξ
  mono⊢⋆ η ∙        = ∙
  mono⊢⋆ η (ts , t) = mono⊢⋆ η ts , mono⊢ η t


-- Monotonicity with respect to modal context inclusion.

mutual
  mmono⊢ : ∀ {A Γ Δ Δ′} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ′ ⊢ A
  mmono⊢ θ (var i)         = var i
  mmono⊢ θ (lam t)         = lam (mmono⊢ θ t)
  mmono⊢ θ (app t u)       = app (mmono⊢ θ t) (mmono⊢ θ u)
  mmono⊢ θ (mvar i ts)     = mvar (mono∈ θ i) (mmono⊢⋆ θ ts)
  mmono⊢ θ (box t)         = box (mmono⊢ θ t)
  mmono⊢ θ (unbox t u)     = unbox (mmono⊢ θ t) (mmono⊢ (keep θ) u)
  mmono⊢ θ (pair t u)      = pair (mmono⊢ θ t) (mmono⊢ θ u)
  mmono⊢ θ (fst t)         = fst (mmono⊢ θ t)
  mmono⊢ θ (snd t)         = snd (mmono⊢ θ t)
  mmono⊢ θ unit            = unit

  mmono⊢⋆ : ∀ {Ξ Δ Δ′ Γ} → Δ ⊆ Δ′ → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ′ ⊢⋆ Ξ
  mmono⊢⋆ θ ∙        = ∙
  mmono⊢⋆ θ (ts , t) = mmono⊢⋆ θ ts , mmono⊢ θ t


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

mv₀ : ∀ {Ψ A Γ Δ}
      → Γ ⁏ Δ , [ Ψ ] A ⊢⋆ Ψ
      → Γ ⁏ Δ , [ Ψ ] A ⊢ A
mv₀ = mvar i₀

mv₁ : ∀ {Ψ Ψ′ A B Γ Δ}
      → Γ ⁏ Δ , [ Ψ ] A , [ Ψ′ ] B ⊢⋆ Ψ
      → Γ ⁏ Δ , [ Ψ ] A , [ Ψ′ ] B ⊢ A
mv₁ = mvar i₁

mv₂ : ∀ {Ψ Ψ′ Ψ″ A B C Γ Δ}
      → Γ ⁏ Δ , [ Ψ ] A , [ Ψ′ ] B , [ Ψ″ ] C ⊢⋆ Ψ
      → Γ ⁏ Δ , [ Ψ ] A , [ Ψ′ ] B , [ Ψ″ ] C ⊢ A
mv₂ = mvar i₂


-- Generalised reflexivity.

grefl⊢⋆ : ∀ {Γ Ψ Δ} → Ψ ⊆ Γ → Γ ⁏ Δ ⊢⋆ Ψ
grefl⊢⋆ {∅}     done     = ∙
grefl⊢⋆ {Γ , A} (skip η) = mono⊢⋆ weak⊆ (grefl⊢⋆ η)
grefl⊢⋆ {Γ , A} (keep η) = mono⊢⋆ weak⊆ (grefl⊢⋆ η) , v₀

refl⊢⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢⋆ Γ
refl⊢⋆ = grefl⊢⋆ refl⊆


-- Deduction theorem is built-in.

-- Modal deduction theorem.

mlam : ∀ {Ψ A B Γ Δ}
      → Γ ⁏ Δ , [ Ψ ] A ⊢ B
      → Γ ⁏ Δ ⊢ [ Ψ ] A ▻ B
mlam t = lam (unbox v₀ (mono⊢ weak⊆ t))


-- Detachment theorems.

det : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▻ B → Γ , A ⁏ Δ ⊢ B
det t = app (mono⊢ weak⊆ t) v₀

mdet : ∀ {Ψ A B Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ] A ▻ B
      → Γ ⁏ Δ , [ Ψ ] A ⊢ B
mdet t = app (mmono⊢ weak⊆ t) (box (mv₀ refl⊢⋆))


-- Cut and multicut.

cut : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A → Γ , A ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ B
cut t u = app (lam u) t

mcut : ∀ {Ψ A B Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ] A
      → Γ ⁏ Δ , [ Ψ ] A ⊢ B
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

mcont : ∀ {Ψ A B Γ Δ} → Γ ⁏ Δ , [ Ψ ] A , [ Ψ ] A ⊢ B → Γ ⁏ Δ , [ Ψ ] A ⊢ B
mcont t = mdet (app ccont (mlam (mlam t)))


-- Exchange, or Schönfinkel’s C combinator.

cexch : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ (A ▻ B ▻ C) ▻ B ▻ A ▻ C
cexch = lam (lam (lam (app (app v₂ v₀) v₁)))

exch : ∀ {A B C Γ Δ} → Γ , A , B ⁏ Δ ⊢ C → Γ , B , A ⁏ Δ ⊢ C
exch t = det (det (app cexch (lam (lam t))))

mexch : ∀ {Ψ Ψ′ A B C Γ Δ}
      → Γ ⁏ Δ , [ Ψ ] A , [ Ψ′ ] B ⊢ C
      → Γ ⁏ Δ , [ Ψ′ ] B , [ Ψ ] A ⊢ C
mexch t = mdet (mdet (app cexch (mlam (mlam t))))


-- Composition, or Schönfinkel’s B combinator.

ccomp : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ (B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
ccomp = lam (lam (lam (app v₂ (app v₁ v₀))))

comp : ∀ {A B C Γ Δ} → Γ , B ⁏ Δ ⊢ C → Γ , A ⁏ Δ ⊢ B → Γ , A ⁏ Δ ⊢ C
comp t u = det (app (app ccomp (lam t)) (lam u))

mcomp : ∀ {Ψ Ψ′ Ψ″ A B C Γ Δ}
      → Γ ⁏ Δ , [ Ψ′ ] B ⊢ [ Ψ″ ] C
      → Γ ⁏ Δ , [ Ψ ] A ⊢ [ Ψ′ ] B
      → Γ ⁏ Δ , [ Ψ ] A ⊢ [ Ψ″ ] C
mcomp t u = mdet (app (app ccomp (mlam t)) (mlam u))


-- Useful theorems in functional form.

dist : ∀ {Ψ A B Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ] (A ▻ B)
      → Γ ⁏ Δ ⊢ [ Ψ ] A
      → Γ ⁏ Δ ⊢ [ Ψ ] B
dist t u = unbox t (unbox (mmono⊢ weak⊆ u) (box (app (mv₁ refl⊢⋆) (mv₀ refl⊢⋆))))

up : ∀ {Ψ A Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ] A
      → Γ ⁏ Δ ⊢ [ Ψ ] [ Ψ ] A
up t = unbox t (box (box (mv₀ refl⊢⋆)))

down : ∀ {Ψ A Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ] A
      → Γ ⁏ Δ , [ Ψ ] A ⊢⋆ Ψ
      → Γ ⁏ Δ ⊢ A
down t us = unbox t (mv₀ us)

distup : ∀ {Ψ A B Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ] ([ Ψ ] A ▻ B)
      → Γ ⁏ Δ ⊢ [ Ψ ] A
      → Γ ⁏ Δ ⊢ [ Ψ ] B
distup t u = dist t (up u)


-- Useful theorems in combinatory form.

ci : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ A ▻ A
ci = lam v₀

ck : ∀ {A B Γ Δ} → Γ ⁏ Δ ⊢ A ▻ B ▻ A
ck = lam (lam v₁)

cs : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
cs = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))

cdist : ∀ {Ψ A B Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ] (A ▻ B) ▻
                  [ Ψ ] A ▻
                  [ Ψ ] B
cdist = lam (lam (dist v₁ v₀))

cup : ∀ {Ψ A Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ] A ▻
                  [ Ψ ] [ Ψ ] A
cup = lam (up v₀)

cdistup : ∀ {Ψ A B Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ] ([ Ψ ] A ▻ B) ▻
                  [ Ψ ] A ▻ [ Ψ ] B
cdistup = lam (lam (dist v₁ (up v₀)))

cunbox : ∀ {Ψ A C Γ Δ}
      → Γ ⁏ Δ ⊢ [ Ψ ] A ▻
                  ([ Ψ ] A ▻ C) ▻
                  C
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

mconcat : ∀ {Ψ A B Γ Δ} Δ′ → Γ ⁏ Δ , [ Ψ ] A ⊢ B → Γ ⁏ Δ′ ⊢ [ Ψ ] A → Γ ⁏ Δ ⧺ Δ′ ⊢ B
mconcat Δ′ t u = app (mmono⊢ (weak⊆⧺₁ Δ′) (mlam t)) (mmono⊢ weak⊆⧺₂ u)


-- Substitution.

mutual
  [_≔_]_ : ∀ {A C Γ Δ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ C → Γ ∖ i ⁏ Δ ⊢ C
  [ i ≔ s ] var j         with i ≟∈ j
  [ i ≔ s ] var .i        | same   = s
  [ i ≔ s ] var ._        | diff j = var j
  [ i ≔ s ] lam t         = lam ([ pop i ≔ mono⊢ weak⊆ s ] t)
  [ i ≔ s ] app t u       = app ([ i ≔ s ] t) ([ i ≔ s ] u)
  [ i ≔ s ] mvar j ts     = mvar j ([ i ≔ s ]⋆ ts)
  [ i ≔ s ] box t         = box t
  [ i ≔ s ] unbox t u     = unbox ([ i ≔ s ] t) ([ i ≔ mmono⊢ weak⊆ s ] u)
  [ i ≔ s ] pair t u      = pair ([ i ≔ s ] t) ([ i ≔ s ] u)
  [ i ≔ s ] fst t         = fst ([ i ≔ s ] t)
  [ i ≔ s ] snd t         = snd ([ i ≔ s ] t)
  [ i ≔ s ] unit          = unit

  [_≔_]⋆_ : ∀ {Ξ A Γ Δ} → (i : A ∈ Γ) → Γ ∖ i ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢⋆ Ξ → Γ ∖ i ⁏ Δ ⊢⋆ Ξ
  [_≔_]⋆_ i s ∙        = ∙
  [_≔_]⋆_ i s (ts , t) = [ i ≔ s ]⋆ ts , [ i ≔ s ] t


-- Modal substitution.

mutual
  m[_≔_]_ : ∀ {Ψ A C Γ Δ} → (i : [ Ψ ] A ∈ Δ) → Ψ ⁏ Δ ∖ i ⊢ A → Γ ⁏ Δ ⊢ C → Γ ⁏ Δ ∖ i ⊢ C
  m[ i ≔ s ] var j          = var j
  m[ i ≔ s ] lam t          = lam (m[ i ≔ s ] t)
  m[ i ≔ s ] app t u        = app (m[ i ≔ s ] t) (m[ i ≔ s ] u)
  m[ i ≔ s ] mvar j  ts     with i ≟∈ j
  m[ i ≔ s ] mvar .i ts     | same   = multicut (m[ i ≔ s ]⋆ ts) s
  m[ i ≔ s ] mvar ._ ts     | diff j = mvar j (m[ i ≔ s ]⋆ ts)
  m[ i ≔ s ] box t          = box (m[ i ≔ s ] t)
  m[ i ≔ s ] unbox t u      = unbox (m[ i ≔ s ] t) (m[ pop i ≔ mmono⊢ weak⊆ s ] u)
  m[ i ≔ s ] pair t u       = pair (m[ i ≔ s ] t) (m[ i ≔ s ] u)
  m[ i ≔ s ] fst t          = fst (m[ i ≔ s ] t)
  m[ i ≔ s ] snd t          = snd (m[ i ≔ s ] t)
  m[ i ≔ s ] unit           = unit

  m[_≔_]⋆_ : ∀ {Ξ Ψ A Γ Δ} → (i : [ Ψ ] A ∈ Δ) → Ψ ⁏ Δ ∖ i ⊢ A → Γ ⁏ Δ ⊢⋆ Ξ → Γ ⁏ Δ ∖ i ⊢⋆ Ξ
  m[_≔_]⋆_ i s ∙        = ∙
  m[_≔_]⋆_ i s (ts , t) = m[ i ≔ s ]⋆ ts , m[ i ≔ s ] t


-- Convertibility.

data _⋙_ {Δ : Cx Box} {Γ : Cx Ty} : ∀ {A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A → Set where
  refl⋙      : ∀ {A} → {t : Γ ⁏ Δ ⊢ A}
                      → t ⋙ t

  trans⋙     : ∀ {A} → {t t′ t″ : Γ ⁏ Δ ⊢ A}
                      → t ⋙ t′ → t′ ⋙ t″
                      → t ⋙ t″

  sym⋙       : ∀ {A} → {t t′ : Γ ⁏ Δ ⊢ A}
                      → t ⋙ t′
                      → t′ ⋙ t

  conglam⋙   : ∀ {A B} → {t t′ : Γ , A ⁏ Δ ⊢ B}
                        → t ⋙ t′
                        → lam t ⋙ lam t′

  congapp⋙   : ∀ {A B} → {t t′ : Γ ⁏ Δ ⊢ A ▻ B} → {u u′ : Γ ⁏ Δ ⊢ A}
                        → t ⋙ t′ → u ⋙ u′
                        → app t u ⋙ app t′ u′

  -- NOTE: Rejected by Pfenning and Davies.
  -- congbox⋙   : ∀ {Ψ A} → {t t′ : Ψ ⁏ Δ ⊢ A}
  --                       → t ⋙ t′
  --                       → box t ⋙ box t′

  congunbox⋙ : ∀ {Ψ A C} → {t t′ : Γ ⁏ Δ ⊢ [ Ψ ] A} → {u u′ : Γ ⁏ Δ , [ Ψ ] A ⊢ C}
                          → t ⋙ t′ → u ⋙ u′
                          → unbox t u ⋙ unbox t′ u′

  congpair⋙  : ∀ {A B} → {t t′ : Γ ⁏ Δ ⊢ A} → {u u′ : Γ ⁏ Δ ⊢ B}
                        → t ⋙ t′ → u ⋙ u′
                        → pair t u ⋙ pair t′ u′

  congfst⋙   : ∀ {A B} → {t t′ : Γ ⁏ Δ ⊢ A ∧ B}
                        → t ⋙ t′
                        → fst t ⋙ fst t′

  congsnd⋙   : ∀ {A B} → {t t′ : Γ ⁏ Δ ⊢ A ∧ B}
                        → t ⋙ t′
                        → snd t ⋙ snd t′

  beta▻⋙     : ∀ {A B} → {t : Γ , A ⁏ Δ ⊢ B} → {u : Γ ⁏ Δ ⊢ A}
                        → app (lam t) u ⋙ ([ top ≔ u ] t)

  eta▻⋙      : ∀ {A B} → {t : Γ ⁏ Δ ⊢ A ▻ B}
                        → t ⋙ lam (app (mono⊢ weak⊆ t) v₀)

  beta□⋙     : ∀ {Ψ A C} → {t : Ψ ⁏ Δ ⊢ A} → {u : Γ ⁏ Δ , [ Ψ ] A ⊢ C}
                          → unbox (box t) u ⋙ (m[ top ≔ t ] u)

  eta□⋙      : ∀ {Ψ A} → {t : Γ ⁏ Δ ⊢ [ Ψ ] A}
                        → t ⋙ unbox t (box (mv₀ refl⊢⋆))

  -- TODO: What about commuting conversions for □?

  beta∧₁⋙    : ∀ {A B} → {t : Γ ⁏ Δ ⊢ A} → {u : Γ ⁏ Δ ⊢ B}
                        → fst (pair t u) ⋙ t

  beta∧₂⋙    : ∀ {A B} → {t : Γ ⁏ Δ ⊢ A} → {u : Γ ⁏ Δ ⊢ B}
                        → snd (pair t u) ⋙ u

  eta∧⋙      : ∀ {A B} → {t : Γ ⁏ Δ ⊢ A ∧ B}
                        → t ⋙ pair (fst t) (snd t)

  eta⊤⋙     : ∀ {t : Γ ⁏ Δ ⊢ ⊤} → t ⋙ unit


-- Examples from the Nanevski-Pfenning-Pientka paper.

module Examples where
  e₁ : ∀ {A C D Γ Δ}
        → Γ ⁏ Δ ⊢ [ ∅ , C ] A ▻
                    [ ∅ , C , D ] A
  e₁ = lam (unbox v₀ (box (mv₀ (∙ , var (pop top)))))

  e₂ : ∀ {A C Γ Δ}
        → Γ ⁏ Δ ⊢ [ ∅ , C , C ] A ▻
                    [ ∅ , C ] A
  e₂ = lam (unbox v₀ (box (mv₀ (refl⊢⋆ , var top))))

  e₃ : ∀ {A Γ Δ}
        → Γ ⁏ Δ ⊢ [ ∅ , A ] A
  e₃ = box v₀

  e₄ : ∀ {A B C Γ Δ}
        → Γ ⁏ Δ ⊢ [ ∅ , A ] B ▻
                    [ ∅ , A ] [ ∅ , B ] C ▻
                    [ ∅ , A ] C
  e₄ = lam (lam (unbox v₁ (unbox v₀ (box
         (unbox (mv₀ refl⊢⋆) (mv₀ (∙ , mv₂ refl⊢⋆)))))))

  e₅ : ∀ {A Γ Δ}
        → Γ ⁏ Δ ⊢ [ ∅ ] A ▻ A
  e₅ = lam (unbox v₀ (mv₀ ∙))

  e₆ : ∀ {A C D Γ Δ}
        → Γ ⁏ Δ ⊢ [ ∅ , C ] A ▻
                    [ ∅ , D ] [ ∅ , C ] A
  e₆ = lam (unbox v₀ (box (box (mv₀ refl⊢⋆))))

  e₇ : ∀ {A B C D Γ Δ}
        → Γ ⁏ Δ ⊢ [ ∅ , C ] (A ▻ B) ▻
                    [ ∅ , D ] A ▻
                    [ ∅ , C , D ] B
  e₇ = lam (lam (unbox v₁ (unbox v₀ (box
         (app (mv₁ (∙ , var (pop top))) (mv₀ (∙ , var top)))))))

  e₈ : ∀ {A B C Γ Δ}
        → Γ ⁏ Δ ⊢ [ ∅ , A ] (A ▻ B) ▻
                    [ ∅ , B ] C ▻
                    [ ∅ , A ] C
  e₈ = lam (lam (unbox v₁ (unbox v₀ (box
         (mv₀ (∙ , app (mv₁ refl⊢⋆) v₀))))))
