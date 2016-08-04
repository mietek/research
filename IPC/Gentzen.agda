module IPC.Gentzen where

open import IPC public


-- Derivations, as Gentzen-style natural deduction trees.

infix 3 _⊢_
data _⊢_ (Γ : Cx Ty) : Ty → Set where
  var  : ∀ {A}     → A ∈ Γ → Γ ⊢ A
  lam  : ∀ {A B}   → Γ , A ⊢ B → Γ ⊢ A ▻ B
  app  : ∀ {A B}   → Γ ⊢ A ▻ B → Γ ⊢ A → Γ ⊢ B
  pair : ∀ {A B}   → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
  fst  : ∀ {A B}   → Γ ⊢ A ∧ B → Γ ⊢ A
  snd  : ∀ {A B}   → Γ ⊢ A ∧ B → Γ ⊢ B
  tt   : Γ ⊢ ⊤
  boom : ∀ {C}     → Γ ⊢ ⊥ → Γ ⊢ C
  inl  : ∀ {A B}   → Γ ⊢ A → Γ ⊢ A ∨ B
  inr  : ∀ {A B}   → Γ ⊢ B → Γ ⊢ A ∨ B
  case : ∀ {A B C} → Γ ⊢ A ∨ B → Γ , A ⊢ C → Γ , B ⊢ C → Γ ⊢ C

infix 3 _⊢⋆_
_⊢⋆_ : Cx Ty → Cx Ty → Set
Γ ⊢⋆ ⌀     = 𝟙
Γ ⊢⋆ Π , A = Γ ⊢⋆ Π × Γ ⊢ A


-- Monotonicity with respect to context inclusion.

mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
mono⊢ η (var i)      = var (mono∈ η i)
mono⊢ η (lam t)      = lam (mono⊢ (keep η) t)
mono⊢ η (app t u)    = app (mono⊢ η t) (mono⊢ η u)
mono⊢ η (pair t u)   = pair (mono⊢ η t) (mono⊢ η u)
mono⊢ η (fst t)      = fst (mono⊢ η t)
mono⊢ η (snd t)      = snd (mono⊢ η t)
mono⊢ η tt           = tt
mono⊢ η (boom t)     = boom (mono⊢ η t)
mono⊢ η (inl t)      = inl (mono⊢ η t)
mono⊢ η (inr t)      = inr (mono⊢ η t)
mono⊢ η (case t u v) = case (mono⊢ η t) (mono⊢ (keep η) u) (mono⊢ (keep η) v)

mono⊢⋆ : ∀ {Γ″ Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⋆ Γ″ → Γ′ ⊢⋆ Γ″
mono⊢⋆ {⌀}      η ∙        = ∙
mono⊢⋆ {Γ″ , A} η (ts , t) = mono⊢⋆ η ts , mono⊢ η t


-- Shorthand for variables.

v₀ : ∀ {A Γ} → Γ , A ⊢ A
v₀ = var i₀

v₁ : ∀ {A B Γ} → (Γ , A) , B ⊢ A
v₁ = var i₁

v₂ : ∀ {A B C Γ} → ((Γ , A) , B) , C ⊢ A
v₂ = var i₂


-- Deduction theorem is built-in.

-- Detachment theorem.

det : ∀ {A B Γ} → Γ ⊢ A ▻ B → Γ , A ⊢ B
det t = app (mono⊢ weak⊆ t) v₀


-- Cut and multicut.

cut : ∀ {A B Γ} → Γ ⊢ A → ⌀ , A ⊢ B → Γ ⊢ B
cut t u = app (mono⊢ bot⊆ (lam u)) t

multicut : ∀ {Π A Γ} → Γ ⊢⋆ Π → Π ⊢ A → Γ ⊢ A
multicut {⌀}     ∙        u = mono⊢ bot⊆ u
multicut {Π , B} (ts , t) u = app (multicut ts (lam u)) t


-- Reflexivity and transitivity.

refl⊢⋆ : ∀ {Γ} → Γ ⊢⋆ Γ
refl⊢⋆ {⌀}     = ∙
refl⊢⋆ {Γ , A} = mono⊢⋆ weak⊆ refl⊢⋆ , v₀

trans⊢⋆ : ∀ {Γ″ Γ′ Γ} → Γ ⊢⋆ Γ′ → Γ′ ⊢⋆ Γ″ → Γ ⊢⋆ Γ″
trans⊢⋆ {⌀}      ts ∙        = ∙
trans⊢⋆ {Γ″ , A} ts (us , u) = trans⊢⋆ ts us , multicut ts u


-- Contraction.

ccont : ∀ {A B Γ} → Γ ⊢ (A ▻ A ▻ B) ▻ A ▻ B
ccont = lam (lam (app (app v₁ v₀) v₀))

cont : ∀ {A B Γ} → (Γ , A) , A ⊢ B → Γ , A ⊢ B
cont t = det (app ccont (lam (lam t)))


-- Exchange.

cexch : ∀ {A B C Γ} → Γ ⊢ (A ▻ B ▻ C) ▻ B ▻ A ▻ C
cexch = lam (lam (lam (app (app v₂ v₀) v₁)))

exch : ∀ {A B C Γ} → (Γ , A) , B ⊢ C → (Γ , B) , A ⊢ C
exch t = det (det (app cexch (lam (lam t))))


-- Composition.

ccomp : ∀ {A B C Γ} → Γ ⊢ (B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
ccomp = lam (lam (lam (app v₂ (app v₁ v₀))))

comp : ∀ {A B C Γ} → Γ , B ⊢ C → Γ , A ⊢ B → Γ , A ⊢ C
comp t u = det (app (app ccomp (lam t)) (lam u))


-- Useful theorems in combinatory form.

ci : ∀ {A Γ} → Γ ⊢ A ▻ A
ci = lam v₀

ck : ∀ {A B Γ} → Γ ⊢ A ▻ B ▻ A
ck = lam (lam v₁)

cs : ∀ {A B C Γ} → Γ ⊢ (A ▻ B ▻ C) ▻ (A ▻ B) ▻ A ▻ C
cs = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))

cpair : ∀ {A B Γ} → Γ ⊢ A ▻ B ▻ A ∧ B
cpair = lam (lam (pair v₁ v₀))

cfst : ∀ {A B Γ} → Γ ⊢ A ∧ B ▻ A
cfst = lam (fst v₀)

csnd : ∀ {A B Γ} → Γ ⊢ A ∧ B ▻ B
csnd = lam (snd v₀)

cboom : ∀ {C Γ} → Γ ⊢ ⊥ ▻ C
cboom = lam (boom v₀)

cinl : ∀ {A B Γ} → Γ ⊢ A ▻ A ∨ B
cinl = lam (inl v₀)

cinr : ∀ {A B Γ} → Γ ⊢ B ▻ A ∨ B
cinr = lam (inr v₀)

ccase : ∀ {A B C Γ} → Γ ⊢ A ∨ B ▻ (A ▻ C) ▻ (B ▻ C) ▻ C
ccase = lam (lam (lam (case v₂ (det v₁) (det v₀))))


-- Closure under context concatenation.

concat : ∀ {A B Γ} Γ′ → Γ , A ⊢ B → Γ′ ⊢ A → Γ ⧺ Γ′ ⊢ B
concat Γ′ t u = app (mono⊢ (weak⊆⧺ₗ Γ′) (lam t)) (mono⊢ weak⊆⧺ᵣ u)


-- Substitution.

[_≔_]_ : ∀ {A B Γ} → (i : A ∈ Γ) → Γ - i ⊢ A → Γ ⊢ B → Γ - i ⊢ B
[ i ≔ s ] var j      with i ≟∈ j
[ i ≔ s ] var .i     | same   = s
[ i ≔ s ] var ._     | diff j = var j
[ i ≔ s ] lam t      = lam ([ pop i ≔ mono⊢ weak⊆ s ] t)
[ i ≔ s ] app t u    = app ([ i ≔ s ] t) ([ i ≔ s ] u)
[ i ≔ s ] pair t u   = pair ([ i ≔ s ] t) ([ i ≔ s ] u)
[ i ≔ s ] fst t      = fst ([ i ≔ s ] t)
[ i ≔ s ] snd t      = snd ([ i ≔ s ] t)
[ i ≔ s ] tt         = tt
[ i ≔ s ] boom t     = boom ([ i ≔ s ] t)
[ i ≔ s ] inl t      = inl ([ i ≔ s ] t)
[ i ≔ s ] inr t      = inr ([ i ≔ s ] t)
[ i ≔ s ] case t u v = case ([ i ≔ s ] t) ([ pop i ≔ mono⊢ weak⊆ s ] u) ([ pop i ≔ mono⊢ weak⊆ s ] v)

[_≔_]⋆_ : ∀ {Π A Γ} → (i : A ∈ Γ) → Γ - i ⊢ A → Γ ⊢⋆ Π → Γ - i ⊢⋆ Π
[_≔_]⋆_ {⌀}     i s ∙        = ∙
[_≔_]⋆_ {Π , B} i s (ts , t) = [ i ≔ s ]⋆ ts , [ i ≔ s ] t


-- TODO: Conversion.

data _⇒_ : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A → Set where
  refl⇒     : ∀ {A Γ} {t : Γ ⊢ A}
               → t ⇒ t
  trans⇒    : ∀ {A Γ} {t t′ t″ : Γ ⊢ A}
               → t ⇒ t′ → t′ ⇒ t″ → t ⇒ t″
  sym⇒      : ∀ {A Γ} {t t′ : Γ ⊢ A}
               → t ⇒ t′ → t′ ⇒ t
  cong⇒lam  : ∀ {A B Γ} {t t′ : Γ , A ⊢ B}
               → t ⇒ t′ → lam t ⇒ lam t′
  cong⇒app  : ∀ {A B Γ} {t t′ : Γ ⊢ A ▻ B} {u u′ : Γ ⊢ A}
               → t ⇒ t′ → u ⇒ u′ → app t u ⇒ app t′ u′
  cong⇒pair : ∀ {A B Γ} {t t′ : Γ ⊢ A} {u u′ : Γ ⊢ B}
               → t ⇒ t′ → u ⇒ u′ → pair t u ⇒ pair t′ u′
  cong⇒fst  : ∀ {A B Γ} {t t′ : Γ ⊢ A ∧ B}
               → t ⇒ t′ → fst t ⇒ fst t′
  cong⇒snd  : ∀ {A B Γ} {t t′ : Γ ⊢ A ∧ B}
               → t ⇒ t′ → snd t ⇒ snd t′
  cong⇒inl  : ∀ {A B Γ} {t t′ : Γ ⊢ A}
               → t ⇒ t′ → inl {B = B} t ⇒ inl t′
  cong⇒inr  : ∀ {A B Γ} {t t′ : Γ ⊢ B}
               → t ⇒ t′ → inr {A = A} t ⇒ inr t′
  cong⇒boom : ∀ {C Γ} {t t′ : Γ ⊢ ⊥}
               → t ⇒ t′ → boom {C = C} t ⇒ boom t′
  cong⇒case : ∀ {A B C Γ} {t t′ : Γ ⊢ A ∨ B} {u u′ : Γ , A ⊢ C} {v v′ : Γ , B ⊢ C}
               → t ⇒ t′ → u ⇒ u′ → v ⇒ v′ → case t u v ⇒ case t′ u′ v′
  conv⇒lam  : ∀ {A B Γ} {t : Γ ⊢ A ▻ B}
               → t ⇒ lam (app (mono⊢ weak⊆ t) (var top))
  conv⇒app  : ∀ {A B Γ} {t : Γ , A ⊢ B} {u : Γ ⊢ A}
               → app (lam t) u ⇒ ([ top ≔ u ] t)
  conv⇒pair : ∀ {A B Γ} {t : Γ ⊢ A ∧ B}
               → t ⇒ pair (fst t) (snd t)
  conv⇒fst  : ∀ {A B Γ} {t : Γ ⊢ A} {u : Γ ⊢ B}
               → fst (pair t u) ⇒ t
  conv⇒snd  : ∀ {A B Γ} {t : Γ ⊢ A} {u : Γ ⊢ B}
               → snd (pair t u) ⇒ u
  conv⇒tt : ∀ {Γ} {t : Γ ⊢ ⊤}
               → t ⇒ tt
