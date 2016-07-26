module BasicILP.Direct.Gentzen where

open import Common.Context public


-- Propositions of intuitionistic logic of proofs, without ∨, ⊥, or +.

mutual
  infixl 7 _∧_
  infixr 6 _⦂_
  infixr 5 _▷_
  data Ty : Set where
    α_  : Atom → Ty
    _▷_ : Ty → Ty → Ty
    _⦂_ : Box → Ty → Ty
    _∧_ : Ty → Ty → Ty
    ⊤  : Ty

  record Box : Set where
    inductive
    constructor [_]
    field
      {/A} : Ty
      t    : ⌀ ⊢ /A

  _⦂⋆_ : ∀ {n} → VCx Box n → VCx Ty n → Cx Ty
  ⌀        ⦂⋆ ⌀       = ⌀
  (ts , t) ⦂⋆ (Π , A) = (ts ⦂⋆ Π) , (t ⦂ A)


  -- Derivations, as Gentzen-style natural deduction trees.

  infix 3 _⊢_
  data _⊢_ (Γ : Cx Ty) : Ty → Set where
    var      : ∀ {A}              → A ∈ Γ → Γ ⊢ A
    lam      : ∀ {A B}            → Γ , A ⊢ B → Γ ⊢ A ▷ B
    app      : ∀ {A B}            → Γ ⊢ A ▷ B → Γ ⊢ A → Γ ⊢ B
--    multibox : ∀ {n A} {[ss] : VCx Box n} {Π : VCx Ty n}
--               → Γ ⊢⋆ [ss] ⦂⋆ Π → (u : [ss] ⦂⋆ Π ⊢ A)
--               → Γ ⊢ [ u ] ⦂ A
    down     : ∀ {A} {t : ⌀ ⊢ A} → Γ ⊢ [ t ] ⦂ A → Γ ⊢ A
    pair     : ∀ {A B}            → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
    fst      : ∀ {A B}            → Γ ⊢ A ∧ B → Γ ⊢ A
    snd      : ∀ {A B}            → Γ ⊢ A ∧ B → Γ ⊢ B
    tt       : Γ ⊢ ⊤

  infix 3 _⊢⋆_
  _⊢⋆_ : Cx Ty → Cx Ty → Set
  Γ ⊢⋆ ⌀     = Top
  Γ ⊢⋆ Π , A = Γ ⊢⋆ Π × Γ ⊢ A

infix 5 _⨝_
_⨝_ : Ty → Ty → Ty
A ⨝ B = (A ▷ B) ∧ (B ▷ A)


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ A → Γ′ ⊢ A
  mono⊢ η (var i)         = var (mono∈ η i)
  mono⊢ η (lam t)         = lam (mono⊢ (keep η) t)
  mono⊢ η (app t u)       = app (mono⊢ η t) (mono⊢ η u)
--  mono⊢ η (multibox ts u) = multibox (mono⊢⋆ η ts) u
  mono⊢ η (down t)        = down (mono⊢ η t)
  mono⊢ η (pair t u)      = pair (mono⊢ η t) (mono⊢ η u)
  mono⊢ η (fst t)         = fst (mono⊢ η t)
  mono⊢ η (snd t)         = snd (mono⊢ η t)
  mono⊢ η tt              = tt

  mono⊢⋆ : ∀ {Π Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⋆ Π → Γ′ ⊢⋆ Π
  mono⊢⋆ {⌀}     η ∙        = ∙
  mono⊢⋆ {Π , A} η (ts , t) = mono⊢⋆ η ts , mono⊢ η t


-- Shorthand for variables.

v₀ : ∀ {A Γ} → Γ , A ⊢ A
v₀ = var i₀

v₁ : ∀ {A B Γ} → (Γ , A) , B ⊢ A
v₁ = var i₁

v₂ : ∀ {A B C Γ} → ((Γ , A) , B) , C ⊢ A
v₂ = var i₂


-- Deduction theorem is built-in.

-- Detachment theorem.

det : ∀ {A B Γ} → Γ ⊢ A ▷ B → Γ , A ⊢ B
det t = app (mono⊢ weak⊆ t) v₀


-- Cut and multicut.

cut : ∀ {A B Γ} → Γ ⊢ A → ⌀ , A ⊢ B → Γ ⊢ B
cut t u = app (mono⊢ bot⊆ (lam u)) t

multicut⊢ : ∀ {Π A Γ} → Γ ⊢⋆ Π → Π ⊢ A → Γ ⊢ A
multicut⊢ {⌀}     ∙        u = mono⊢ bot⊆ u
multicut⊢ {Π , B} (ts , t) u = app (multicut⊢ ts (lam u)) t


-- Reflexivity and transitivity.

refl⊢⋆ : ∀ {Γ} → Γ ⊢⋆ Γ
refl⊢⋆ {⌀}     = ∙
refl⊢⋆ {Γ , A} = mono⊢⋆ weak⊆ refl⊢⋆ , v₀

trans⊢⋆ : ∀ {Π Γ Γ′} → Γ ⊢⋆ Γ′ → Γ′ ⊢⋆ Π → Γ ⊢⋆ Π
trans⊢⋆ {⌀}     ts ∙        = ∙
trans⊢⋆ {Π , A} ts (us , u) = trans⊢⋆ ts us , multicut⊢ ts u


-- Contraction.

ccont : ∀ {A B Γ} → Γ ⊢ (A ▷ A ▷ B) ▷ A ▷ B
ccont = lam (lam (app (app v₁ v₀) v₀))

cont : ∀ {A B Γ} → (Γ , A) , A ⊢ B → Γ , A ⊢ B
cont t = det (app ccont (lam (lam t)))


-- Exchange.

cexch : ∀ {A B C Γ} → Γ ⊢ (A ▷ B ▷ C) ▷ B ▷ A ▷ C
cexch = lam (lam (lam (app (app v₂ v₀) v₁)))

exch : ∀ {A B C Γ} → (Γ , A) , B ⊢ C → (Γ , B) , A ⊢ C
exch t = det (det (app cexch (lam (lam t))))


-- Composition.

ccomp : ∀ {A B C Γ} → Γ ⊢ (B ▷ C) ▷ (A ▷ B) ▷ A ▷ C
ccomp = lam (lam (lam (app v₂ (app v₁ v₀))))

comp : ∀ {A B C Γ} → Γ , B ⊢ C → Γ , A ⊢ B → Γ , A ⊢ C
comp t u = det (app (app ccomp (lam t)) (lam u))


-- Useful theorems in functional form.

-- dist : ∀ {A B Ξ Γ} {t : Ξ ⊢ A ▷ B} {u : Ξ ⊢ A}
--        → Γ ⊢ [ t ] ⦂ (A ▷ B) → Γ ⊢ [ u ] ⦂ A
--        → Γ ⊢ [ app (down v₁) (down v₀) ] ⦂ B
-- dist t u = multibox ((∙ , t) , u) (app (down v₁) (down v₀))
--
-- up : ∀ {A Ξ Γ} {t : Ξ ⊢ A}
--      → Γ ⊢ [ t ] ⦂ A
--      → Γ ⊢ [ v₀ ] ⦂ [ t ] ⦂ A
-- up t = multibox (∙ , t) v₀
--
-- distup : ∀ {A B Ξ Γ} {u : Ξ ⊢ A} {t : ⌀ , [ u ] ⦂ A ⊢ [ u ] ⦂ A ▷ B}
--          → Γ ⊢ [ t ] ⦂ ([ u ] ⦂ A ▷ B) → Γ ⊢ [ u ] ⦂ A
--          → Γ ⊢ [ app (down v₁) (down v₀) ] ⦂ B
-- distup t u = dist t (up u)
--
-- box : ∀ {A Γ}
--       → (t : ⌀ ⊢ A)
--       → Γ ⊢ [ t ] ⦂ A
-- box t = multibox ∙ t

unbox : ∀ {A C Γ} {t : ⌀ ⊢ A} {u : ⌀ ⊢ C}
        → Γ ⊢ [ t ] ⦂ A → Γ , [ t ] ⦂ A ⊢ [ u ] ⦂ C
        → Γ ⊢ [ u ] ⦂ C
unbox t u = app (lam u) t


-- Useful theorems in combinatory form.

ci : ∀ {A Γ} → Γ ⊢ A ▷ A
ci = lam v₀

ck : ∀ {A B Γ} → Γ ⊢ A ▷ B ▷ A
ck = lam (lam v₁)

cs : ∀ {A B C Γ} → Γ ⊢ (A ▷ B ▷ C) ▷ (A ▷ B) ▷ A ▷ C
cs = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))

-- cdist : ∀ {A B Ξ Γ} {t : Ξ ⊢ A ▷ B} {u : Ξ ⊢ A}
--         → Γ ⊢ [ t ] ⦂ (A ▷ B) ▷ [ u ] ⦂ A ▷ [ app (down v₁) (down v₀) ] ⦂ B
-- cdist = lam (lam (dist v₁ v₀))
--
-- cup : ∀ {A Ξ Γ} {t : Ξ ⊢ A} → Γ ⊢ [ t ] ⦂ A ▷ [ v₀ ] ⦂ [ t ] ⦂ A
-- cup = lam (up v₀)

cdown : ∀ {A Γ} {t : ⌀ ⊢ A} → Γ ⊢ [ t ] ⦂ A ▷ A
cdown = lam (down v₀)

-- cdistup : ∀ {A B Ξ Γ} {u : Ξ ⊢ A} {t : ⌀ , [ u ] ⦂ A ⊢ [ u ] ⦂ A ▷ B}
--           → Γ ⊢ [ t ] ⦂ ([ u ] ⦂ A ▷ B) ▷ [ u ] ⦂ A ▷ [ app (down v₁) (down v₀) ] ⦂ B
-- cdistup = lam (lam (dist v₁ (up v₀)))

cunbox : ∀ {A C Γ} {t : ⌀ ⊢ A} {u : ⌀ ⊢ C}
         → Γ ⊢ [ t ] ⦂ A ▷ ([ t ] ⦂ A ▷ C) ▷ C
cunbox = lam (lam (app v₀ v₁))

cpair : ∀ {A B Γ} → Γ ⊢ A ▷ B ▷ A ∧ B
cpair = lam (lam (pair v₁ v₀))

cfst : ∀ {A B Γ} → Γ ⊢ A ∧ B ▷ A
cfst = lam (fst v₀)

csnd : ∀ {A B Γ} → Γ ⊢ A ∧ B ▷ B
csnd = lam (snd v₀)


-- Closure under context concatenation.

concat : ∀ {A B Γ} Γ′ → Γ , A ⊢ B → Γ′ ⊢ A → Γ ⧺ Γ′ ⊢ B
concat Γ′ t u = app (mono⊢ (weak⊆⧺ₗ Γ′) (lam t)) (mono⊢ weak⊆⧺ᵣ u)


-- Substitution.

mutual
  [_≔_]_ : ∀ {A B Γ} → (i : A ∈ Γ) → Γ - i ⊢ A → Γ ⊢ B → Γ - i ⊢ B
  [ i ≔ s ] var j         with i ≟∈ j
  [ i ≔ s ] var .i        | same   = s
  [ i ≔ s ] var ._        | diff j = var j
  [ i ≔ s ] lam t         = lam ([ pop i ≔ mono⊢ weak⊆ s ] t)
  [ i ≔ s ] app t u       = app ([ i ≔ s ] t) ([ i ≔ s ] u)
--  [ i ≔ s ] multibox ts u = multibox ([ i ≔ s ]⋆ ts) u
  [ i ≔ s ] down t        = down ([ i ≔ s ] t)
  [ i ≔ s ] pair t u      = pair ([ i ≔ s ] t) ([ i ≔ s ] u)
  [ i ≔ s ] fst t         = fst ([ i ≔ s ] t)
  [ i ≔ s ] snd t         = snd ([ i ≔ s ] t)
  [ i ≔ s ] tt            = tt

  [_≔_]⋆_ : ∀ {Π A Γ} → (i : A ∈ Γ) → Γ - i ⊢ A → Γ ⊢⋆ Π → Γ - i ⊢⋆ Π
  [_≔_]⋆_ {⌀}     i s ∙        = ∙
  [_≔_]⋆_ {Π , B} i s (ts , t) = [ i ≔ s ]⋆ ts , [ i ≔ s ] t
