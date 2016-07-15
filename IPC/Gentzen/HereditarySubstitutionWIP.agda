module IPC.Gentzen.HereditarySubstitutionWIP where

open import IPC.Gentzen.Core public


-- Outermost propositions for neutrals.

data Tyⁿᵉ : Ty → Set where
  ᴬ_  : (P : Atom) → Tyⁿᵉ (ᴬ P)
  _∨_ : (A B : Ty) → Tyⁿᵉ (A ∨ B)
  ⫫  : Tyⁿᵉ ⫫


-- Derivations, as Gentzen-style natural deduction trees.

mutual
  -- Normal forms, or introductions.
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ (Γ : Cx Ty) : Ty → Set where
    neⁿᶠ   : ∀ {A}   → Γ ⊢ⁿᵉ A → {{_ : Tyⁿᵉ A}} → Γ ⊢ⁿᶠ A
    lamⁿᶠ  : ∀ {A B} → Γ , A ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ▷ B
    unitⁿᶠ : Γ ⊢ⁿᶠ ⫪
    pairⁿᶠ : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∧ B
    inlⁿᶠ  : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ A ∨ B
    inrⁿᶠ  : ∀ {A B} → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∨ B

  -- Neutrals, or eliminations.
  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ (Γ : Cx Ty) : Ty → Set where
    spⁿᵉ : ∀ {A B C} → A ∈ Γ → Γ ⊢ˢᵖ A ⦙ B → Γ ⊢ˢᵖ′ B ⦙ C → Γ ⊢ⁿᵉ C

  -- Spines.
  infix 3 _⊢ˢᵖ_⦙_
  data _⊢ˢᵖ_⦙_ (Γ : Cx Ty) : Ty → Ty → Set where
    nilˢᵖ : ∀ {C}     → Γ ⊢ˢᵖ C ⦙ C
    appˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ B ⦙ C → Γ ⊢ⁿᶠ A → Γ ⊢ˢᵖ A ▷ B ⦙ C
    fstˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ A ⦙ C → Γ ⊢ˢᵖ A ∧ B ⦙ C
    sndˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ B ⦙ C → Γ ⊢ˢᵖ A ∧ B ⦙ C

  -- Falsehood elimination, optional.
  infix 3 _⊢ˢᵖ′_⦙_
  data _⊢ˢᵖ′_⦙_ (Γ : Cx Ty) : Ty → Ty → Set where
    nothingˢᵖ′ : ∀ {C}     → Γ ⊢ˢᵖ′ C ⦙ C
    caseˢᵖ′    : ∀ {A B C} → Γ , A ⊢ⁿᶠ C → Γ , B ⊢ⁿᶠ C → Γ ⊢ˢᵖ′ A ∨ B ⦙ C


-- Translation to simple terms.

mutual
  nf→tm : ∀ {A Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm unitⁿᶠ       = unit
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)
  nf→tm (inlⁿᶠ t)    = inl (nf→tm t)
  nf→tm (inrⁿᶠ t)    = inr (nf→tm t)

  ne→tm : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ A
  ne→tm (spⁿᵉ i xs ys) = sp→tm′ (var i) xs ys

  sp→tm : ∀ {A C Γ} → Γ ⊢ A → Γ ⊢ˢᵖ A ⦙ C → Γ ⊢ C
  sp→tm t nilˢᵖ        = t
  sp→tm t (appˢᵖ xs u) = sp→tm (app t (nf→tm u)) xs
  sp→tm t (fstˢᵖ xs)   = sp→tm (fst t) xs
  sp→tm t (sndˢᵖ xs)   = sp→tm (snd t) xs

  sp→tm′ : ∀ {A B C Γ} → Γ ⊢ A → Γ ⊢ˢᵖ A ⦙ B → Γ ⊢ˢᵖ′ B ⦙ C → Γ ⊢ C
  sp→tm′ t xs nothingˢᵖ′    = sp→tm t xs
  sp→tm′ t xs (caseˢᵖ′ u v) = case (sp→tm t xs) (nf→tm u) (nf→tm v)


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ⁿᶠ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᶠ A → Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ η (neⁿᶠ t)     = neⁿᶠ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᶠ η (lamⁿᶠ t)    = lamⁿᶠ (mono⊢ⁿᶠ (keep η) t)
  mono⊢ⁿᶠ η unitⁿᶠ       = unitⁿᶠ
  mono⊢ⁿᶠ η (pairⁿᶠ t u) = pairⁿᶠ (mono⊢ⁿᶠ η t) (mono⊢ⁿᶠ η u)
  mono⊢ⁿᶠ η (inlⁿᶠ t)    = inlⁿᶠ (mono⊢ⁿᶠ η t)
  mono⊢ⁿᶠ η (inrⁿᶠ t)    = inrⁿᶠ (mono⊢ⁿᶠ η t)

  mono⊢ⁿᵉ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᵉ A → Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ η (spⁿᵉ i xs ys) = spⁿᵉ (mono∈ η i) (mono⊢ˢᵖ η xs) (mono⊢ˢᵖ′ η ys)

  mono⊢ˢᵖ : ∀ {A C Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ˢᵖ A ⦙ C → Γ′ ⊢ˢᵖ A ⦙ C
  mono⊢ˢᵖ η nilˢᵖ        = nilˢᵖ
  mono⊢ˢᵖ η (appˢᵖ xs u) = appˢᵖ (mono⊢ˢᵖ η xs) (mono⊢ⁿᶠ η u)
  mono⊢ˢᵖ η (fstˢᵖ xs)   = fstˢᵖ (mono⊢ˢᵖ η xs)
  mono⊢ˢᵖ η (sndˢᵖ xs)   = sndˢᵖ (mono⊢ˢᵖ η xs)

  mono⊢ˢᵖ′ : ∀ {A C Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ˢᵖ′ A ⦙ C → Γ′ ⊢ˢᵖ′ A ⦙ C
  mono⊢ˢᵖ′ η nothingˢᵖ′    = nothingˢᵖ′
  mono⊢ˢᵖ′ η (caseˢᵖ′ u v) = caseˢᵖ′ (mono⊢ⁿᶠ (keep η) u) (mono⊢ⁿᶠ (keep η) v)


-- Hereditary substitution and reduction.

mutual
  [_≔_]ⁿᶠ_ : ∀ {A B Γ} → (i : A ∈ Γ) → Γ - i ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ - i ⊢ⁿᶠ B
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ j  xs ys) with i ≟∈ j
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ .i xs ys) | same   = reduce s ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ˢᵖ′ ys)
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ ._ xs ys) | diff j = neⁿᶠ (spⁿᵉ j ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ˢᵖ′ ys))
  [ i ≔ s ]ⁿᶠ lamⁿᶠ t              = lamⁿᶠ ([ pop i ≔ mono⊢ⁿᶠ weak⊆ s ]ⁿᶠ t)
  [ i ≔ s ]ⁿᶠ unitⁿᶠ               = unitⁿᶠ
  [ i ≔ s ]ⁿᶠ pairⁿᶠ t u           = pairⁿᶠ ([ i ≔ s ]ⁿᶠ t) ([ i ≔ s ]ⁿᶠ u)
  [ i ≔ s ]ⁿᶠ inlⁿᶠ t              = inlⁿᶠ ([ i ≔ s ]ⁿᶠ t)
  [ i ≔ s ]ⁿᶠ inrⁿᶠ t              = inrⁿᶠ ([ i ≔ s ]ⁿᶠ t)

  [_≔_]ˢᵖ_ : ∀ {A B C Γ} → (i : A ∈ Γ) → Γ - i ⊢ⁿᶠ A → Γ ⊢ˢᵖ B ⦙ C → Γ - i ⊢ˢᵖ B ⦙ C
  [ i ≔ s ]ˢᵖ nilˢᵖ      = nilˢᵖ
  [ i ≔ s ]ˢᵖ appˢᵖ xs u = appˢᵖ ([ i ≔ s ]ˢᵖ xs) ([ i ≔ s ]ⁿᶠ u)
  [ i ≔ s ]ˢᵖ fstˢᵖ xs   = fstˢᵖ ([ i ≔ s ]ˢᵖ xs)
  [ i ≔ s ]ˢᵖ sndˢᵖ xs   = sndˢᵖ ([ i ≔ s ]ˢᵖ xs)

  [_≔_]ˢᵖ′_ : ∀ {A B C Γ} → (i : A ∈ Γ) → Γ - i ⊢ⁿᶠ A → Γ ⊢ˢᵖ′ B ⦙ C → Γ - i ⊢ˢᵖ′ B ⦙ C
  [ i ≔ s ]ˢᵖ′ nothingˢᵖ′  = nothingˢᵖ′
  [ i ≔ s ]ˢᵖ′ caseˢᵖ′ u v = caseˢᵖ′ ([ pop i ≔ mono⊢ⁿᶠ weak⊆ s ]ⁿᶠ u)
                                     ([ pop i ≔ mono⊢ⁿᶠ weak⊆ s ]ⁿᶠ v)

  reduce : ∀ {A B C Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ˢᵖ A ⦙ B → Γ ⊢ˢᵖ′ B ⦙ C → {{_ : Tyⁿᵉ C}} → Γ ⊢ⁿᶠ C
  reduce t                                nilˢᵖ        nothingˢᵖ′    = t
  reduce (inlⁿᶠ t)                        nilˢᵖ        (caseˢᵖ′ u v) = [ top ≔ t ]ⁿᶠ u
  reduce (inrⁿᶠ t)                        nilˢᵖ        (caseˢᵖ′ u v) = [ top ≔ t ]ⁿᶠ v
  reduce (neⁿᶠ (spⁿᵉ i xs nothingˢᵖ′))    nilˢᵖ        ys            = neⁿᶠ (spⁿᵉ i xs ys)
  reduce (neⁿᶠ (spⁿᵉ i xs (caseˢᵖ′ u v))) nilˢᵖ        ys            = neⁿᶠ (spⁿᵉ i xs (caseˢᵖ′ u′ v′))
    where u′ = reduce u nilˢᵖ (mono⊢ˢᵖ′ weak⊆ ys)
          v′ = reduce v nilˢᵖ (mono⊢ˢᵖ′ weak⊆ ys)
  reduce (neⁿᶠ t {{()}})                  (appˢᵖ xs u) ys
  reduce (neⁿᶠ t {{()}})                  (fstˢᵖ xs)   ys
  reduce (neⁿᶠ t {{()}})                  (sndˢᵖ xs)   ys
  reduce (lamⁿᶠ t)                        (appˢᵖ xs u) ys            = reduce ([ top ≔ u ]ⁿᶠ t) xs ys
  reduce (pairⁿᶠ t u)                     (fstˢᵖ xs)   ys            = reduce t xs ys
  reduce (pairⁿᶠ t u)                     (sndˢᵖ xs)   ys            = reduce u xs ys


-- Reduction-based normal forms.

appⁿᶠ : ∀ {A B Γ} → Γ ⊢ⁿᶠ A ▷ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B
appⁿᶠ (neⁿᶠ t {{()}})
appⁿᶠ (lamⁿᶠ t) u = [ top ≔ u ]ⁿᶠ t

fstⁿᶠ : ∀ {A B Γ} → Γ ⊢ⁿᶠ A ∧ B → Γ ⊢ⁿᶠ A
fstⁿᶠ (neⁿᶠ t {{()}})
fstⁿᶠ (pairⁿᶠ t u) = t

sndⁿᶠ : ∀ {A B Γ} → Γ ⊢ⁿᶠ A ∧ B → Γ ⊢ⁿᶠ B
sndⁿᶠ (neⁿᶠ t {{()}})
sndⁿᶠ (pairⁿᶠ t u) = u


-- Useful equipment for deriving neutrals.

≪app : ∀ {A B C Γ} → Γ ⊢ˢᵖ C ⦙ A ▷ B → Γ ⊢ⁿᶠ A → Γ ⊢ˢᵖ C ⦙ B
≪app nilˢᵖ        t = appˢᵖ nilˢᵖ t
≪app (appˢᵖ xs u) t = appˢᵖ (≪app xs t) u
≪app (fstˢᵖ xs)   t = fstˢᵖ (≪app xs t)
≪app (sndˢᵖ xs)   t = sndˢᵖ (≪app xs t)

≪fst : ∀ {A B C Γ} → Γ ⊢ˢᵖ C ⦙ A ∧ B → Γ ⊢ˢᵖ C ⦙ A
≪fst nilˢᵖ        = fstˢᵖ nilˢᵖ
≪fst (appˢᵖ xs u) = appˢᵖ (≪fst xs) u
≪fst (fstˢᵖ xs)   = fstˢᵖ (≪fst xs)
≪fst (sndˢᵖ xs)   = sndˢᵖ (≪fst xs)

≪snd : ∀ {A B C Γ} → Γ ⊢ˢᵖ C ⦙ A ∧ B → Γ ⊢ˢᵖ C ⦙ B
≪snd nilˢᵖ        = sndˢᵖ nilˢᵖ
≪snd (appˢᵖ xs u) = appˢᵖ (≪snd xs) u
≪snd (fstˢᵖ xs)   = fstˢᵖ (≪snd xs)
≪snd (sndˢᵖ xs)   = sndˢᵖ (≪snd xs)


-- Derived neutrals.

varⁿᵉ : ∀ {A Γ} → A ∈ Γ → Γ ⊢ⁿᵉ A
varⁿᵉ i = spⁿᵉ i nilˢᵖ nothingˢᵖ′

appⁿᵉ : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ▷ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᵉ B
appⁿᵉ (spⁿᵉ i xs nothingˢᵖ′)    t = spⁿᵉ i (≪app xs t) nothingˢᵖ′
appⁿᵉ (spⁿᵉ i xs (caseˢᵖ′ u v)) t = spⁿᵉ i xs (caseˢᵖ′ (appⁿᶠ u (mono⊢ⁿᶠ weak⊆ t))
                                                       (appⁿᶠ v (mono⊢ⁿᶠ weak⊆ t)))

fstⁿᵉ : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ A
fstⁿᵉ (spⁿᵉ i xs nothingˢᵖ′)    = spⁿᵉ i (≪fst xs) nothingˢᵖ′
fstⁿᵉ (spⁿᵉ i xs (caseˢᵖ′ u v)) = spⁿᵉ i xs (caseˢᵖ′ (fstⁿᶠ u) (fstⁿᶠ v))

sndⁿᵉ : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ B
sndⁿᵉ (spⁿᵉ i xs nothingˢᵖ′)    = spⁿᵉ i (≪snd xs) nothingˢᵖ′
sndⁿᵉ (spⁿᵉ i xs (caseˢᵖ′ u v)) = spⁿᵉ i xs (caseˢᵖ′ (sndⁿᶠ u) (sndⁿᶠ v))


-- Iterated expansion.

expand : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ⁿᶠ A
expand {ᴬ P}   t = neⁿᶠ t {{ᴬ P}}
expand {A ▷ B} t = lamⁿᶠ (expand (appⁿᵉ (mono⊢ⁿᵉ weak⊆ t) (expand (varⁿᵉ top))))
expand {⫪}    t = unitⁿᶠ
expand {A ∧ B} t = pairⁿᶠ (expand (fstⁿᵉ t)) (expand (sndⁿᵉ t))
expand {A ∨ B} t = neⁿᶠ t {{A ∨ B}}
expand {⫫}    t = neⁿᶠ t {{⫫}}


-- Expansion-based normal forms.

varⁿᶠ : ∀ {A Γ} → A ∈ Γ → Γ ⊢ⁿᶠ A
varⁿᶠ i = expand (varⁿᵉ i)

mutual
  caseⁿᶠ : ∀ {A B C Γ} → Γ ⊢ⁿᶠ A ∨ B → Γ , A ⊢ⁿᶠ C → Γ , B ⊢ⁿᶠ C → Γ ⊢ⁿᶠ C
  caseⁿᶠ (neⁿᶠ t)  u v = expand (caseⁿᵉ t u v)
  caseⁿᶠ (inlⁿᶠ t) u v = [ top ≔ t ]ⁿᶠ u
  caseⁿᶠ (inrⁿᶠ t) u v = [ top ≔ t ]ⁿᶠ v

  caseⁿᵉ : ∀ {A B C Γ} → Γ ⊢ⁿᵉ A ∨ B → Γ , A ⊢ⁿᶠ C → Γ , B ⊢ⁿᶠ C → Γ ⊢ⁿᵉ C
  caseⁿᵉ (spⁿᵉ i xs nothingˢᵖ′)      u v = spⁿᵉ i xs (caseˢᵖ′ u v)
  caseⁿᵉ (spⁿᵉ i xs (caseˢᵖ′ t₁ t₂)) u v = spⁿᵉ i xs (caseˢᵖ′ u′ v′)
    where u′ = caseⁿᶠ t₁ (mono⊢ⁿᶠ (keep weak⊆) u) (mono⊢ⁿᶠ (keep weak⊆) v)
          v′ = caseⁿᶠ t₂ (mono⊢ⁿᶠ (keep weak⊆) u) (mono⊢ⁿᶠ (keep weak⊆) v)

boomⁿᶠ : ∀ {C Γ} → Γ ⊢ⁿᶠ ⫫ → Γ ⊢ⁿᶠ C
boomⁿᶠ t = reduce t nilˢᵖ {!!}


-- Translation from terms to normal forms.

tm→nf : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ⁿᶠ A
tm→nf (var i)      = varⁿᶠ i
tm→nf (lam t)      = lamⁿᶠ (tm→nf t)
tm→nf (app t u)    = appⁿᶠ (tm→nf t) (tm→nf u)
tm→nf unit         = unitⁿᶠ
tm→nf (pair t u)   = pairⁿᶠ (tm→nf t) (tm→nf u)
tm→nf (fst t)      = fstⁿᶠ (tm→nf t)
tm→nf (snd t)      = sndⁿᶠ (tm→nf t)
tm→nf (inl t)      = inlⁿᶠ (tm→nf t)
tm→nf (inr t)      = inrⁿᶠ (tm→nf t)
tm→nf (case t u v) = caseⁿᶠ (tm→nf t) (tm→nf u) (tm→nf v)
tm→nf (boom t)     = boomⁿᶠ (tm→nf t)


-- Normalisation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = nf→tm ∘ tm→nf


-- TODO: Correctness with respect to conversion.

-- coco : ∀ {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → norm t ≡ norm t′
-- coco refl⇒             = refl
-- coco (trans⇒ p q)      = trans (coco p) (coco q)
-- coco (sym⇒ p)          = sym (coco p)
-- coco (cong⇒lam p)      = cong lam (coco p)
-- coco (cong⇒app p q)    = cong₂ {!!} (coco p) (coco q)
-- coco (cong⇒pair p q)   = cong₂ pair (coco p) (coco q)
-- coco (cong⇒fst p)      = cong {!!} (coco p)
-- coco (cong⇒snd p)      = cong {!!} (coco p)
-- coco (cong⇒inl p)      = cong inl (coco p)
-- coco (cong⇒inr p)      = cong inr (coco p)
-- coco (cong⇒case p q r) = cong₃ {!!} (coco p) (coco q) (coco r)
-- coco (cong⇒boom p)     = cong {!!} (coco p)
-- coco conv⇒lam          = {!!}
-- coco conv⇒app          = {!!}
-- coco conv⇒unit         = {!!}
-- coco conv⇒pair         = {!!}
-- coco conv⇒fst          = refl
-- coco conv⇒snd          = refl
