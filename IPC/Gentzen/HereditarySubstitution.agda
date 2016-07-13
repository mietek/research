module IPC.Gentzen.HereditarySubstitution where

open import IPC.Gentzen.Core public


-- Normal forms, neutrals, and spines.

mutual
  infix 1 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ (Γ : Cx Ty) : Ty → Set where
    neⁿᶠ   : ∀ {p}   → Γ ⊢ⁿᵉ α p → Γ ⊢ⁿᶠ α p
    lamⁿᶠ  : ∀ {A B} → Γ , A ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ⊃ B
    unitⁿᶠ : Γ ⊢ⁿᶠ ι
    pairⁿᶠ : ∀ {A B} → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ ⊢ⁿᶠ A ∧ B

  infix 1 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ (Γ : Cx Ty) : Ty → Set where
    spⁿᵉ : ∀ {A C} → Γ ⊢ˢᵖ A ∣ C → A ∈ Γ → Γ ⊢ⁿᵉ C

  infix 1 _⊢ˢᵖ_∣_
  data _⊢ˢᵖ_∣_ (Γ : Cx Ty) : Ty → Ty → Set where
    endˢᵖ : ∀ {C}     → Γ ⊢ˢᵖ C ∣ C
    appˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ B ∣ C → Γ ⊢ⁿᶠ A → Γ ⊢ˢᵖ A ⊃ B ∣ C
    fstˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ A ∣ C → Γ ⊢ˢᵖ A ∧ B ∣ C
    sndˢᵖ : ∀ {A B C} → Γ ⊢ˢᵖ B ∣ C → Γ ⊢ˢᵖ A ∧ B ∣ C


-- Translation to terms.

mutual
  nf→tm : ∀ {A Γ} → Γ ⊢ⁿᶠ A → Γ ⊢ A
  nf→tm (neⁿᶠ t)     = ne→tm t
  nf→tm (lamⁿᶠ t)    = lam (nf→tm t)
  nf→tm unitⁿᶠ       = unit
  nf→tm (pairⁿᶠ t u) = pair (nf→tm t) (nf→tm u)

  ne→tm : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ A
  ne→tm (spⁿᵉ ss i) = sp→tm ss (var i)

  sp→tm : ∀ {A C Γ} → Γ ⊢ˢᵖ A ∣ C → Γ ⊢ A → Γ ⊢ C
  sp→tm endˢᵖ        t = t
  sp→tm (appˢᵖ ss u) t = sp→tm ss (app t (nf→tm u))
  sp→tm (fstˢᵖ ss)   t = sp→tm ss (fst t)
  sp→tm (sndˢᵖ ss)   t = sp→tm ss (snd t)


-- Monotonicity with respect to context inclusion.

mutual
  mono⊢ⁿᶠ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᶠ A → Γ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ η (neⁿᶠ t)     = neⁿᶠ (mono⊢ⁿᵉ η t)
  mono⊢ⁿᶠ η (lamⁿᶠ t)    = lamⁿᶠ (mono⊢ⁿᶠ (keep η) t)
  mono⊢ⁿᶠ η unitⁿᶠ       = unitⁿᶠ
  mono⊢ⁿᶠ η (pairⁿᶠ t u) = pairⁿᶠ (mono⊢ⁿᶠ η t) (mono⊢ⁿᶠ η u)

  mono⊢ⁿᵉ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ⁿᵉ A → Γ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ η (spⁿᵉ ss i) = spⁿᵉ (mono⊢ˢᵖ η ss) (mono∈ η i)

  mono⊢ˢᵖ : ∀ {A C Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢ˢᵖ A ∣ C → Γ′ ⊢ˢᵖ A ∣ C
  mono⊢ˢᵖ η endˢᵖ        = endˢᵖ
  mono⊢ˢᵖ η (appˢᵖ ss u) = appˢᵖ (mono⊢ˢᵖ η ss) (mono⊢ⁿᶠ η u)
  mono⊢ˢᵖ η (fstˢᵖ ss)   = fstˢᵖ (mono⊢ˢᵖ η ss)
  mono⊢ˢᵖ η (sndˢᵖ ss)   = sndˢᵖ (mono⊢ˢᵖ η ss)


-- Hereditary substitution and reduction.

mutual
  [_≔_]ⁿᶠ_ : ∀ {A B Γ} → (i : A ∈ Γ) → Γ - i ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B → Γ - i ⊢ⁿᶠ B
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ ss j ) with i ≟∈ j
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ ss .i) | same   = reduce ([ i ≔ s ]ˢᵖ ss) s
  [ i ≔ s ]ⁿᶠ neⁿᶠ (spⁿᵉ ss ._) | diff j = neⁿᶠ (spⁿᵉ ([ i ≔ s ]ˢᵖ ss) j)
  [ i ≔ s ]ⁿᶠ lamⁿᶠ t           = lamⁿᶠ ([ pop i ≔ mono⊢ⁿᶠ weak⊆ s ]ⁿᶠ t)
  [ i ≔ s ]ⁿᶠ unitⁿᶠ            = unitⁿᶠ
  [ i ≔ s ]ⁿᶠ pairⁿᶠ t u        = pairⁿᶠ ([ i ≔ s ]ⁿᶠ t) ([ i ≔ s ]ⁿᶠ u)

  [_≔_]ˢᵖ_ : ∀ {A B C Γ} → (i : A ∈ Γ) → Γ - i ⊢ⁿᶠ A → Γ ⊢ˢᵖ B ∣ C → Γ - i ⊢ˢᵖ B ∣ C
  [ i ≔ s ]ˢᵖ endˢᵖ      = endˢᵖ
  [ i ≔ s ]ˢᵖ appˢᵖ ss u = appˢᵖ ([ i ≔ s ]ˢᵖ ss) ([ i ≔ s ]ⁿᶠ u)
  [ i ≔ s ]ˢᵖ fstˢᵖ ss   = fstˢᵖ ([ i ≔ s ]ˢᵖ ss)
  [ i ≔ s ]ˢᵖ sndˢᵖ ss   = sndˢᵖ ([ i ≔ s ]ˢᵖ ss)

  reduce : ∀ {A C Γ} → Γ ⊢ˢᵖ A ∣ C → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ C
  reduce endˢᵖ        t            = t
  reduce (appˢᵖ ss u) (lamⁿᶠ t)    = reduce ss ([ top ≔ u ]ⁿᶠ t)
  reduce (fstˢᵖ ss)   (pairⁿᶠ t u) = reduce ss t
  reduce (sndˢᵖ ss)   (pairⁿᶠ t u) = reduce ss u


-- Derived neutrals.

varⁿᵉ : ∀ {A Γ} → A ∈ Γ → Γ ⊢ⁿᵉ A
varⁿᵉ i = spⁿᵉ endˢᵖ i

appⁿᵉ : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ⊃ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᵉ B
appⁿᵉ (spⁿᵉ ss u) t = spⁿᵉ (≪app ss t) u
  where
    ≪app : ∀ {A B C Γ} → Γ ⊢ˢᵖ C ∣ A ⊃ B → Γ ⊢ⁿᶠ A → Γ ⊢ˢᵖ C ∣ B
    ≪app endˢᵖ        t = appˢᵖ endˢᵖ t
    ≪app (appˢᵖ ss u) t = appˢᵖ (≪app ss t) u
    ≪app (fstˢᵖ ss)   t = fstˢᵖ (≪app ss t)
    ≪app (sndˢᵖ ss)   t = sndˢᵖ (≪app ss t)

fstⁿᵉ : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ A
fstⁿᵉ (spⁿᵉ ss t) = spⁿᵉ (≪fst ss) t
  where
    ≪fst : ∀ {A B C Γ} → Γ ⊢ˢᵖ C ∣ A ∧ B → Γ ⊢ˢᵖ C ∣ A
    ≪fst endˢᵖ        = fstˢᵖ endˢᵖ
    ≪fst (appˢᵖ ss u) = appˢᵖ (≪fst ss) u
    ≪fst (fstˢᵖ ss)   = fstˢᵖ (≪fst ss)
    ≪fst (sndˢᵖ ss)   = sndˢᵖ (≪fst ss)

sndⁿᵉ : ∀ {A B Γ} → Γ ⊢ⁿᵉ A ∧ B → Γ ⊢ⁿᵉ B
sndⁿᵉ (spⁿᵉ ss t) = spⁿᵉ (≪snd ss) t
  where
    ≪snd : ∀ {A B C Γ} → Γ ⊢ˢᵖ C ∣ A ∧ B → Γ ⊢ˢᵖ C ∣ B
    ≪snd endˢᵖ        = sndˢᵖ endˢᵖ
    ≪snd (appˢᵖ ss u) = appˢᵖ (≪snd ss) u
    ≪snd (fstˢᵖ ss)   = fstˢᵖ (≪snd ss)
    ≪snd (sndˢᵖ ss)   = sndˢᵖ (≪snd ss)


-- Iterated expansion.

expand : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊢ⁿᶠ A
expand {α p}   t = neⁿᶠ t
expand {A ⊃ B} t = lamⁿᶠ (expand (appⁿᵉ (mono⊢ⁿᵉ weak⊆ t) (expand (varⁿᵉ top))))
expand {ι}     t = unitⁿᶠ
expand {A ∧ B} t = pairⁿᶠ (expand (fstⁿᵉ t)) (expand (sndⁿᵉ t))


-- Derived normal forms.

varⁿᶠ : ∀ {A Γ} → A ∈ Γ → Γ ⊢ⁿᶠ A
varⁿᶠ i = expand (varⁿᵉ i)

appⁿᶠ : ∀ {A B Γ} → Γ ⊢ⁿᶠ A ⊃ B → Γ ⊢ⁿᶠ A → Γ ⊢ⁿᶠ B
appⁿᶠ (lamⁿᶠ t) u = [ top ≔ u ]ⁿᶠ t

fstⁿᶠ : ∀ {A B Γ} → Γ ⊢ⁿᶠ A ∧ B → Γ ⊢ⁿᶠ A
fstⁿᶠ (pairⁿᶠ t u) = t

sndⁿᶠ : ∀ {A B Γ} → Γ ⊢ⁿᶠ A ∧ B → Γ ⊢ⁿᶠ B
sndⁿᶠ (pairⁿᶠ t u) = u


-- Translation from terms to normal forms.

tm→nf : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ⁿᶠ A
tm→nf (var i)    = varⁿᶠ i
tm→nf (lam t)    = lamⁿᶠ (tm→nf t)
tm→nf (app t u)  = appⁿᶠ (tm→nf t) (tm→nf u)
tm→nf unit       = unitⁿᶠ
tm→nf (pair t u) = pairⁿᶠ (tm→nf t) (tm→nf u)
tm→nf (fst t)    = fstⁿᶠ (tm→nf t)
tm→nf (snd t)    = sndⁿᶠ (tm→nf t)


-- Normalisation.

norm : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ A
norm = nf→tm ∘ tm→nf


-- TODO: Correctness with respect to conversion.

-- coco : ∀ {A Γ} {t t′ : Γ ⊢ A} → t ⇒ t′ → norm t ≡ norm t′
-- coco refl⇒           = refl
-- coco (trans⇒ p q)    = trans (coco p) (coco q)
-- coco (sym⇒ p)        = sym (coco p)
-- coco (cong⇒lam p)    = cong lam (coco p)
-- coco (cong⇒app p q)  = cong₂ {!!} (coco p) (coco q)
-- coco (cong⇒pair p q) = cong₂ pair (coco p) (coco q)
-- coco (cong⇒fst p)    = cong {!!} (coco p)
-- coco (cong⇒snd p)    = cong {!!} (coco p)
-- coco conv⇒lam        = {!!}
-- coco conv⇒app        = refl
-- coco conv⇒unit       = {!!}
-- coco conv⇒pair       = {!!}
-- coco conv⇒fst        = refl
-- coco conv⇒snd        = refl
