module A201606.STLC.HereditarySubstitution where

open import A201606.STLC.Syntax public

open import Data.Product using (_×_) renaming (_,_ to _∙_)
open import Function using (_∘_)


-- Normal terms, neutral terms, and spines.

mutual
  data No (Γ : Cx Ty) : Ty → Set where
    lamₙ  : ∀ {A B} → No (Γ , A) B → No Γ (A ⊃ B)
    pairₙ : ∀ {A B} → No Γ A → No Γ B → No Γ (A ∧ B)
    unitₙ : No Γ ⊤
    neₙ   : Ne Γ ι → No Γ ι

  data Ne (Γ : Cx Ty) : Ty → Set where
    spₙ : ∀ {A B} → Sp Γ (B ∙ A) → A ∈ Γ → Ne Γ B

  data Sp (Γ : Cx Ty) : Ty × Ty → Set where
    ∅ₛ   : ∀ {Z} → Sp Γ (Z ∙ Z)
    appₛ : ∀ {Z A B} → Sp Γ (Z ∙ B) → No Γ A → Sp Γ (Z ∙ (A ⊃ B))
    fstₛ : ∀ {Z A B} → Sp Γ (Z ∙ A) → Sp Γ (Z ∙ (A ∧ B))
    sndₛ : ∀ {Z A B} → Sp Γ (Z ∙ B) → Sp Γ (Z ∙ (A ∧ B))


-- Weakening.

mutual
  ren-no : ∀ {Γ Γ′} → Renᵢ Γ Γ′ → Ren No Γ Γ′
  ren-no ρ (lamₙ t)    = lamₙ (ren-no (wk-renᵢ ρ) t)
  ren-no ρ (pairₙ t u) = pairₙ (ren-no ρ t) (ren-no ρ u)
  ren-no ρ unitₙ       = unitₙ
  ren-no ρ (neₙ t)     = neₙ (ren-ne ρ t)

  ren-ne : ∀ {Γ Γ′} → Renᵢ Γ Γ′ → Ren Ne Γ Γ′
  ren-ne ρ (spₙ ss i) = spₙ (ren-sp ρ ss) (ρ i)

  ren-sp : ∀ {Γ Γ′} → Renᵢ Γ Γ′ → Ren Sp Γ Γ′
  ren-sp ρ ∅ₛ          = ∅ₛ
  ren-sp ρ (appₛ ss t) = appₛ (ren-sp ρ ss) (ren-no ρ t)
  ren-sp ρ (fstₛ ss)   = fstₛ (ren-sp ρ ss)
  ren-sp ρ (sndₛ ss)   = sndₛ (ren-sp ρ ss)

wk-no : ∀ {A Γ} → Ren No Γ (Γ , A)
wk-no = ren-no pop

wk-ne : ∀ {A Γ} → Ren Ne Γ (Γ , A)
wk-ne = ren-ne pop


-- Hereditary substitution.

mutual
  [_≔_]ₙ_ : ∀ {A Γ} → (i : A ∈ Γ) → No (Γ -ᵢ i) A → Sub No Γ (Γ -ᵢ i)
  [ i ≔ ν ]ₙ (lamₙ t)          = lamₙ ([ pop i ≔ wk-no ν ]ₙ t)
  [ i ≔ ν ]ₙ (pairₙ t u)       = pairₙ ([ i ≔ ν ]ₙ t) ([ i ≔ ν ]ₙ u)
  [ i ≔ ν ]ₙ unitₙ             = unitₙ
  [ i ≔ ν ]ₙ (neₙ (spₙ ss j))  with i ≟ᵢ j
  [ i ≔ ν ]ₙ (neₙ (spₙ ss .i)) | same   = reduce ([ i ≔ ν ]ₛ ss) ν
  [ i ≔ ν ]ₙ (neₙ (spₙ ss ._)) | diff j = neₙ (spₙ ([ i ≔ ν ]ₛ ss) j)

  [_≔_]ₛ_ : ∀ {A Γ} → (i : A ∈ Γ) → No (Γ -ᵢ i) A → Sub Sp Γ (Γ -ᵢ i)
  [ i ≔ ν ]ₛ ∅ₛ          = ∅ₛ
  [ i ≔ ν ]ₛ (appₛ ss t) = appₛ ([ i ≔ ν ]ₛ ss) ([ i ≔ ν ]ₙ t)
  [ i ≔ ν ]ₛ (fstₛ ss)   = fstₛ ([ i ≔ ν ]ₛ ss)
  [ i ≔ ν ]ₛ (sndₛ ss)   = sndₛ ([ i ≔ ν ]ₛ ss)

  reduce : ∀ {A B Γ} → Sp Γ (B ∙ A) → No Γ A → No Γ B
  reduce ∅ₛ          t           = t
  reduce (appₛ ss u) (lamₙ t)    = reduce ss ([ top ≔ u ]ₙ t)
  reduce (fstₛ ss)   (pairₙ t u) = reduce ss t
  reduce (sndₛ ss)   (pairₙ t u) = reduce ss u


-- Iterated expansion.

append-appₛ : ∀ {A B C Γ} → Sp Γ ((A ⊃ B) ∙ C) → No Γ A → Sp Γ (B ∙ C)
append-appₛ ∅ₛ          u = appₛ ∅ₛ u
append-appₛ (appₛ ss t) u = appₛ (append-appₛ ss u) t
append-appₛ (fstₛ ss)   u = fstₛ (append-appₛ ss u)
append-appₛ (sndₛ ss)   u = sndₛ (append-appₛ ss u)

append-fstₛ : ∀ {A B C Γ} → Sp Γ ((A ∧ B) ∙ C) → Sp Γ (A ∙ C)
append-fstₛ ∅ₛ          = fstₛ ∅ₛ
append-fstₛ (appₛ ss t) = appₛ (append-fstₛ ss) t
append-fstₛ (fstₛ ss)   = fstₛ (append-fstₛ ss)
append-fstₛ (sndₛ ss)   = sndₛ (append-fstₛ ss)

append-sndₛ : ∀ {A B C Γ} → Sp Γ ((A ∧ B) ∙ C) → Sp Γ (B ∙ C)
append-sndₛ ∅ₛ          = sndₛ ∅ₛ
append-sndₛ (appₛ ss t) = appₛ (append-sndₛ ss) t
append-sndₛ (fstₛ ss)   = fstₛ (append-sndₛ ss)
append-sndₛ (sndₛ ss)   = sndₛ (append-sndₛ ss)

varₙ : ∀ {A Γ} → A ∈ Γ → Ne Γ A
varₙ i = spₙ ∅ₛ i

appₙ : ∀ {A B Γ} → Ne Γ (A ⊃ B) → No Γ A → Ne Γ B
appₙ (spₙ ss t) u = spₙ (append-appₛ ss u) t

fstₙ : ∀ {A B Γ} → Ne Γ (A ∧ B) → Ne Γ A
fstₙ (spₙ ss t) = spₙ (append-fstₛ ss) t

sndₙ : ∀ {A B Γ} → Ne Γ (A ∧ B) → Ne Γ B
sndₙ (spₙ ss t) = spₙ (append-sndₛ ss) t

expand : ∀ {A Γ} → Ne Γ A → No Γ A
expand {ι}     t = neₙ t
expand {A ⊃ B} t = lamₙ (expand (appₙ (wk-ne t) (expand (varₙ top))))
expand {A ∧ B} t = pairₙ (expand (fstₙ t)) (expand (sndₙ t))
expand {⊤}    t = unitₙ


-- Normalisation.

tm⇒no : ∀ {A Γ} → Tm A Γ → No A Γ
tm⇒no (var i)    = expand (varₙ i)
tm⇒no (lam t)    = lamₙ (tm⇒no t)
tm⇒no (app t u)  = reduce (appₛ ∅ₛ (tm⇒no u)) (tm⇒no t)
tm⇒no (pair t u) = pairₙ (tm⇒no t) (tm⇒no u)
tm⇒no (fst t)    = reduce (fstₛ ∅ₛ) (tm⇒no t)
tm⇒no (snd t)    = reduce (sndₛ ∅ₛ) (tm⇒no t)
tm⇒no unit       = unitₙ

mutual
  no⇒tm : ∀ {A Γ} → No Γ A → Tm Γ A
  no⇒tm (lamₙ t)    = lam (no⇒tm t)
  no⇒tm (pairₙ t u) = pair (no⇒tm t) (no⇒tm u)
  no⇒tm unitₙ       = unit
  no⇒tm (neₙ t)     = ne⇒tm t

  ne⇒tm : ∀ {A Γ} → Ne Γ A → Tm Γ A
  ne⇒tm (spₙ ss i) = sp⇒tm ss (var i)

  sp⇒tm : ∀ {A B Γ} → Sp Γ (B ∙ A) → Tm Γ A → Tm Γ B
  sp⇒tm ∅ₛ          u = u
  sp⇒tm (appₛ ss t) u = sp⇒tm ss (app u (no⇒tm t))
  sp⇒tm (fstₛ ss)   u = sp⇒tm ss (fst u)
  sp⇒tm (sndₛ ss)   u = sp⇒tm ss (snd u)

norm : ∀ {A Γ} → Tm A Γ → Tm A Γ
norm = no⇒tm ∘ tm⇒no
