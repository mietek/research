module A201606.STLC.Syntax where

open import A201606.Common.Context public


-- Types.

infixl 5 _∧_
infixr 3 _⊃_
data Ty : Set where
  ι   : Ty
  _⊃_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty
  ⊤  : Ty


-- Terms.

data Tm (Γ : Cx Ty) : Ty → Set where
  var  : ∀ {A} → A ∈ Γ → Tm Γ A
  lam  : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⊃ B)
  app  : ∀ {A B} → Tm Γ (A ⊃ B) → Tm Γ A → Tm Γ B
  pair : ∀ {A B} → Tm Γ A → Tm Γ B → Tm Γ (A ∧ B)
  fst  : ∀ {A B} → Tm Γ (A ∧ B) → Tm Γ A
  snd  : ∀ {A B} → Tm Γ (A ∧ B) → Tm Γ B
  unit : Tm Γ ⊤

v₀ : ∀ {A Γ} → Tm (Γ , A) A
v₀ = var i₀

v₁ : ∀ {A B Γ} → Tm (Γ , A , B) A
v₁ = var i₁

v₂ : ∀ {A B C Γ} → Tm (Γ , A , B , C) A
v₂ = var i₂


-- Weakening.

ren-tm : ∀ {Γ Γ′} → Renᵢ Γ Γ′ → Ren Tm Γ Γ′
ren-tm ρ (var i)    = var (ρ i)
ren-tm ρ (lam t)    = lam (ren-tm (wk-renᵢ ρ) t)
ren-tm ρ (app t u)  = app (ren-tm ρ t) (ren-tm ρ u)
ren-tm ρ (pair t u) = pair (ren-tm ρ t) (ren-tm ρ u)
ren-tm ρ (fst t)    = fst (ren-tm ρ t)
ren-tm ρ (snd t)    = snd (ren-tm ρ t)
ren-tm ρ unit       = unit

wk-tm : ∀ {A B Γ} → Tm Γ A → Tm (Γ , B) A
wk-tm = ren-tm pop


-- Substitution.

[_≔_]ᵢ_ : ∀ {A Γ} → (i : A ∈ Γ) → Tm (Γ -ᵢ i) A → Subᵢ Tm Γ (Γ -ᵢ i)
[ i ≔ ν ]ᵢ j  with i ≟ᵢ j
[ i ≔ ν ]ᵢ .i | same   = ν
[ i ≔ ν ]ᵢ ._ | diff j = var j

[_≔_]_ : ∀ {A Γ} → (i : A ∈ Γ) → Tm (Γ -ᵢ i) A → Sub Tm Γ (Γ -ᵢ i)
[ i ≔ ν ] (var j)    = [ i ≔ ν ]ᵢ j
[ i ≔ ν ] (lam t)    = lam ([ pop i ≔ wk-tm ν ] t)
[ i ≔ ν ] (app t u)  = app ([ i ≔ ν ] t) ([ i ≔ ν ] u)
[ i ≔ ν ] (pair t u) = pair ([ i ≔ ν ] t) ([ i ≔ ν ] u)
[ i ≔ ν ] (fst t)    = fst ([ i ≔ ν ] t)
[ i ≔ ν ] (snd t)    = snd ([ i ≔ ν ] t)
[ i ≔ ν ] unit       = unit


-- Conversion to β-short, η-long normal form.

infix 0 _▻_
data _▻_ {Γ : Cx Ty} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  refl▻     : ∀ {A} {t : Tm Γ A} → t ▻ t
  sym▻      : ∀ {A} {t t′ : Tm Γ A} → t ▻ t′ → t′ ▻ t
  trans▻    : ∀ {A} {t t′ t″ : Tm Γ A} → t ▻ t′ → t′ ▻ t″ → t ▻ t″
  cong▻lam  : ∀ {A B} {t t′ : Tm (Γ , A) B} → t ▻ t′ → lam t ▻ lam t′
  cong▻app  : ∀ {A B} {t t′ : Tm Γ (A ⊃ B)} {u u′ : Tm Γ A} → t ▻ t′ → u ▻ u′ → app t u ▻ app t′ u′
  cong▻pair : ∀ {A B} {t t′ : Tm Γ A} {u u′ : Tm Γ B} → t ▻ t′ → u ▻ u′ → pair t u ▻ pair t′ u′
  cong▻fst  : ∀ {A B} {t t′ : Tm Γ (A ∧ B)} → t ▻ t′ → fst t ▻ fst t′
  cong▻snd  : ∀ {A B} {t t′ : Tm Γ (A ∧ B)} → t ▻ t′ → snd t ▻ snd t′
  reduce▻⊃  : ∀ {A B} {t : Tm (Γ , A) B} {u : Tm Γ A} → app (lam t) u ▻ [ top ≔ u ] t
  expand▻⊃  : ∀ {A B} {t : Tm Γ (A ⊃ B)} → t ▻ lam (app (wk-tm t) (var top))
  reduce▻∧₁ : ∀ {A B} {t : Tm Γ A} {u : Tm Γ B} → fst (pair t u) ▻ t
  reduce▻∧₂ : ∀ {A B} {t : Tm Γ A} {u : Tm Γ B} → snd (pair t u) ▻ u
  expand▻∧  : ∀ {A B} {t : Tm Γ (A ∧ B)} → t ▻ pair (fst t) (snd t)
