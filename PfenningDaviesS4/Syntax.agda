module PfenningDaviesS4.Syntax where

open import Common.Context public

open import Function using (flip)


-- Types.

infixl 5 _∧_
infixr 3 _⊃_
data Ty : Set where
  ι   : Ty
  _⊃_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty
  □_  : Ty → Ty
  ⊤  : Ty


-- Terms.

data Tm (Γ Δ : Cx Ty) : Ty → Set where
  var   : ∀ {A} → A ∈ Γ → Tm Γ Δ A
  ⋆var  : ∀ {A} → A ∈ Δ → Tm Γ Δ A
  lam   : ∀ {A B} → Tm (Γ , A) Δ B → Tm Γ Δ (A ⊃ B)
  app   : ∀ {A B} → Tm Γ Δ (A ⊃ B) → Tm Γ Δ A → Tm Γ Δ B
  pair  : ∀ {A B} → Tm Γ Δ A → Tm Γ Δ B → Tm Γ Δ (A ∧ B)
  fst   : ∀ {A B} → Tm Γ Δ (A ∧ B) → Tm Γ Δ A
  snd   : ∀ {A B} → Tm Γ Δ (A ∧ B) → Tm Γ Δ B
  unit  : Tm Γ Δ ⊤
  box   : ∀ {A} → Tm ∅ Δ A → Tm Γ Δ (□ A)
  unbox : ∀ {A C} → Tm Γ Δ (□ A) → Tm Γ (Δ , A) C → Tm Γ Δ C

v₀ : ∀ {A Γ Δ} → Tm (Γ , A) Δ A
v₀ = var i₀

v₁ : ∀ {A B Γ Δ} → Tm (Γ , A , B) Δ A
v₁ = var i₁

v₂ : ∀ {A B C Γ Δ} → Tm (Γ , A , B , C) Δ A
v₂ = var i₂

⋆v₀ : ∀ {A Γ Δ} → Tm Γ (Δ , A) A
⋆v₀ = ⋆var i₀

⋆v₁ : ∀ {A B Γ Δ} → Tm Γ (Δ , A , B) A
⋆v₁ = ⋆var i₁

⋆v₂ : ∀ {A B C Γ Δ} → Tm Γ (Δ , A , B , C) A
⋆v₂ = ⋆var i₂


-- Weakening.

ren-tm : ∀ {Γ Γ′ Δ} → Renᵢ Γ Γ′ → Ren (flip Tm Δ) Γ Γ′
ren-tm ρ (var i)     = var (ρ i)
ren-tm ρ (⋆var i)    = ⋆var i
ren-tm ρ (lam t)     = lam (ren-tm (wk-renᵢ ρ) t)
ren-tm ρ (app t u)   = app (ren-tm ρ t) (ren-tm ρ u)
ren-tm ρ (pair t u)  = pair (ren-tm ρ t) (ren-tm ρ u)
ren-tm ρ (fst t)     = fst (ren-tm ρ t)
ren-tm ρ (snd t)     = snd (ren-tm ρ t)
ren-tm ρ unit        = unit
ren-tm ρ (box t)     = box t
ren-tm ρ (unbox t u) = unbox (ren-tm ρ t) (ren-tm ρ u)

wk-tm : ∀ {A Γ Δ} → Ren (flip Tm Δ) Γ (Γ , A)
wk-tm = ren-tm pop

wk-tm∅ : ∀ {Γ Δ} → Ren (flip Tm Δ) ∅ Γ
wk-tm∅ = ren-tm (λ ())


-- Modal weakening.

⋆ren-tm : ∀ {Γ Δ Δ′} → Renᵢ Δ Δ′ → Ren (Tm Γ) Δ Δ′
⋆ren-tm ρ (var i)     = var i
⋆ren-tm ρ (⋆var i)    = ⋆var (ρ i)
⋆ren-tm ρ (lam t)     = lam (⋆ren-tm ρ t)
⋆ren-tm ρ (app t u)   = app (⋆ren-tm ρ t) (⋆ren-tm ρ u)
⋆ren-tm ρ (pair t u)  = pair (⋆ren-tm ρ t) (⋆ren-tm ρ u)
⋆ren-tm ρ (fst t)     = fst (⋆ren-tm ρ t)
⋆ren-tm ρ (snd t)     = snd (⋆ren-tm ρ t)
⋆ren-tm ρ unit        = unit
⋆ren-tm ρ (box t)     = box (⋆ren-tm ρ t)
⋆ren-tm ρ (unbox t u) = unbox (⋆ren-tm ρ t) (⋆ren-tm (wk-renᵢ ρ) u)

⋆wk-tm : ∀ {A Γ Δ} → Ren (Tm Γ) Δ (Δ , A)
⋆wk-tm = ⋆ren-tm pop


-- Substitution.

[_≔_]ᵢ_ : ∀ {A Γ Δ} → (i : A ∈ Γ) → Tm (Γ -ᵢ i) Δ A → Subᵢ (flip Tm Δ) Γ (Γ -ᵢ i)
[ i ≔ ν ]ᵢ j  with i ≟ᵢ j
[ i ≔ ν ]ᵢ .i | same   = ν
[ i ≔ ν ]ᵢ ._ | diff j = var j

[_≔_]_ : ∀ {A Γ Δ} → (i : A ∈ Γ) → Tm (Γ -ᵢ i) Δ A → Sub (flip Tm Δ) Γ (Γ -ᵢ i)
[ i ≔ ν ] (var j)     = [ i ≔ ν ]ᵢ j
[ i ≔ ν ] (⋆var j)    = ⋆var j
[ i ≔ ν ] (lam t)     = lam ([ pop i ≔ wk-tm ν ] t)
[ i ≔ ν ] (app t u)   = app ([ i ≔ ν ] t) ([ i ≔ ν ] u)
[ i ≔ ν ] (pair t u)  = pair ([ i ≔ ν ] t) ([ i ≔ ν ] u)
[ i ≔ ν ] (fst t)     = fst ([ i ≔ ν ] t)
[ i ≔ ν ] (snd t)     = snd ([ i ≔ ν ] t)
[ i ≔ ν ] unit        = unit
[ i ≔ ν ] (box t)     = box t
[ i ≔ ν ] (unbox t u) = unbox ([ i ≔ ν ] t) ([ i ≔ ⋆wk-tm ν ] u)


-- Modal substitution.

⋆[_≔_]ᵢ_ : ∀ {A Γ Δ} → (i : A ∈ Δ) → Tm ∅ (Δ -ᵢ i) A → Subᵢ (Tm Γ) Δ (Δ -ᵢ i)
⋆[ i ≔ ν ]ᵢ j  with i ≟ᵢ j
⋆[ i ≔ ν ]ᵢ .i | same   = wk-tm∅ ν
⋆[ i ≔ ν ]ᵢ ._ | diff j = ⋆var j

⋆[_≔_]_ : ∀ {A Γ Δ} → (i : A ∈ Δ) → Tm ∅ (Δ -ᵢ i) A → Sub (Tm Γ) Δ (Δ -ᵢ i)
⋆[ i ≔ ν ] (var j)     = var j
⋆[ i ≔ ν ] (⋆var j)    = ⋆[ i ≔ ν ]ᵢ j
⋆[ i ≔ ν ] (lam t)     = lam (⋆[ i ≔ ν ] t)
⋆[ i ≔ ν ] (app t u)   = app (⋆[ i ≔ ν ] t) (⋆[ i ≔ ν ] u)
⋆[ i ≔ ν ] (pair t u)  = pair (⋆[ i ≔ ν ] t) (⋆[ i ≔ ν ] u)
⋆[ i ≔ ν ] (fst t)     = fst (⋆[ i ≔ ν ] t)
⋆[ i ≔ ν ] (snd t)     = snd (⋆[ i ≔ ν ] t)
⋆[ i ≔ ν ] unit        = unit
⋆[ i ≔ ν ] (box t)     = box (⋆[ i ≔ ν ] t)
⋆[ i ≔ ν ] (unbox t u) = unbox (⋆[ i ≔ ν ] t) (⋆[ pop i ≔ ⋆wk-tm ν ] u)


-- Conversion to β-short, η-long normal form.

infix 0 _▻_
data _▻_ {Γ Δ : Cx Ty} : ∀ {A} → Tm Γ Δ A → Tm Γ Δ A → Set where
  refl▻      : ∀ {A} {t : Tm Γ Δ A} → t ▻ t
  sym▻       : ∀ {A} {t t′ : Tm Γ Δ A} → t ▻ t′ → t′ ▻ t
  trans▻     : ∀ {A} {t t′ t″ : Tm Γ Δ A} → t ▻ t′ → t′ ▻ t″ → t ▻ t″
  cong▻lam   : ∀ {A B} {t t′ : Tm (Γ , A) Δ B} → t ▻ t′ → lam t ▻ lam t′
  cong▻app   : ∀ {A B} {t t′ : Tm Γ Δ (A ⊃ B)} {u u′ : Tm Γ Δ A} → t ▻ t′ → u ▻ u′ → app t u ▻ app t′ u′
  cong▻pair  : ∀ {A B} {t t′ : Tm Γ Δ A} {u u′ : Tm Γ Δ B} → t ▻ t′ → u ▻ u′ → pair t u ▻ pair t′ u′
  cong▻fst   : ∀ {A B} {t t′ : Tm Γ Δ (A ∧ B)} → t ▻ t′ → fst t ▻ fst t′
  cong▻snd   : ∀ {A B} {t t′ : Tm Γ Δ (A ∧ B)} → t ▻ t′ → snd t ▻ snd t′
  cong▻box   : ∀ {A} {t t′ : Tm ∅ Δ A} → t ▻ t′ → box t ▻ box t′
  cong▻unbox : ∀ {A C} {t t′ : Tm Γ Δ (□ A)} {u u′ : Tm Γ (Δ , A) C} → t ▻ t′ → u ▻ u′ → unbox t u ▻ unbox t′ u′
  reduce▻⊃   : ∀ {A B} {t : Tm (Γ , A) Δ B} {u : Tm Γ Δ A} → app (lam t) u ▻ [ top ≔ u ] t
  expand▻⊃   : ∀ {A B} {t : Tm Γ Δ (A ⊃ B)} → t ▻ lam (app (wk-tm t) (var top))
  reduce▻∧₁  : ∀ {A B} {t : Tm Γ Δ A} {u : Tm Γ Δ B} → fst (pair t u) ▻ t
  reduce▻∧₂  : ∀ {A B} {t : Tm Γ Δ A} {u : Tm Γ Δ B} → snd (pair t u) ▻ u
  expand▻∧   : ∀ {A B} {t : Tm Γ Δ (A ∧ B)} → t ▻ pair (fst t) (snd t)
  reduce▻□   : ∀ {A C} {t : Tm ∅ Δ A} {u : Tm Γ (Δ , A) C} → unbox (box t) u ▻ ⋆[ top ≔ t ] u
  expand▻□   : ∀ {A} {t : Tm Γ Δ (□ A)} → t ▻ unbox t (box (⋆var top))
