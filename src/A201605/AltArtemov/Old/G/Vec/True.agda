module A201605.AltArtemov.Old.G.Vec.True where

open import A201605.AltArtemov.Old.G.Vec.Core public


data True (Γ : Cx) : Ty → Set where
  var  : ∀ {A} → Var Γ A → True Γ A
  lam  : ∀ {A B} → True (Γ , A) B → True Γ (A ⊃ B)
  app  : ∀ {A B} → True Γ (A ⊃ B) → True Γ A → True Γ B
  pair : ∀ {A B} → True Γ A → True Γ B → True Γ (A ∧ B)
  fst  : ∀ {A B} → True Γ (A ∧ B) → True Γ A
  snd  : ∀ {A B} → True Γ (A ∧ B) → True Γ B
  up   : ∀ {A t} → True Γ (t ∶ A) → True Γ (! t ∶ t ∶ A)
  down : ∀ {A t} → True Γ (t ∶ A) → True Γ A

ᵗ⌊_⌋ : ∀ {Γ A} → True Γ A → Tm ᵍ⌊ Γ ⌋
ᵗ⌊ var x ⌋      = VAR[ 0 ] ⁱ⌊ x ⌋
ᵗ⌊ lam j ⌋      = LAM[ 0 ] ᵗ⌊ j ⌋
ᵗ⌊ app j₁ j₂ ⌋  = APP[ 0 ] ᵗ⌊ j₁ ⌋ ᵗ⌊ j₂ ⌋
ᵗ⌊ pair j₁ j₂ ⌋ = PAIR[ 0 ] ᵗ⌊ j₁ ⌋ ᵗ⌊ j₂ ⌋
ᵗ⌊ fst j ⌋      = FST[ 0 ] ᵗ⌊ j ⌋
ᵗ⌊ snd j ⌋      = SND[ 0 ] ᵗ⌊ j ⌋
ᵗ⌊ up j ⌋       = UP[ 0 ] ᵗ⌊ j ⌋
ᵗ⌊ down j ⌋     = DOWN[ 0 ] ᵗ⌊ j ⌋

ren-true : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → True Γ A → True Γ′ A
ren-true η (var x)      = var (ren-var η x)
ren-true η (lam j)      = lam (ren-true (lift η) j)
ren-true η (app j₁ j₂)  = app (ren-true η j₁) (ren-true η j₂)
ren-true η (pair j₁ j₂) = pair (ren-true η j₁) (ren-true η j₂)
ren-true η (fst j)      = fst (ren-true η j)
ren-true η (snd j)      = snd (ren-true η j)
ren-true η (up j)       = up (ren-true η j)
ren-true η (down j)     = down (ren-true η j)

wk-true : ∀ {Γ A C} → True Γ C → True (Γ , A) C
wk-true = ren-true ⊇wk

wk*-true : ∀ {Γ C} → True ∅ C → True Γ C
wk*-true = ren-true ⊇to

ren-true-id : ∀ {Γ A} (j : True Γ A) → ren-true ⊇id j ≡ j
ren-true-id (var x)      = cong var (ren-var-id x)
ren-true-id (lam j)      = cong lam (ren-true-id j)
ren-true-id (app j₁ j₂)  = cong₂ app (ren-true-id j₁) (ren-true-id j₂)
ren-true-id (pair j₁ j₂) = cong₂ pair (ren-true-id j₁) (ren-true-id j₂)
ren-true-id (fst j)      = cong fst (ren-true-id j)
ren-true-id (snd j)      = cong snd (ren-true-id j)
ren-true-id (up j)       = cong up (ren-true-id j)
ren-true-id (down j)     = cong down (ren-true-id j)

ren-true-● : ∀ {Γ Γ′ Γ″ A} (η′ : Γ″ ⊇ Γ′) (η : Γ′ ⊇ Γ) (j : True Γ A) →
               ren-true η′ (ren-true η j) ≡ ren-true (η′ ● η) j
ren-true-● η′ η (var x)      = cong var (ren-var-● η′ η x)
ren-true-● η′ η (lam j)      = cong lam (ren-true-● (lift η′) (lift η) j)
ren-true-● η′ η (app j₁ j₂)  = cong₂ app (ren-true-● η′ η j₁) (ren-true-● η′ η j₂)
ren-true-● η′ η (pair j₁ j₂) = cong₂ pair (ren-true-● η′ η j₁) (ren-true-● η′ η j₂)
ren-true-● η′ η (fst j)      = cong fst (ren-true-● η′ η j)
ren-true-● η′ η (snd j)      = cong snd (ren-true-● η′ η j)
ren-true-● η′ η (up j)       = cong up (ren-true-● η′ η j)
ren-true-● η′ η (down j)     = cong down (ren-true-● η′ η j)

v₀ : ∀ {Γ A} → True (Γ , A) A
v₀ = var x₀

v₁ : ∀ {Γ A B} → True ((Γ , A) , B) A
v₁ = var x₁

v₂ : ∀ {Γ A B C} → True (((Γ , A) , B) , C) A
v₂ = var x₂

I : ∀ {Γ A} → True Γ (A ⊃ A)
I = lam v₀

K : ∀ {Γ A B} → True Γ (A ⊃ B ⊃ A)
K = lam (lam v₁)

S : ∀ {Γ A B C} → True Γ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S = lam (lam (lam
      (app (app v₂ v₀)
           (app v₁ v₀))))
