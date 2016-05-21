module AltArtemov.Try4.Try4 where

open import AltArtemov.Library.Fin public


mutual
  data Cx : Set where
    ∅   : Cx
    _,_ : Cx → Ty → Cx

  data Ty : Set where
    ⊥  : Ty
    _⊃_ : Ty → Ty → Ty
    _∧_ : Ty → Ty → Ty
    _∵_ : (A : Ty) → Tm ∅ A → Ty

  data Var : Cx → Ty → Set where
    top : ∀ {Γ A} → Var (Γ , A) A
    pop : ∀ {Γ A B} → Var Γ A → Var (Γ , B) A

  data Tm (Γ : Cx) : Ty → Set where
    var  : ∀ {A} → Var Γ A → Tm Γ A
    lam  : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⊃ B)
    app  : ∀ {A B} → Tm Γ (A ⊃ B) → Tm Γ A → Tm Γ B
    pair : ∀ {A B} → Tm Γ A → Tm Γ B → Tm Γ (A ∧ B)
    fst  : ∀ {A B} → Tm Γ (A ∧ B) → Tm Γ A
    snd  : ∀ {A B} → Tm Γ (A ∧ B) → Tm Γ B
    up   : ∀ {A} → (t : Tm ∅ A) → Tm Γ (A ∵ t)
    down : ∀ {A t} → Tm Γ (A ∵ t) → Tm Γ A

infixr 5 _⊃_
infixl 15 _∵_


x₀ : ∀ {Γ A} → Var (Γ , A) A
x₀ = top

x₁ : ∀ {Γ A B} → Var ((Γ , A) , B) A
x₁ = pop x₀

x₂ : ∀ {Γ A B C} → Var (((Γ , A) , B) , C) A
x₂ = pop x₁

v₀ : ∀ {Γ A} → Tm (Γ , A) A
v₀ = var x₀

v₁ : ∀ {Γ A B} → Tm ((Γ , A), B) A
v₁ = var x₁

v₂ : ∀ {Γ A B C} → Tm (((Γ , A) , B) , C) A
v₂ = var x₂

I : ∀ {Γ A} → Tm Γ (A ⊃ A)
I = lam v₀

K : ∀ {Γ A B} → Tm Γ (A ⊃ B ⊃ A)
K = lam (lam v₁)

S : ∀ {Γ A B C} → Tm Γ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))

-- f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ (f ∘ x) ∶ B
--D : ∀ {Γ A B f x} → Tm Γ (((A ⊃ B) ∵ f) ⊃ (A ∵ x) ⊃ (B ∵ (app f x)))
D : ∀ {Γ A B f x} → Tm Γ ((A ⊃ B) ∵ f ⊃ A ∵ x ⊃ B ∵ (app f x))
D = lam (lam (up {!!}))

T : ∀ {Γ A x} → Tm Γ (A ∵ x ⊃ A)
T = lam (down v₀)

S4 : ∀ {Γ A x} → Tm Γ (A ∵ x ⊃ A ∵ x ∵ {!!})
S4 = lam (up {!!})
