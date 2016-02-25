module AltArtemov where

open import Data.Nat using (ℕ)


infixl 5 _∧_
infixr 4 _⊃_
infixr 3 _∷_
infix 2 _,_
infix 1 _∈_
infix 0 _⊢_


data Tm : Set where
  fⁿ_⇒_#_   : Tm → Tm → ℕ → Tm
  _∘ⁿ_#_    : Tm → Tm → ℕ → Tm
  pⁿ⟨_,_⟩#_ : Tm → Tm → ℕ → Tm
  π₀ⁿ_#_    : Tm → ℕ → Tm
  π₁ⁿ_#_    : Tm → ℕ → Tm
  ⇑ⁿ_#_     : Tm → ℕ → Tm
  ⇓ⁿ_#_     : Tm → ℕ → Tm
  !_        : Tm → Tm


data Ty : Set where
  _∧_ : Ty → Ty → Ty
  _⊃_ : Ty → Ty → Ty
  _∷_ : Tm → Ty → Ty
  ⊥   : Ty


⊤ : Ty
⊤ = ⊥ ⊃ ⊥

¬_ : Ty → Ty
¬ A = A ⊃ ⊥

_⊃⊂_ : Ty → Ty → Ty
A ⊃⊂ B = A ⊃ B ∧ B ⊃ A


data Cx : Set where
  []  : Cx
  _,_ : Cx → Ty → Cx


data _∈_ (A : Ty) : Cx → Set where
  vz : ∀{Γ} → A ∈ Γ , A
  vs : ∀{Γ}{B : Ty} → A ∈ Γ → A ∈ Γ , B


f_⇒_ : Tm → Tm → Tm
f x ⇒ t = fⁿ x ⇒ t # 1

_∘_ : Tm → Tm → Tm
t ∘ s = t ∘ⁿ s # 1

p⟨_,_⟩ : Tm → Tm → Tm
p⟨ t , s ⟩ = pⁿ⟨ t , s ⟩# 1

π₀_ : Tm → Tm
π₀ t = π₀ⁿ t # 1

π₁_ : Tm → Tm
π₁ t = π₁ⁿ t # 1

⇑_ : Tm → Tm
⇑ t = ⇑ⁿ t # 1

⇓_ : Tm → Tm
⇓ t = ⇓ⁿ t # 1


f²_⇒_ : Tm → Tm → Tm
f² x ⇒ t = fⁿ x ⇒ t # 2

_∘²_ : Tm → Tm → Tm
t ∘² s = t ∘ⁿ s # 2

p²⟨_,_⟩ : Tm → Tm → Tm
p²⟨ t , s ⟩ = pⁿ⟨ t , s ⟩# 2

π₀²_ : Tm → Tm
π₀² t = π₀ⁿ t # 2

π₁²_ : Tm → Tm
π₁² t = π₁ⁿ t # 2

⇑²_ : Tm → Tm
⇑² t = ⇑ⁿ t # 2

⇓²_ : Tm → Tm
⇓² t = ⇓ⁿ t # 2


data _⊢_ : Cx → Ty → Set where
  Rx : ∀{Γ x A}
     → x ∷ A ∈ Γ
     → Γ ⊢ x ∷ A

  Rf : ∀{Γ x t A B}
     → Γ , x ∷ A ⊢ t ∷ B
     → Γ ⊢ f x ⇒ t ∷ A ⊃ B

  R∘ : ∀{Γ t s A B}
     → Γ ⊢ t ∷ A ⊃ B → Γ ⊢ s ∷ B
     → Γ ⊢ t ∘ s ∷ B

  Rp : ∀{Γ t s A B}
     → Γ ⊢ t ∷ A → Γ ⊢ s ∷ B
     → Γ ⊢ p⟨ t , s ⟩ ∷ A ∧ B

  Rπ₀ : ∀{Γ t A B}
      → Γ ⊢ t ∷ A ∧ B
      → Γ ⊢ π₀ t ∷ A

  Rπ₁ : ∀{Γ t A B}
      → Γ ⊢ t ∷ A ∧ B
      → Γ ⊢ π₁ t ∷ B

  R⇑ : ∀{Γ t u A}
     → Γ ⊢ t ∷ u ∷ A
     → Γ ⊢ ⇑ t ∷ ! u ∷ u ∷ A

  R⇓ : ∀{Γ t u A}
     → Γ ⊢ t ∷ u ∷ A
     → Γ ⊢ ⇓ t ∷ A


  Rx² : ∀{Γ x₂ x₁ A}
     → x₂ ∷ x₁ ∷ A ∈ Γ
     → Γ ⊢ x₂ ∷ x₁ ∷ A

  Rf² : ∀{Γ x₂ x₁ t₂ t₁ A B}
      → Γ , x₂ ∷ x₁ ∷ A ⊢ t₂ ∷ t₁ ∷ B
      → Γ ⊢ (f² x₂ ⇒ t₂) ∷ (f x₁ ⇒ t₁) ∷ A ⊃ B

  R∘² : ∀{Γ t₂ t₁ s₂ s₁ A B}
      → Γ ⊢ t₂ ∷ t₁ ∷ A ⊃ B → Γ ⊢ s₂ ∷ s₁ ∷ B
      → Γ ⊢ t₂ ∘² s₂ ∷ t₁ ∘ s₁ ∷ B

  Rp² : ∀{Γ t₂ t₁ s₂ s₁ A B}
      → Γ ⊢ t₂ ∷ t₁ ∷ A → Γ ⊢ s₂ ∷ s₁ ∷ B
      → Γ ⊢ p²⟨ t₂ , s₂ ⟩ ∷ p⟨ t₁ , s₁ ⟩ ∷ A ∧ B

  Rπ₀² : ∀{Γ t₂ t₁ A B}
       → Γ ⊢ t₂ ∷ t₁ ∷ A ∧ B
       → Γ ⊢ π₀² t₂ ∷ π₀ t₁ ∷ A

  Rπ₁² : ∀{Γ t₂ t₁ A B}
       → Γ ⊢ t₂ ∷ t₁ ∷ A ∧ B
       → Γ ⊢ π₁² t₂ ∷ π₁ t₁ ∷ B

  R⇑² : ∀{Γ t₂ t₁ u A}
      → Γ ⊢ t₂ ∷ t₁ ∷ u ∷ A
      → Γ ⊢ ⇑² t₂ ∷ ⇑ t₁ ∷ ! u ∷ u ∷ A

  R⇓² : ∀{Γ t₂ t₁ u A}
      → Γ ⊢ t₂ ∷ t₁ ∷ u ∷ A
      → Γ ⊢ ⇓² t₂ ∷ ⇓ t₁ ∷ A


⊩_ : Ty → Set
⊩ A = ∀{Γ} → Γ ⊢ A


e11 : ∀{x y A}
    → ⊩ (f y ⇒ (⇓ y) ∷ (x ∷ A) ⊃ A)
e11 = Rf (R⇓ (Rx vz))

e12 : ∀{x y A}
    → ⊩ (f y ⇒ (⇑ y) ∷ (x ∷ A) ⊃ (! x ∷ x ∷ A))
e12 = Rf (R⇑ (Rx vz))

e13 : ∀{u v x y A B}
    → ⊩ ((f² u ⇒ (f² v ⇒ p²⟨ u , v ⟩)) ∷ (f x ⇒ (f y ⇒ p⟨ x , y ⟩)) ∷ A ⊃ B ⊃ A ∧ B)
e13 = Rf² (Rf² (Rp² (Rx (vs vz)) (Rx vz)))

e14 : ∀{u v x y A B}
    → ⊩ ((f u ⇒ (f v ⇒ ⇑ p²⟨ u , v ⟩)) ∷ (x ∷ A) ⊃ (y ∷ B) ⊃ (! p⟨ x , y ⟩ ∷ p⟨ x , y ⟩ ∷ A ∧ B))
e14 = Rf (Rf (R⇑ (Rp² (Rx (vs vz)) (Rx vz))))


e2 : ∀{x₃ x₂ x₁ A}
   → ⊩ ((f² x₃ ⇒ ⇓² ⇑² x₃) ∷ (f x₂ ⇒ ⇓ ⇑ x₂) ∷ (x₁ ∷ A) ⊃ (x₁ ∷ A))
e2 = Rf² (R⇓² (R⇑² (Rx vz)))
