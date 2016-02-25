module AltArtemov where

open import Data.Nat using (ℕ)


infixl 5 _∧_
infixr 4 _⊃_
infixr 3 _∷_
infix 2 _,_
infix 1 _∈_
infix 0 _⊢_


data Tm : Set where
  !_       : Tm → Tm
  f_⇒_#_   : Tm → Tm → ℕ → Tm
  _∘_#_    : Tm → Tm → ℕ → Tm
  p⟨_,_⟩#_ : Tm → Tm → ℕ → Tm
  π₀_#_    : Tm → ℕ → Tm
  π₁_#_    : Tm → ℕ → Tm
  ⇑_#_     : Tm → ℕ → Tm
  ⇓_#_     : Tm → ℕ → Tm


data Ty : Set where
  ⊥   : Ty
  _∧_ : Ty → Ty → Ty
  _⊃_ : Ty → Ty → Ty
  _∷_ : Tm → Ty → Ty


data Cx : Set where
  []  : Cx
  _,_ : Cx → Ty → Cx


data _∈_ (A : Ty) : Cx → Set where
  vz : ∀{Γ} → A ∈ Γ , A
  vs : ∀{Γ}{B : Ty} → A ∈ Γ → A ∈ Γ , B


f¹_⇒_ : Tm → Tm → Tm
f¹ x ⇒ t = f x ⇒ t # 1

f²_⇒_ : Tm → Tm → Tm
f² x ⇒ t = f x ⇒ t # 2

_∘¹_ : Tm → Tm → Tm
t ∘¹ s = t ∘ s # 1

_∘²_ : Tm → Tm → Tm
t ∘² s = t ∘ s # 2

p¹⟨_,_⟩ : Tm → Tm → Tm
p¹⟨ t , s ⟩ = p⟨ t , s ⟩# 1

p²⟨_,_⟩ : Tm → Tm → Tm
p²⟨ t , s ⟩ = p⟨ t , s ⟩# 2

π₀¹_ : Tm → Tm
π₀¹ t = π₀ t # 1

π₀²_ : Tm → Tm
π₀² t = π₀ t # 2

π₁¹_ : Tm → Tm
π₁¹ t = π₁ t # 1

π₁²_ : Tm → Tm
π₁² t = π₁ t # 2

⇑¹_ : Tm → Tm
⇑¹ t = ⇑ t # 1

⇑²_ : Tm → Tm
⇑² t = ⇑ t # 2

⇓¹_ : Tm → Tm
⇓¹ t = ⇓ t # 1

⇓²_ : Tm → Tm
⇓² t = ⇓ t # 2


data _⊢_ : Cx → Ty → Set where
  Rx : ∀{Γ x A}
     → x ∷ A ∈ Γ
     → Γ ⊢ x ∷ A
     
  Rf¹ : ∀{Γ x₁ t₁ A B}
      → Γ , x₁ ∷ A ⊢ t₁ ∷ B
      → Γ ⊢ f¹ x₁ ⇒ t₁ ∷ A ⊃ B
     
  Rf² : ∀{Γ x₂ x₁ t₂ t₁ A B}
      → Γ , x₂ ∷ x₁ ∷ A ⊢ t₂ ∷ t₁ ∷ B
      → Γ ⊢ (f² x₂ ⇒ t₂) ∷ (f¹ x₁ ⇒ t₁) ∷ A ⊃ B
     
  R∘¹ : ∀{Γ t₁ s₁ A B}
      → Γ ⊢ t₁ ∷ A ⊃ B → Γ ⊢ s₁ ∷ B
      → Γ ⊢ t₁ ∘¹ s₁ ∷ B
     
  R∘² : ∀{Γ t₁ t₂ s₁ s₂ A B}
      → Γ ⊢ t₂ ∷ t₁ ∷ A ⊃ B → Γ ⊢ s₂ ∷ s₁ ∷ B
      → Γ ⊢ t₂ ∘² s₂ ∷ t₁ ∘¹ s₁ ∷ B

  Rp¹ : ∀{Γ t₁ s₁ A B}
      → Γ ⊢ t₁ ∷ A → Γ ⊢ s₁ ∷ B
      → Γ ⊢ p¹⟨ t₁ , s₁ ⟩ ∷ A ∧ B

  Rp² : ∀{Γ t₁ t₂ s₁ s₂ A B}
      → Γ ⊢ t₂ ∷ t₁ ∷ A → Γ ⊢ s₂ ∷ s₁ ∷ B
      → Γ ⊢ p²⟨ t₂ , s₂ ⟩ ∷ p¹⟨ t₁ , s₁ ⟩ ∷ A ∧ B
     
  Rπ₀¹ : ∀{Γ t₁ A B}
       → Γ ⊢ t₁ ∷ A ∧ B
       → Γ ⊢ π₀¹ t₁ ∷ A
     
  Rπ₀² : ∀{Γ t₁ t₂ A B}
       → Γ ⊢ t₂ ∷ t₁ ∷ A ∧ B
       → Γ ⊢ π₀² t₂ ∷ π₀¹ t₁ ∷ A
      
  Rπ₁¹ : ∀{Γ t₁ A B}
       → Γ ⊢ t₁ ∷ A ∧ B
       → Γ ⊢ π₁¹ t₁ ∷ B
      
  Rπ₁² : ∀{Γ t₁ t₂ A B}
       → Γ ⊢ t₂ ∷ t₁ ∷ A ∧ B
       → Γ ⊢ π₁² t₂ ∷ π₁¹ t₁ ∷ B
      
  R⇑¹ : ∀{Γ t₁ u A}
      → Γ ⊢ t₁ ∷ u ∷ A
      → Γ ⊢ ⇑¹ t₁ ∷ ! u ∷ u ∷ A
      
  R⇑² : ∀{Γ t₁ t₂ u A}
      → Γ ⊢ t₂ ∷ t₁ ∷ u ∷ A
      → Γ ⊢ ⇑² t₂ ∷ ⇑¹ t₁ ∷ ! u ∷ u ∷ A

  R⇓¹ : ∀{Γ t₁ u A}
      → Γ ⊢ t₁ ∷ u ∷ A
      → Γ ⊢ ⇓¹ t₁ ∷ A

  R⇓² : ∀{Γ t₁ t₂ u A}
      → Γ ⊢ t₂ ∷ t₁ ∷ u ∷ A
      → Γ ⊢ ⇓² t₂ ∷ ⇓¹ t₁ ∷ A


⊩_ : Ty → Set
⊩ A = ∀{Γ} → Γ ⊢ A


e1 : ∀{x y A}
   → ⊩ (f¹ y ⇒ (⇓¹ y) ∷ (x ∷ A) ⊃ A)
e1 = Rf¹ (R⇓¹ (Rx vz))

e2 : ∀{x y A}
   → ⊩ (f¹ y ⇒ (⇑¹ y) ∷ (x ∷ A) ⊃ (! x ∷ x ∷ A))
e2 = Rf¹ (R⇑¹ (Rx vz))

e3 : ∀{u v x y A B}
   → ⊩ ((f² u ⇒ (f² v ⇒ p²⟨ u , v ⟩)) ∷ (f¹ x ⇒ (f¹ y ⇒ p¹⟨ x , y ⟩)) ∷ A ⊃ B ⊃ A ∧ B)
e3 = Rf² (Rf² (Rp² (Rx (vs vz)) (Rx vz)))

e4 : ∀{u v x y A B}
   → ⊩ ((f¹ u ⇒ (f¹ v ⇒ ⇑¹ p²⟨ u , v ⟩)) ∷ ((x ∷ A) ⊃ (y ∷ B) ⊃ (! p¹⟨ x , y ⟩ ∷ p¹⟨ x , y ⟩ ∷ A ∧ B)))
e4 = Rf¹ (Rf¹ (R⇑¹ (Rp² (Rx (vs vz)) (Rx vz))))
