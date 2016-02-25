module AltArtemov where

open import Data.Nat using (ℕ ; _+_ ; zero ; suc)

module New where
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

  p¹⟨_,_⟩ : Tm → Tm → Tm
  p¹⟨ t , s ⟩ = p⟨ t , s ⟩# 1

  p²⟨_,_⟩ : Tm → Tm → Tm
  p²⟨ t , s ⟩ = p⟨ t , s ⟩# 2

  ⇑¹_ : Tm → Tm
  ⇑¹ t = ⇑ t # 1

  ⇓¹_ : Tm → Tm
  ⇓¹ t = ⇓ t # 1

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
       
    R∘ : ∀{n Γ t s A B}
       → Γ ⊢ t ∷ A ⊃ B → Γ ⊢ s ∷ B
       → Γ ⊢ t ∘ s # n ∷ B

    Rp : ∀{n Γ t s A B}
       → Γ ⊢ t ∷ A → Γ ⊢ s ∷ B
       → Γ ⊢ p⟨ t , s ⟩# n ∷ A ∧ B

    Rp² : ∀{Γ t₁ t₂ s₁ s₂ A B}
        → Γ ⊢ t₂ ∷ t₁ ∷ A → Γ ⊢ s₂ ∷ s₁ ∷ B
        → Γ ⊢ p²⟨ t₂ , s₂ ⟩ ∷ p¹⟨ t₁ , s₁ ⟩ ∷ A ∧ B
       
    Rπ₀ : ∀{n Γ t A B}
        → Γ ⊢ t ∷ A ∧ B
        → Γ ⊢ π₀ t # n ∷ A
        
    Rπ₁ : ∀{n Γ t A B}
        → Γ ⊢ t ∷ A ∧ B
        → Γ ⊢ π₁ t # n ∷ B
        
    R⇑ : ∀{n Γ t u A}
       → Γ ⊢ t ∷ u ∷ A
       → Γ ⊢ ⇑ t # n ∷ ! u ∷ u ∷ A

    R⇓ : ∀{n Γ t u A}
       → Γ ⊢ t ∷ u ∷ A
       → Γ ⊢ ⇓ t # n ∷ A

  module Examples where
    e1 : ∀{Γ x y A} → Γ ⊢ f¹ y ⇒ (⇓¹ y) ∷ (x ∷ A) ⊃ A
    e1 = Rf¹ (R⇓ (Rx vz))

    e2 : ∀{Γ x y A} → Γ ⊢ f¹ y ⇒ (⇑¹ y) ∷ (x ∷ A) ⊃ (! x ∷ x ∷ A)
    e2 = Rf¹ (R⇑ (Rx vz))

    e3 : ∀{Γ u v x y A B} → Γ ⊢ (f² u ⇒ (f² v ⇒ p²⟨ u , v ⟩)) ∷ (f¹ x ⇒ (f¹ y ⇒ p¹⟨ x , y ⟩)) ∷ A ⊃ B ⊃ A ∧ B
    e3 = Rf² (Rf² (Rp² (Rx (vs vz)) (Rx vz)))

    e4 : ∀{Γ u v x y A B} → Γ ⊢ (f¹ u ⇒ (f¹ v ⇒ ⇑¹ p²⟨ u , v ⟩)) ∷ ((x ∷ A) ⊃ (y ∷ B) ⊃ (! p¹⟨ x , y ⟩ ∷ p¹⟨ x , y ⟩ ∷ A ∧ B))
    e4 = Rf¹ (Rf¹ (R⇑ (Rp² (Rx (vs vz)) (Rx vz))))
