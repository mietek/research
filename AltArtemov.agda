{-

A partial implementation of the Alt-Artëmov system λ∞[1].

Miëtek Bak <mietek@bak.io>

Thanks to Darryl McAdams and Paolo Giarrusso for comments and discussion.

[1]: Alt, J., Artëmov, S. (2001) Reflective λ-calculus, Proceedings of the
     2001 International Seminar on Proof Theory in Computer Science (PTCS’01),
     Lecture Notes in Computer Science, vol. 2183, pp. 22–37.
     http://dx.doi.org/10.1007/3-540-45504-3_2

-}

module AltArtemov where

open import Data.Nat using (ℕ)


infixr 9 !_
infixl 8 _∘_
infixl 8 _∘²_
infixr 7 _∷_
infixr 6 ¬_
infixl 5 _∧_
infixr 4 _⊃_
infixr 3 _⊃⊂_
infix 2 _,_
infix 1 _∈_
infix 0 _⊢_
infix 0 ⊩_


-- Term judgement

data Tm : Set where
  Fⁿ_⇒_#_   : Tm → Tm → ℕ → Tm -- Originally λⁿ_._
  _∘ⁿ_#_    : Tm → Tm → ℕ → Tm
  Pⁿ⟨_,_⟩#_ : Tm → Tm → ℕ → Tm -- Originally pⁿ(_,_)
  π₀ⁿ_#_    : Tm → ℕ → Tm
  π₁ⁿ_#_    : Tm → ℕ → Tm
  ⇑ⁿ_#_     : Tm → ℕ → Tm
  ⇓ⁿ_#_     : Tm → ℕ → Tm
  !_        : Tm → Tm


-- Type judgement

data Ty : Set where
  _∧_ : Ty → Ty → Ty
  _⊃_ : Ty → Ty → Ty -- Originally _→_
  _∷_ : Tm → Ty → Ty -- Originally _∶_
  ⊥   : Ty


-- Notational definitions

⊤ : Ty
⊤ = ⊥ ⊃ ⊥

¬_ : Ty → Ty
¬ A = A ⊃ ⊥

_⊃⊂_ : Ty → Ty → Ty
A ⊃⊂ B = A ⊃ B ∧ B ⊃ A


-- Contexts

data Cx : Set where
  []  : Cx
  _,_ : Cx → Ty → Cx


-- Context membership evidence

data _∈_ (A : Ty) : Cx → Set where
  vz : ∀{Γ} → A ∈ Γ , A
  vs : ∀{Γ}{B : Ty} → A ∈ Γ → A ∈ Γ , B


-- Notation for level 1 terms

F_⇒_ : Tm → Tm → Tm
F x ⇒ t = Fⁿ x ⇒ t # 1

_∘_ : Tm → Tm → Tm
t ∘ s = t ∘ⁿ s # 1

P⟨_,_⟩ : Tm → Tm → Tm
P⟨ t , s ⟩ = Pⁿ⟨ t , s ⟩# 1

π₀_ : Tm → Tm
π₀ t = π₀ⁿ t # 1

π₁_ : Tm → Tm
π₁ t = π₁ⁿ t # 1

⇑_ : Tm → Tm
⇑ t = ⇑ⁿ t # 1

⇓_ : Tm → Tm
⇓ t = ⇓ⁿ t # 1


-- Notation for level 2 terms

F²_⇒_ : Tm → Tm → Tm
F² x ⇒ t = Fⁿ x ⇒ t # 2

_∘²_ : Tm → Tm → Tm
t ∘² s = t ∘ⁿ s # 2

P²⟨_,_⟩ : Tm → Tm → Tm
P²⟨ t , s ⟩ = Pⁿ⟨ t , s ⟩# 2

π₀²_ : Tm → Tm
π₀² t = π₀ⁿ t # 2

π₁²_ : Tm → Tm
π₁² t = π₁ⁿ t # 2

⇑²_ : Tm → Tm
⇑² t = ⇑ⁿ t # 2

⇓²_ : Tm → Tm
⇓² t = ⇓ⁿ t # 2


-- Inference rules for level 1 terms

data _⊢_ (Γ : Cx) : Ty → Set where
  Rx : ∀{x A}
     → x ∷ A ∈ Γ
     → Γ ⊢ x ∷ A

  RF : ∀{x A t B}
     → Γ , x ∷ A ⊢ t ∷ B
     → Γ ⊢ F x ⇒ t ∷ (A ⊃ B)

  R∘ : ∀{t A s B}
     → Γ ⊢ t ∷ (A ⊃ B)
     → Γ ⊢ s ∷ A
     → Γ ⊢ (t ∘ s) ∷ B

  RP : ∀{t A s B}
     → Γ ⊢ t ∷ A
     → Γ ⊢ s ∷ B
     → Γ ⊢ P⟨ t , s ⟩ ∷ (A ∧ B)

  Rπ₀ : ∀{t A B}
      → Γ ⊢ t ∷ (A ∧ B)
      → Γ ⊢ π₀ t ∷ A

  Rπ₁ : ∀{t A B}
      → Γ ⊢ t ∷ (A ∧ B)
      → Γ ⊢ π₁ t ∷ B

  R⇑ : ∀{t u A}
     → Γ ⊢ t ∷ u ∷ A
     → Γ ⊢ ⇑ t ∷ ! u ∷ u ∷ A

  R⇓ : ∀{t u A}
     → Γ ⊢ t ∷ u ∷ A
     → Γ ⊢ ⇓ t ∷ A


  -- Inference rules for level 2 terms

  Rx² : ∀{x₂ x₁ A}
     → x₂ ∷ x₁ ∷ A ∈ Γ
     → Γ ⊢ x₂ ∷ x₁ ∷ A

  RF² : ∀{x₂ x₁ A t₂ t₁ B}
      → Γ , x₂ ∷ x₁ ∷ A ⊢ t₂ ∷ t₁ ∷ B
      → Γ ⊢ F² x₂ ⇒ t₂ ∷ F x₁ ⇒ t₁ ∷ (A ⊃ B)

  R∘² : ∀{t₂ t₁ A s₂ s₁ B}
      → Γ ⊢ t₂ ∷ t₁ ∷ (A ⊃ B)
      → Γ ⊢ s₂ ∷ s₁ ∷ A
      → Γ ⊢ (t₂ ∘² s₂) ∷ (t₁ ∘ s₁) ∷ B

  RP² : ∀{t₂ t₁ A s₂ s₁ B}
      → Γ ⊢ t₂ ∷ t₁ ∷ A
      → Γ ⊢ s₂ ∷ s₁ ∷ B
      → Γ ⊢ P²⟨ t₂ , s₂ ⟩ ∷ P⟨ t₁ , s₁ ⟩ ∷ (A ∧ B)

  Rπ₀² : ∀{t₂ t₁ A B}
       → Γ ⊢ t₂ ∷ t₁ ∷ (A ∧ B)
       → Γ ⊢ π₀² t₂ ∷ π₀ t₁ ∷ A

  Rπ₁² : ∀{t₂ t₁ A B}
       → Γ ⊢ t₂ ∷ t₁ ∷ (A ∧ B)
       → Γ ⊢ π₁² t₂ ∷ π₁ t₁ ∷ B

  R⇑² : ∀{t₂ t₁ u A}
      → Γ ⊢ t₂ ∷ t₁ ∷ u ∷ A
      → Γ ⊢ ⇑² t₂ ∷ ⇑ t₁ ∷ ! u ∷ u ∷ A

  R⇓² : ∀{t₂ t₁ u A}
      → Γ ⊢ t₂ ∷ t₁ ∷ u ∷ A
      → Γ ⊢ ⇓² t₂ ∷ ⇓ t₁ ∷ A


-- TODO: Inference rules for level n terms


-- Theorems of λ∞

⊩_ : Ty → Set
⊩ A = ∀{Γ} → Γ ⊢ A


-- Example 1 (p. 28[1])

e11 : ∀{x y A}
    → ⊩ F y ⇒ ⇓ y ∷ (x ∷ A ⊃ A)
e11 = RF (R⇓ (Rx vz))

e12 : ∀{x y A}
    → ⊩ F y ⇒ ⇑ y ∷ (x ∷ A ⊃ ! x ∷ x ∷ A)
e12 = RF (R⇑ (Rx vz))

e13 : ∀{u x A v y B}
    → ⊩ F² u ⇒ F² v ⇒ P²⟨ u , v ⟩ ∷ F x ⇒ F y ⇒ P⟨ x , y ⟩ ∷ (A ⊃ B ⊃ A ∧ B)
e13 = RF² (RF² (RP² (Rx (vs vz))
                    (Rx vz)))

e14 : ∀{u x A v y B}
    → ⊩ F u ⇒ F v ⇒ ⇑ P²⟨ u , v ⟩ ∷ (x ∷ A ⊃ y ∷ B ⊃ ! P⟨ x , y ⟩ ∷ P⟨ x , y ⟩ ∷ (A ∧ B))
e14 = RF (RF (R⇑ (RP² (Rx (vs vz))
                      (Rx vz))))


-- Example 2 (pp. 31–32[1])

e2a : ∀{x₃ x₂ x₁ A}
    → ⊩ F² x₃ ⇒ ⇓² ⇑² x₃ ∷ F x₂ ⇒ ⇓ ⇑ x₂ ∷ (x₁ ∷ A ⊃ x₁ ∷ A)
e2a = RF² (R⇓² (R⇑² (Rx vz)))

e2b : ∀{x₃ x₂ x₁ A}
    → ⊩ F² x₃ ⇒ x₃ ∷ F x₂ ⇒ x₂ ∷ (x₁ ∷ A ⊃ x₁ ∷ A)
e2b = RF² (Rx vz)
