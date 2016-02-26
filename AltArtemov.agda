{-

A partial implementation of the Alt-Artëmov system λ∞[1].

Miëtek Bak <mietek@bak.io>

Thanks to Darryl McAdams and Paolo Giarrusso for comments and discussion.

For easy editing with the Emacs agda-mode:
 '(agda-input-user-translations
   (quote
    (("if" "⊃") ("iff" "⊃⊂") ("not" "¬") ("ent" "⊢")
     ("l" "𝜆") ("l1" "𝜆") ("l2" "𝜆²") ("ln" "𝜆ⁿ") ("." "．")
     ("o" "∘") ("o1" "∘") ("o2" "∘²") ("on" "∘ⁿ")
     ("p" "𝗽") ("p1" "𝗽") ("p2" "𝗽²") ("pn" "𝗽ⁿ")
     ("pi0" "𝛑₀") ("pi01" "𝛑₀") ("pi02" "𝛑₀²") ("pi0n" "𝛑₀ⁿ")
     ("pi1" "𝛑₁") ("pi11" "𝛑₁") ("pi12" "𝛑₁²") ("pi1n" "𝛑₁ⁿ")
     ("u" "⇑") ("u1" "⇑") ("u2" "⇑²") ("un" "⇑ⁿ")
     ("d" "⇓") ("d1" "⇓") ("d2" "⇓²") ("dn" "⇓ⁿ"))))

[1]: Alt, J., Artëmov, S. (2001) Reflective λ-calculus, Proceedings of the
     2001 International Seminar on Proof Theory in Computer Science (PTCS’01),
     Lecture Notes in Computer Science, vol. 2183, pp. 22–37.
     http://dx.doi.org/10.1007/3-540-45504-3_2

-}


module AltArtemov where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


infixr 9 !_
infixl 8 _∘_
infixl 8 _∘²_
infixr 7 _∶_
infixr 6 ¬_
infixl 5 _∧_
infixr 4 _⊃_
infixr 3 _⊃⊂_
infix 2 _,_
infix 1 _∈_
infix 0 _⊢_


-- Term judgement

data Tm : Set where
  𝜆ⁿ_．_#_   : Tm → Tm → ℕ → Tm
  _∘ⁿ_#_    : Tm → Tm → ℕ → Tm
  𝗽ⁿ⟨_,_⟩#_ : Tm → Tm → ℕ → Tm
  𝛑₀ⁿ_#_    : Tm → ℕ → Tm
  𝛑₁ⁿ_#_    : Tm → ℕ → Tm
  ⇑ⁿ_#_     : Tm → ℕ → Tm
  ⇓ⁿ_#_     : Tm → ℕ → Tm
  !_        : Tm → Tm


-- Type judgement

data Ty : Set where
  _∧_ : Ty → Ty → Ty
  _⊃_ : Ty → Ty → Ty
  _∶_ : Tm → Ty → Ty
  ⊥   : Ty


-- Notational definitions

_⊃⊂_ : Ty → Ty → Ty
A ⊃⊂ B = A ⊃ B ∧ B ⊃ A

¬_ : Ty → Ty
¬ A = A ⊃ ⊥

⊤ : Ty
⊤ = ⊥ ⊃ ⊥


-- Contexts

data Cx : Set where
  ∅   : Cx
  _,_ : Cx → Ty → Cx


-- Context membership evidence

data _∈_ (A : Ty) : Cx → Set where
  vz : ∀{Γ} → A ∈ Γ , A
  vs : ∀{Γ}{B : Ty} → A ∈ Γ → A ∈ Γ , B


-- Notation for level 1 terms

𝜆_．_ : Tm → Tm → Tm
𝜆 x ． t = 𝜆ⁿ x ． t # 1

_∘_ : Tm → Tm → Tm
t ∘ s = t ∘ⁿ s # 1

𝗽⟨_,_⟩ : Tm → Tm → Tm
𝗽⟨ t , s ⟩ = 𝗽ⁿ⟨ t , s ⟩# 1

𝛑₀_ : Tm → Tm
𝛑₀ t = 𝛑₀ⁿ t # 1

𝛑₁_ : Tm → Tm
𝛑₁ t = 𝛑₁ⁿ t # 1

⇑_ : Tm → Tm
⇑ t = ⇑ⁿ t # 1

⇓_ : Tm → Tm
⇓ t = ⇓ⁿ t # 1


-- Notation for level 2 terms

𝜆²_．_ : Tm → Tm → Tm
𝜆² x ． t = 𝜆ⁿ x ． t # 2

_∘²_ : Tm → Tm → Tm
t ∘² s = t ∘ⁿ s # 2

𝗽²⟨_,_⟩ : Tm → Tm → Tm
𝗽²⟨ t , s ⟩ = 𝗽ⁿ⟨ t , s ⟩# 2

𝛑₀²_ : Tm → Tm
𝛑₀² t = 𝛑₀ⁿ t # 2

𝛑₁²_ : Tm → Tm
𝛑₁² t = 𝛑₁ⁿ t # 2

⇑²_ : Tm → Tm
⇑² t = ⇑ⁿ t # 2

⇓²_ : Tm → Tm
⇓² t = ⇓ⁿ t # 2


-- Inference rules for level 1 terms

data _⊢_ (Γ : Cx) : Ty → Set where
  RAx : ∀{x A}
      → x ∶ A ∈ Γ
      → Γ ⊢ x ∶ A

  R𝜆 : ∀{x A t B}
     → Γ , x ∶ A ⊢ t ∶ B
     → Γ ⊢ 𝜆 x ． t ∶ (A ⊃ B)

  RApp : ∀{t A s B}
       → Γ ⊢ t ∶ (A ⊃ B)
       → Γ ⊢ s ∶ A
       → Γ ⊢ (t ∘ s) ∶ B

  R𝗽 : ∀{t A s B}
     → Γ ⊢ t ∶ A
     → Γ ⊢ s ∶ B
     → Γ ⊢ 𝗽⟨ t , s ⟩ ∶ (A ∧ B)

  R𝛑₀ : ∀{t A B}
      → Γ ⊢ t ∶ (A ∧ B)
      → Γ ⊢ 𝛑₀ t ∶ A

  R𝛑₁ : ∀{t A B}
      → Γ ⊢ t ∶ (A ∧ B)
      → Γ ⊢ 𝛑₁ t ∶ B

  R⇑ : ∀{t u A}
     → Γ ⊢ t ∶ u ∶ A
     → Γ ⊢ ⇑ t ∶ ! u ∶ u ∶ A

  R⇓ : ∀{t u A}
     → Γ ⊢ t ∶ u ∶ A
     → Γ ⊢ ⇓ t ∶ A


  -- Inference rules for level 2 terms

  RAx² : ∀{x₂ x₁ A}
       → x₂ ∶ x₁ ∶ A ∈ Γ
       → Γ ⊢ x₂ ∶ x₁ ∶ A

  R𝜆² : ∀{x₂ x₁ A t₂ t₁ B}
      → Γ , x₂ ∶ x₁ ∶ A ⊢ t₂ ∶ t₁ ∶ B
      → Γ ⊢ 𝜆² x₂ ． t₂ ∶ 𝜆 x₁ ． t₁ ∶ (A ⊃ B)

  RApp² : ∀{t₂ t₁ A s₂ s₁ B}
        → Γ ⊢ t₂ ∶ t₁ ∶ (A ⊃ B)
        → Γ ⊢ s₂ ∶ s₁ ∶ A
        → Γ ⊢ (t₂ ∘² s₂) ∶ (t₁ ∘ s₁) ∶ B

  R𝗽² : ∀{t₂ t₁ A s₂ s₁ B}
      → Γ ⊢ t₂ ∶ t₁ ∶ A
      → Γ ⊢ s₂ ∶ s₁ ∶ B
      → Γ ⊢ 𝗽²⟨ t₂ , s₂ ⟩ ∶ 𝗽⟨ t₁ , s₁ ⟩ ∶ (A ∧ B)

  R𝛑₀² : ∀{t₂ t₁ A B}
       → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
       → Γ ⊢ 𝛑₀² t₂ ∶ 𝛑₀ t₁ ∶ A

  R𝛑₁² : ∀{t₂ t₁ A B}
       → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
       → Γ ⊢ 𝛑₁² t₂ ∶ 𝛑₁ t₁ ∶ B

  R⇑² : ∀{t₂ t₁ u A}
      → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
      → Γ ⊢ ⇑² t₂ ∶ ⇑ t₁ ∶ ! u ∶ u ∶ A

  R⇓² : ∀{t₂ t₁ u A}
      → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
      → Γ ⊢ ⇓² t₂ ∶ ⇓ t₁ ∶ A


-- TODO: Inference rules for level n terms


-- Example 1 (p. 28[1])

e11 : ∀{Γ x y A}
    → Γ ⊢ 𝜆 y ． ⇓ y ∶ (x ∶ A ⊃ A)
e11 = R𝜆 (R⇓ (RAx vz))

e12 : ∀{Γ x y A}
    → Γ ⊢ 𝜆 y ． ⇑ y ∶ (x ∶ A ⊃ ! x ∶ x ∶ A)
e12 = R𝜆 (R⇑ (RAx vz))

e13 : ∀{Γ u x A v y B}
    → Γ ⊢ 𝜆² u ． 𝜆² v ． 𝗽²⟨ u , v ⟩ ∶ 𝜆 x ． 𝜆 y ． 𝗽⟨ x , y ⟩ ∶ (A ⊃ B ⊃ A ∧ B)
e13 = R𝜆² (R𝜆² (R𝗽² (RAx (vs vz))
                    (RAx vz)))

e14 : ∀{Γ u x A v y B}
    → Γ ⊢ 𝜆 u ． 𝜆 v ． ⇑ 𝗽²⟨ u , v ⟩ ∶ (x ∶ A ⊃ y ∶ B ⊃ ! 𝗽⟨ x , y ⟩ ∶ 𝗽⟨ x , y ⟩ ∶ (A ∧ B))
e14 = R𝜆 (R𝜆 (R⇑ (R𝗽² (RAx (vs vz))
                      (RAx vz))))


-- Example 2 (pp. 31–32[1])

e2a : ∀{Γ x₃ x₂ x₁ A}
    → Γ ⊢ 𝜆² x₃ ． ⇓² ⇑² x₃ ∶ 𝜆 x₂ ． ⇓ ⇑ x₂ ∶ (x₁ ∶ A ⊃ x₁ ∶ A)
e2a = R𝜆² (R⇓² (R⇑² (RAx vz)))

e2b : ∀{Γ x₃ x₂ x₁ A}
    → Γ ⊢ 𝜆² x₃ ． x₃ ∶ 𝜆 x₂ ． x₂ ∶ (x₁ ∶ A ⊃ x₁ ∶ A)
e2b = R𝜆² (RAx vz)
