{-

A partial implementation of the Alt-Artëmov system λ∞[1].

Miëtek Bak <mietek@bak.io>

Thanks to Darryl McAdams and Paolo Giarrusso for comments and discussion.

For easy editing with Emacs agda-mode, add to your .emacs file:
 '(agda-input-user-translations
   (quote
    (("if" "⊃") ("iff" "⊃⊂") ("not" "¬") ("ent" "⊢")
     ("v" "𝜈") ("v1" "𝜈") ("v2" "𝜈²") ("vn" "𝜈ⁿ")
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
open import Data.Product using (_×_)

infixl 8 _∘_ _∘²_
infixr 7 ⇓_ ⇓²_ ⇑_ ⇑²_ !_ 𝜈_ 𝜈²_
infixr 6 𝜆_．_ 𝜆²_．_ _∶_
infixr 5 ¬_
infixl 4 _∧_
infixr 3 _⊃_ _⊃⊂_
infixl 2 _,_
infixr 1 _∈_
infixr 0 _⊢_



-- Term judgement

mutual
  Var : Set
  Var = ℕ × Ty
  
  data Tm : Set where
    𝜈ⁿ_#_     : Var → ℕ → Tm
    𝜆ⁿ_．_#_   : Var → Tm → ℕ → Tm
    _∘ⁿ_#_    : Tm → Tm → ℕ → Tm
    𝗽ⁿ⟨_,_⟩#_ : Tm → Tm → ℕ → Tm
    𝛑₀ⁿ_#_    : Tm → ℕ → Tm
    𝛑₁ⁿ_#_    : Tm → ℕ → Tm
    !_        : Tm → Tm
    ⇑ⁿ_#_     : Tm → ℕ → Tm
    ⇓ⁿ_#_     : Tm → ℕ → Tm


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
  Z : ∀{Γ}   → A ∈ Γ , A
  S : ∀{Γ B} → A ∈ Γ
             → A ∈ Γ , B


-- Notation for level 1 terms

𝜈_ : Var → Tm
𝜈 x = 𝜈ⁿ x # 1

𝜆_．_ : Var → Tm → Tm
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

𝜈²_ : Var → Tm
𝜈² x = 𝜈ⁿ x # 2

𝜆²_．_ : Var → Tm → Tm
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
  R𝜈 : ∀{x : Var}{A}
     → 𝜈 x ∶ A ∈ Γ
     → Γ ⊢ 𝜈 x ∶ A

  R𝜆 : ∀{x : Var}{A t B}
     → Γ , 𝜈 x ∶ A ⊢ t ∶ B
     → Γ ⊢ 𝜆 x ． t ∶ (A ⊃ B)

  R∘ : ∀{t A s B}
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

  R𝜈² : ∀{x₂ x₁ : Var}{A}
      → 𝜈² x₂ ∶ 𝜈 x₁ ∶ A ∈ Γ
      → Γ ⊢ 𝜈² x₂ ∶ 𝜈 x₁ ∶ A

  R𝜆² : ∀{x₂ x₁ : Var}{A t₂ t₁ B}
      → Γ , 𝜈² x₂ ∶ 𝜈 x₁ ∶ A ⊢ t₂ ∶ t₁ ∶ B
      → Γ ⊢ 𝜆² x₂ ． t₂ ∶ 𝜆 x₁ ． t₁ ∶ (A ⊃ B)

  R∘² : ∀{t₂ t₁ A s₂ s₁ B}
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

e1₁ : ∀{Γ}{x y : Var}{A}
    → Γ ⊢ 𝜆 y ． ⇓ 𝜈 y ∶ (𝜈 x ∶ A ⊃ A)
e1₁ = R𝜆 (R⇓ (R𝜈 Z))

e1₂ : ∀{Γ}{x y : Var}{A}
    → Γ ⊢ 𝜆 y ． ⇑ 𝜈 y ∶ (𝜈 x ∶ A ⊃ ! (𝜈 x) ∶ 𝜈 x ∶ A)
e1₂ = R𝜆 (R⇑ (R𝜈 Z))

e1₃ : ∀{Γ}{u x : Var}{A}{v y : Var}{B}
    → Γ ⊢ 𝜆² u ． 𝜆² v ． 𝗽²⟨ 𝜈² u , 𝜈² v ⟩ ∶ 𝜆 x ． 𝜆 y ． 𝗽⟨ 𝜈 x , 𝜈 y ⟩ ∶ (A ⊃ B ⊃ A ∧ B)
e1₃ = R𝜆² (R𝜆² (R𝗽² (R𝜈² (S Z))
                    (R𝜈² Z)))

e1₄ : ∀{Γ}{u x : Var}{A}{v y : Var}{B}
    → Γ ⊢ 𝜆 u ． 𝜆 v ． ⇑ 𝗽²⟨ 𝜈 u , 𝜈 v ⟩ ∶ (𝜈 x ∶ A ⊃ 𝜈 y ∶ B ⊃ ! 𝗽⟨ 𝜈 x , 𝜈 y ⟩ ∶ 𝗽⟨ 𝜈 x , 𝜈 y ⟩ ∶ (A ∧ B))
e1₄ = R𝜆 (R𝜆 (R⇑ (R𝗽² (R𝜈 (S Z))
                      (R𝜈 Z))))


-- Example 2 (pp. 31–32[1])

e2 : ∀{Γ}{x₃ x₂ x₁ : Var}{A}
   → Γ ⊢ 𝜆² x₃ ． ⇓² ⇑² 𝜈² x₃ ∶ 𝜆 x₂ ． ⇓ ⇑ 𝜈 x₂ ∶ (𝜈 x₁ ∶ A ⊃ 𝜈 x₁ ∶ A)
e2 = R𝜆² (R⇓² (R⇑² (R𝜈² Z)))

e2' : ∀{Γ}{x₃ x₂ x₁ : Var}{A}
    → Γ ⊢ 𝜆² x₃ ． 𝜈² x₃ ∶ 𝜆 x₂ ． 𝜈 x₂ ∶ (𝜈 x₁ ∶ A ⊃ 𝜈 x₁ ∶ A)
e2' = R𝜆² (R𝜈² Z)
