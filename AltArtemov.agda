{-

A partial implementation of the Alt-Artëmov system λ∞[1].

Miëtek Bak <mietek@bak.io>

Thanks to Darryl McAdams and Paolo Giarrusso for comments and discussion.

For easy editing with Emacs agda-mode, add to your .emacs file:
 '(agda-input-user-translations
   (quote
    (("imp" "⊃") ("iff" "⊃⊂") ("not" "¬") ("ent" "⊢") ("thm" "⊩") ("N" "ℕ")
     ("s" "𝒔") ("t" "𝒕") ("x" "𝒙") ("y" "𝒚")
     ("v" "𝑣") ("v1" "𝑣") ("v2" "𝑣²") ("vn" "𝑣ⁿ")
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

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_)

infixl 9 _∘_ _∘²_ _∘ⁿ_#_ 
infixr 8 𝑣_ !_ ⇓_ ⇑_ ⇓²_ ⇑²_ ⇓ⁿ_#_ ⇑ⁿ_#_ 
infixr 7 𝜆_．_ 𝜆²_．_ 𝜆ⁿ_．_#_
infixr 6 _∶_
infixr 5 ¬_
infixl 4 _∧_
infixr 3 _⊃_ _⊃⊂_
infixl 2 _,_
infixr 1 _∈_
infixr 0 _⊢_ ⊩_


mutual

  -- Variables

  Var : Set
  Var = ℕ × Ty


  -- Terms

  data Tm : Set where
    𝑣_        : (x : Var)                  → Tm    -- Variable
    𝜆ⁿ_．_#_   : (x : Var) (t : Tm) (n : ℕ) → Tm    -- Abstraction
    _∘ⁿ_#_    : (t s : Tm)         (n : ℕ) → Tm    -- Application
    𝗽ⁿ⟨_,_⟩#_ : (t s : Tm)         (n : ℕ) → Tm    -- Pairing
    𝛑₀ⁿ_#_    : (t : Tm)           (n : ℕ) → Tm    -- Left projection
    𝛑₁ⁿ_#_    : (t : Tm)           (n : ℕ) → Tm    -- Right projection
    !_        : (t : Tm)                   → Tm    -- Proof checking
    ⇑ⁿ_#_     : (t : Tm)           (n : ℕ) → Tm    -- Reification
    ⇓ⁿ_#_     : (t : Tm)           (n : ℕ) → Tm    -- Reflection


  -- Types

  data Ty : Set where
    ⊥   :                     Ty    -- Falsehood
    _⊃_ : (A B : Ty)        → Ty    -- Implication
    _∧_ : (A B : Ty)        → Ty    -- Conjunction
    _∶_ : (x : Tm) (A : Ty) → Ty    -- Provability


-- Additional types

⊤ : Ty                    -- Truth
⊤ = ⊥ ⊃ ⊥

¬_ : (A : Ty) → Ty        -- Negation
¬ A = A ⊃ ⊥

_⊃⊂_ : (A B : Ty) → Ty    -- Equivalence
A ⊃⊂ B = A ⊃ B ∧ B ⊃ A


-- Term vectors

data TmV : ℕ → Set where
  _∶⋯ : (t₁ : Tm)                     → TmV zero
  _∶_ : (tₙ : Tm) {n : ℕ} (𝒕 : TmV n) → TmV (suc n)

V_∶_ : {n : ℕ} (𝒕 : TmV n) (A : Ty) → Ty
V t₁ ∶⋯  ∶ A = t₁ ∶ A
V tₙ ∶ 𝒕 ∶ A = tₙ ∶ V 𝒕 ∶ A


-- Variable vectors

data VarV : ℕ → Set where
  _∶⋯ : (x₁ : Var)                      → VarV zero
  _∶_ : (xₙ : Var) {n : ℕ} (𝒙 : VarV n) → VarV (suc n)

V𝑣_∶_ : {n : ℕ} (𝒙 : VarV n) (A : Ty) → Ty
V𝑣 x₁ ∶⋯  ∶ A = 𝑣 x₁ ∶ A
V𝑣 xₙ ∶ 𝒙 ∶ A = 𝑣 xₙ ∶ V𝑣 𝒙 ∶ A


-- Abstraction vectors

V𝜆ⁿ_．_∶_ : {n : ℕ} (𝒙 : VarV n) (𝒕 : TmV n) (A : Ty) → Ty
V𝜆ⁿ_．_∶_ {zero}  (x₁ ∶⋯)  (t₁ ∶⋯)  A = 𝜆ⁿ x₁ ． t₁ # zero  ∶ A
V𝜆ⁿ_．_∶_ {suc n} (xₙ ∶ 𝒙) (tₙ ∶ 𝒕) A = 𝜆ⁿ xₙ ． tₙ # suc n ∶ V𝜆ⁿ 𝒙 ． 𝒕 ∶ A


-- Application vectors

_V∘ⁿ_∶_ : {n : ℕ} (𝒕 𝒔 : TmV n) (A : Ty) → Ty
_V∘ⁿ_∶_ {zero}  (t₁ ∶⋯)  (s₁ ∶⋯)  A = t₁ ∘ⁿ s₁ # zero  ∶ A
_V∘ⁿ_∶_ {suc n} (tₙ ∶ 𝒕) (sₙ ∶ 𝒔) A = tₙ ∘ⁿ sₙ # suc n ∶ 𝒕 V∘ⁿ 𝒔 ∶ A


-- Conjunction vectors

V𝗽ⁿ⟨_,_⟩∶_ : {n : ℕ} (𝒕 𝒔 : TmV n) (A : Ty) → Ty
V𝗽ⁿ⟨_,_⟩∶_ {zero}  (t₁ ∶⋯)  (s₁ ∶⋯)  A = 𝗽ⁿ⟨ t₁ , s₁ ⟩# zero  ∶ A
V𝗽ⁿ⟨_,_⟩∶_ {suc n} (tₙ ∶ 𝒕) (sₙ ∶ 𝒔) A = 𝗽ⁿ⟨ tₙ , sₙ ⟩# suc n ∶ V𝗽ⁿ⟨ 𝒕 , 𝒔 ⟩∶ A


-- Left projection vectors

V𝛑₀ⁿ_∶_ : {n : ℕ} (𝒕 : TmV n) (A : Ty) → Ty
V𝛑₀ⁿ_∶_ {zero}  (t₁ ∶⋯)  A = 𝛑₀ⁿ t₁ # zero  ∶ A
V𝛑₀ⁿ_∶_ {suc n} (tₙ ∶ 𝒕) A = 𝛑₀ⁿ tₙ # suc n ∶ V𝛑₀ⁿ 𝒕 ∶ A


-- Right projection vectors

V𝛑₁ⁿ_∶_ : {n : ℕ} (𝒕 : TmV n) (A : Ty) → Ty
V𝛑₁ⁿ_∶_ {zero}  (t₁ ∶⋯)  A = 𝛑₁ⁿ t₁ # zero  ∶ A
V𝛑₁ⁿ_∶_ {suc n} (tₙ ∶ 𝒕) A = 𝛑₁ⁿ tₙ # suc n ∶ V𝛑₁ⁿ 𝒕 ∶ A


-- Reification vectors

V⇑ⁿ_∶_ : {n : ℕ} (𝒕 : TmV n) (A : Ty) → Ty
V⇑ⁿ_∶_ {zero}  (t₁ ∶⋯)  A = ⇑ⁿ t₁ # zero  ∶ A
V⇑ⁿ_∶_ {suc n} (tₙ ∶ 𝒕) A = ⇑ⁿ tₙ # suc n ∶ V⇑ⁿ 𝒕 ∶ A


-- Reflection vectors

V⇓ⁿ_∶_ : {n : ℕ} (𝒕 : TmV n) (A : Ty) → Ty
V⇓ⁿ_∶_ {zero}  (t₁ ∶⋯)  A = ⇓ⁿ t₁ # zero  ∶ A
V⇓ⁿ_∶_ {suc n} (tₙ ∶ 𝒕) A = ⇓ⁿ tₙ # suc n ∶ V⇓ⁿ 𝒕 ∶ A


-- Contexts

data Cx : Set where
  ∅   :           Cx
  _,_ : Cx → Ty → Cx


-- Context membership evidence

data _∈_ (A : Ty) : Cx → Set where
  Z : {Γ : Cx}                  → A ∈ Γ , A
  S : {Γ : Cx} {B : Ty} → A ∈ Γ → A ∈ Γ , B


-- Typing rules

data _⊢_ (Γ : Cx) : Ty → Set where
  R𝑣ⁿ  : {n : ℕ} {𝒙 : VarV n} {A : Ty}
       → V𝑣 𝒙 ∶ A ∈ Γ
       → Γ ⊢ V𝑣 𝒙 ∶ A

  R𝜆ⁿ  : {n : ℕ} {𝒙 : VarV n} {𝒕 : TmV n} {A B : Ty}
       → Γ , V𝑣 𝒙 ∶ A ⊢ V 𝒕 ∶ B
       → Γ ⊢ V𝜆ⁿ 𝒙 ． 𝒕 ∶ (A ⊃ B)

  R∘ⁿ  : {n : ℕ} {𝒕 𝒔 : TmV n} {A B : Ty}
       → Γ ⊢ V 𝒕 ∶ (A ⊃ B)    → Γ ⊢ V 𝒔 ∶ A
       → Γ ⊢ 𝒕 V∘ⁿ 𝒔 ∶ B

  R𝗽ⁿ  : {n : ℕ} {𝒕 𝒔 : TmV n} {A B : Ty}
       → Γ ⊢ V 𝒕 ∶ A    → Γ ⊢ V 𝒔 ∶ B
       → Γ ⊢ V𝗽ⁿ⟨ 𝒕 , 𝒔 ⟩∶ (A ∧ B)

  R𝛑₀ⁿ : {n : ℕ} {𝒕 : TmV n} {A B : Ty}
       → Γ ⊢ V 𝒕 ∶ (A ∧ B)
       → Γ ⊢ V𝛑₀ⁿ 𝒕 ∶ A

  R𝛑₁ⁿ : {n : ℕ} {𝒕 : TmV n} {A B : Ty}
       → Γ ⊢ V 𝒕 ∶ (A ∧ B)
       → Γ ⊢ V𝛑₁ⁿ 𝒕 ∶ B

  R⇑ⁿ  : {n : ℕ} {𝒕 : TmV n} {u : Tm} {A : Ty}
       → Γ ⊢ V 𝒕 ∶ (u ∶ A)
       → Γ ⊢ V⇑ⁿ 𝒕 ∶ (! u ∶ u ∶ A)

  R⇓ⁿ  : {n : ℕ} {𝒕 : TmV n} {u : Tm} {A : Ty}
       → Γ ⊢ V 𝒕 ∶ (u ∶ A)
       → Γ ⊢ V⇓ⁿ 𝒕 ∶ A


-- Theorems

⊩_  : (A : Ty) → Set
⊩ A = {Γ : Cx} → Γ ⊢ A


-- Notation for level 1 terms

𝜆_．_ : (x : Var) (t : Tm) → Tm
𝜆 x ． t = 𝜆ⁿ x ． t # 0

_∘_ : (t s : Tm) → Tm
t ∘ s = t ∘ⁿ s # 0

𝗽⟨_,_⟩ : (t s : Tm) → Tm
𝗽⟨ t , s ⟩ = 𝗽ⁿ⟨ t , s ⟩# 0

𝛑₀_ : (t : Tm) → Tm
𝛑₀ t = 𝛑₀ⁿ t # 0

𝛑₁_ : (t : Tm) → Tm
𝛑₁ t = 𝛑₁ⁿ t # 0

⇑_ : (t : Tm) → Tm
⇑ t = ⇑ⁿ t # 0

⇓_ : (t : Tm) → Tm
⇓ t = ⇓ⁿ t # 0


-- Notation for level 2 terms

𝜆²_．_ : (x : Var) (t : Tm) → Tm
𝜆² x ． t = 𝜆ⁿ x ． t # 1

_∘²_ : (t s : Tm) → Tm
t ∘² s = t ∘ⁿ s # 1

𝗽²⟨_,_⟩ : (t s : Tm) → Tm
𝗽²⟨ t , s ⟩ = 𝗽ⁿ⟨ t , s ⟩# 1

𝛑₀²_ : (t : Tm) → Tm
𝛑₀² t = 𝛑₀ⁿ t # 1

𝛑₁²_ : (t : Tm) → Tm
𝛑₁² t = 𝛑₁ⁿ t # 1

⇑²_ : (t : Tm) → Tm
⇑² t = ⇑ⁿ t # 1

⇓²_ : (t : Tm) → Tm
⇓² t = ⇓ⁿ t # 1


-- Notation for level 1 typing rules

R𝑣 : {x : Var} {A : Ty} {Γ : Cx}
   → 𝑣 x ∶ A ∈ Γ
   → Γ ⊢ 𝑣 x ∶ A
R𝑣 {x} e = R𝑣ⁿ {𝒙 = x ∶⋯} e

R𝜆 : {x : Var} {t : Tm} {A B : Ty} {Γ : Cx}
   → Γ , 𝑣 x ∶ A ⊢ t ∶ B
   → Γ ⊢ 𝜆 x ． t ∶ (A ⊃ B)
R𝜆 {x} {t} e = R𝜆ⁿ {𝒙 = x ∶⋯} {𝒕 = t ∶⋯} e

R∘ : {t s : Tm} {A B : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ (A ⊃ B)    → Γ ⊢ s ∶ A
   → Γ ⊢ t ∘ s ∶ B
R∘ {t} {s} e f = R∘ⁿ {𝒕 = t ∶⋯} {𝒔 = s ∶⋯} e f

R𝗽 : {t s : Tm} {A B : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ A    → Γ ⊢ s ∶ B
   → Γ ⊢ 𝗽⟨ t , s ⟩ ∶ (A ∧ B)
R𝗽 {t} {s} e f = R𝗽ⁿ {𝒕 = t ∶⋯} {𝒔 = s ∶⋯} e f

R𝛑₀ : {t : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝛑₀ t ∶ A
R𝛑₀ {t} e = R𝛑₀ⁿ {𝒕 = t ∶⋯} e

R𝛑₁ : {t : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ 𝛑₁ t ∶ B
R𝛑₁ {t} e = R𝛑₁ⁿ {𝒕 = t ∶⋯} e

R⇑ : {t u : Tm} {A : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ u ∶ A
   → Γ ⊢ ⇑ t ∶ ! u ∶ u ∶ A
R⇑ {t} e = R⇑ⁿ {𝒕 = t ∶⋯} e

R⇓ : {t u : Tm} {A : Ty} {Γ : Cx}
   → Γ ⊢ t ∶ u ∶ A
   → Γ ⊢ ⇓ t ∶ A
R⇓ {t} e = R⇓ⁿ {𝒕 = t ∶⋯} e


-- Notation for level 2 typing rules

R𝑣² : {x₂ x₁ : Var} {A : Ty} {Γ : Cx}
    → 𝑣 x₂ ∶ 𝑣 x₁ ∶ A ∈ Γ
    → Γ ⊢ 𝑣 x₂ ∶ 𝑣 x₁ ∶ A
R𝑣² {x₂} {x₁} = R𝑣ⁿ {𝒙 = x₂ ∶ x₁ ∶⋯}

R𝜆² : {x₂ x₁ : Var} {t₂ t₁ : Tm} {A B : Ty} {Γ : Cx}
    → Γ , 𝑣 x₂ ∶ 𝑣 x₁ ∶ A ⊢ t₂ ∶ t₁ ∶ B
    → Γ ⊢ 𝜆² x₂ ． t₂ ∶ 𝜆 x₁ ． t₁ ∶ (A ⊃ B)
R𝜆² {x₂} {x₁} {t₂} {t₁} = R𝜆ⁿ {𝒙 = x₂ ∶ x₁ ∶⋯} {𝒕 = t₂ ∶ t₁ ∶⋯}

R∘² : {t₂ t₁ s₂ s₁ : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ (A ⊃ B)    → Γ ⊢ s₂ ∶ s₁ ∶ A
    → Γ ⊢ t₂ ∘² s₂ ∶ t₁ ∘ s₁ ∶ B
R∘² {t₂} {t₁} {s₂} {s₁} = R∘ⁿ {𝒕 = t₂ ∶ t₁ ∶⋯} {𝒔 = s₂ ∶ s₁ ∶⋯}

R𝗽² : {t₂ t₁ s₂ s₁ : Tm} {A B : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ A    → Γ ⊢ s₂ ∶ s₁ ∶ B
    → Γ ⊢ 𝗽²⟨ t₂ , s₂ ⟩ ∶ 𝗽⟨ t₁ , s₁ ⟩ ∶ (A ∧ B)
R𝗽² {t₂} {t₁} {s₂} {s₁} = R𝗽ⁿ {𝒕 = t₂ ∶ t₁ ∶⋯} {𝒔 = s₂ ∶ s₁ ∶⋯}

R𝛑₀² : {t₂ t₁ : Tm} {A B : Ty} {Γ : Cx}
     → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
     → Γ ⊢ 𝛑₀² t₂ ∶ 𝛑₀ t₁ ∶ A
R𝛑₀² {t₂} {t₁} = R𝛑₀ⁿ {𝒕 = t₂ ∶ t₁ ∶⋯}

R𝛑₁² : {t₂ t₁ : Tm} {A B : Ty} {Γ : Cx}
     → Γ ⊢ t₂ ∶ t₁ ∶ (A ∧ B)
     → Γ ⊢ 𝛑₁² t₂ ∶ 𝛑₁ t₁ ∶ B
R𝛑₁² {t₂} {t₁} = R𝛑₁ⁿ {𝒕 = t₂ ∶ t₁ ∶⋯}

R⇑² : {t₂ t₁ u : Tm} {A : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇑² t₂ ∶ ⇑ t₁ ∶ ! u ∶ u ∶ A
R⇑² {t₂} {t₁} = R⇑ⁿ {𝒕 = t₂ ∶ t₁ ∶⋯}

R⇓² : {t₂ t₁ u : Tm} {A : Ty} {Γ : Cx}
    → Γ ⊢ t₂ ∶ t₁ ∶ u ∶ A
    → Γ ⊢ ⇓² t₂ ∶ ⇓ t₁ ∶ A
R⇓² {t₂} {t₁} = R⇓ⁿ {𝒕 = t₂ ∶ t₁ ∶⋯}


----

-- Examples

-- Example 1 (p. 28[1])

e1₁ : {x y : Var} {A : Ty}
    → ⊩ 𝜆 y ． ⇓ 𝑣 y ∶ (𝑣 x ∶ A ⊃ A)
e1₁ = R𝜆 (R⇓ (R𝑣 Z))

e1₂ : {x y : Var} {A : Ty}
    → ⊩ 𝜆 y ． ⇑ 𝑣 y ∶ (𝑣 x ∶ A ⊃ ! 𝑣 x ∶ 𝑣 x ∶ A)
e1₂ = R𝜆 (R⇑ (R𝑣 Z))

e1₃ : {u x v y : Var} {A B : Ty}
    → ⊩ 𝜆² u ． 𝜆² v ． 𝗽²⟨ 𝑣 u , 𝑣 v ⟩ ∶ 𝜆 x ． 𝜆 y ． 𝗽⟨ 𝑣 x , 𝑣 y ⟩ ∶ (A ⊃ B ⊃ A ∧ B)
e1₃ = R𝜆² (R𝜆² (R𝗽² (R𝑣² (S Z))
                    (R𝑣² Z)))

e1₄ : {u x v y : Var} {A B : Ty}
    → ⊩ 𝜆 u ． 𝜆 v ． ⇑ 𝗽²⟨ 𝑣 u , 𝑣 v ⟩ ∶ (𝑣 x ∶ A ⊃ 𝑣 y ∶ B ⊃ ! 𝗽⟨ 𝑣 x , 𝑣 y ⟩ ∶ 𝗽⟨ 𝑣 x , 𝑣 y ⟩ ∶ (A ∧ B))
e1₄ = R𝜆 (R𝜆 (R⇑ (R𝗽² (R𝑣 (S Z))
                      (R𝑣 Z))))


-- Example 2 (pp. 31–32[1])

e2  : {x₃ x₂ x₁ : Var} {A : Ty}
    → ⊩ 𝜆² x₃ ． ⇓² ⇑² 𝑣 x₃ ∶ 𝜆 x₂ ． ⇓ ⇑ 𝑣 x₂ ∶ (𝑣 x₁ ∶ A ⊃ 𝑣 x₁ ∶ A)
e2  = R𝜆² (R⇓² (R⇑² (R𝑣² Z)))

e2' : {x₃ x₂ x₁ : Var} {A : Ty}
    → ⊩ 𝜆² x₃ ． 𝑣 x₃ ∶ 𝜆 x₂ ． 𝑣 x₂ ∶ (𝑣 x₁ ∶ A ⊃ 𝑣 x₁ ∶ A)
e2' = R𝜆² (R𝑣² Z)
